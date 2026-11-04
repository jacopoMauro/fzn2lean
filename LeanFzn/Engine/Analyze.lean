/-
File: LeanFzn/Engine/Analyze.lean

N8: first-UIP conflict analysis over the array trail, with proof-carrying
learned clauses.

Every learned clause is an `EClause` built through `EClause.ofLiterals`
from a genuine entailment proof.  A failed analysis has no clause to
return: `Analysis.learned` is an `Option`, and `ok = true` holds exactly
when a clause is present.

Soundness is intrinsic: the analysis definition only takes resolution
steps whose certificates it can check at runtime (`initSlotOKB`,
`domFalseB`, `itemCheckB`, `slotKindOKB`, `sortedB`, `slotObsB`).  Any
doubt returns `ok = false` with `learned = none`.  The main proof
obligations are exported as theorems too: `explainLit_spec`,
`chainReasonLits_entailed`, `resolveWith_entailed`,
`entailed_of_entailed_cons_initial`, `initialDomain_neg_entailed`,
`analyze_sound`, `analyze_ok_learned`, `analyze_empty_unsat`,
`analyze_asserting_mem`, and the operational facts in §C.
-/
import LeanFzn.Engine.Lit
import LeanFzn.Engine.Trail
import LeanFzn.Engine.Queue

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Conflict items -/

/-- A conflict-clause literal together with the earliest trail position
that explains why it is false.  `pos = st.trail.size` is the sentinel for
"false in the initial domain" (a level-0 fact with no trail entry).
`cidx` is the position of `pos` in the slot's change list (irrelevant for
the sentinel). -/
structure CItem where
  lit : Literal
  pos : Nat
  level : Nat
  cidx : Nat
  deriving Repr, DecidableEq

instance : Inhabited CItem :=
  ⟨{ lit := posLe 0 0, pos := 0, level := 0, cidx := 0 }⟩

/-- The current live domains falsify the item's literal. -/
def ItemFalse (st : EngineState p T) (it : CItem) : Prop :=
  (st.doms.getD (atomSlot it.lit.atom) DomC.empty).evalLit it.lit = some false

/-- Everything a conflict item must certify: its slot is in range and
converts, and it has a genuine explanation (initial-domain falsity or a
trail entry whose post-domain falsifies it).  The entry branch also records
the change-list index and the exact undo image, so a chain reason needs no
global `SlotHistory` hypothesis at the analysis site. -/
structure ItemExplained (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (it : CItem) : Prop where
  slot_lt : atomSlot it.lit.atom < p.domains.length
  conv : DomC.ofDom? (p.domains.getD (atomSlot it.lit.atom) Dom.empty) =
    some (init.getD (atomSlot it.lit.atom) DomC.empty)
  expl : (it.pos = st.trail.size ∧ it.level = 0 ∧
      (init.getD (atomSlot it.lit.atom) DomC.empty).evalLit it.lit = some false) ∨
    (∃ e, st.trail[it.pos]? = some e ∧ e.level = it.level ∧
      e.slot = atomSlot it.lit.atom ∧
      (st.changeList (atomSlot it.lit.atom))[it.cidx]? = some it.pos ∧
      e.prev = domAfter init st (atomSlot it.lit.atom) it.cidx ∧
      (e.prev.applyLit e.lit.lit).evalLit it.lit = some false)

/-- The loop invariant: the items clause is entailed, every item is
explained, and every item is false on the current live domains. -/
structure ItemsInv (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (items : Array CItem) : Prop where
  ent : Entailed p (items.toList.map (fun it => it.lit))
  explained : ∀ it, it ∈ items.toList → ItemExplained p init st it
  isFalse : ∀ it, it ∈ items.toList → ItemFalse st it

/-! ## Explanation search -/

/-- Earliest entry in the change list after which `l` is false.  The
position list is scanned in order; `i` is the current index (stored in the
returned item for the chain certificate). -/
def findExplainList (tr : Array Entry) (l : Literal) : List Nat → Nat → Option CItem
  | [], _ => none
  | pos :: rest, i =>
      match tr[pos]? with
      | some e =>
          if (e.prev.applyLit e.lit.lit).evalLit l == some false then
            some ⟨l, pos, e.level, i⟩
          else findExplainList tr l rest (i + 1)
      | none => findExplainList tr l rest (i + 1)

/-- Earliest explanation of a false literal: the initial domain, or the
first trail entry after which the slot domain falsifies it. -/
def explainLit (init : Array DomC) (st : EngineState p T) (l : Literal) :
    Option CItem :=
  if (init.getD (atomSlot l.atom) DomC.empty).evalLit l == some false then
    some ⟨l, st.trail.size, 0, 0⟩
  else
    findExplainList st.trail l (st.changeList (atomSlot l.atom)).toList 0

/-- Specification of the private finder. -/
theorem findExplainList_spec {tr : Array Entry} {l : Literal} {ls : List Nat} {i : Nat}
    {it : CItem} (h : findExplainList tr l ls i = some it) :
    it.lit = l ∧ ∃ j, j < ls.length ∧ ls[j]? = some it.pos ∧ it.cidx = i + j ∧
      ∃ e, tr[it.pos]? = some e ∧ it.level = e.level ∧
        (e.prev.applyLit e.lit.lit).evalLit l = some false := by
  induction ls generalizing i with
  | nil => simp [findExplainList] at h
  | cons pos rest ih =>
      rw [findExplainList] at h
      split at h
      · rename_i e he
        split at h
        · rename_i hfalse
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨rfl, 0, by simp, by simp, by simp, e, he, rfl, ?_⟩
          simpa using hfalse
        · obtain ⟨hlit, j, hj, hget, hidx, e', he', hlev, hfalse⟩ := ih h
          refine ⟨hlit, j + 1, by simp [hj], by simpa using hget, by omega,
            e', he', hlev, hfalse⟩
      · rename_i he
        obtain ⟨hlit, j, hj, hget, hidx, e', he', hlev, hfalse⟩ := ih h
        refine ⟨hlit, j + 1, by simp [hj], by simpa using hget, by omega,
          e', he', hlev, hfalse⟩

theorem explainLit_lit {init : Array DomC} {st : EngineState p T} {l : Literal}
    {it : CItem} (h : explainLit init st l = some it) : it.lit = l := by
  unfold explainLit at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact (findExplainList_spec h).1

/-- If a listed position carries an entry after which `l` is false, the
finder succeeds. -/
theorem findExplainList_some_of_mem_false {tr : Array Entry} {l : Literal}
    {ls : List Nat} {i : Nat} {pos : Nat} {e : Entry}
    (hmem : pos ∈ ls) (he : tr[pos]? = some e)
    (hfalse : (e.prev.applyLit e.lit.lit).evalLit l = some false) :
    ∃ it, findExplainList tr l ls i = some it := by
  have aux : ∀ (ls : List Nat) (i pos : Nat) (e : Entry), pos ∈ ls →
      tr[pos]? = some e →
      (e.prev.applyLit e.lit.lit).evalLit l = some false →
      ∃ it, findExplainList tr l ls i = some it := by
    intro ls
    induction ls with
    | nil => intro i pos e hmem _ _; simp at hmem
    | cons p rest ih =>
        intro i pos e hmem he hfalse
        rw [findExplainList]
        split
        · rename_i e' he'
          split
          · exact ⟨_, rfl⟩
          · rename_i hnot
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · rw [he] at he'
              have heq : e = e' := Option.some.inj he'
              rw [← heq] at hnot
              exact absurd hfalse (by simpa using hnot)
            · exact ih (i + 1) pos e hmem' he hfalse
        · rename_i he'
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · rw [he] at he'
            simp at he'
          · exact ih (i + 1) pos e hmem' he hfalse
  exact aux ls i pos e hmem he hfalse

/-- `none` exactly when no listed position explains the literal. -/
theorem findExplainList_none_iff {tr : Array Entry} {l : Literal}
    {ls : List Nat} {i : Nat} :
    findExplainList tr l ls i = none ↔
      ∀ pos ∈ ls, ∀ e, tr[pos]? = some e →
        (e.prev.applyLit e.lit.lit).evalLit l ≠ some false := by
  constructor
  · intro h pos hp e he hfalse
    obtain ⟨it, hit⟩ := findExplainList_some_of_mem_false (i := i) hp he hfalse
    rw [h] at hit
    simp at hit
  · intro hall
    cases hfind : findExplainList tr l ls i with
    | none => rfl
    | some it =>
        obtain ⟨_hlit, j, hj, hget, _hidx, e, he, _hlev, hfalse⟩ :=
          findExplainList_spec hfind
        have hposmem : it.pos ∈ ls := List.mem_iff_getElem?.mpr ⟨j, hget⟩
        exact absurd hfalse (hall it.pos hposmem e he)

/-- **B1.**  If `explainLit` returns an item, it is either the initial
domain (sentinel position, level zero) or a trail entry whose
post-domain falsifies the literal.  The entry branch also records the
change-list index and the membership of the position in the change list. -/
theorem explainLit_spec (hTI : TrailInv st)
    {init : Array DomC} {l : Literal} {it : CItem}
    (h : explainLit init st l = some it) :
    it.lit = l ∧
    ((it.pos = st.trail.size ∧ it.level = 0 ∧
        (init.getD (atomSlot l.atom) DomC.empty).evalLit l = some false ∧
        it.cidx = 0) ∨
      (∃ e, st.trail[it.pos]? = some e ∧ e.level = it.level ∧
        e.slot = atomSlot l.atom ∧ it.pos ∈ st.changeList (atomSlot l.atom) ∧
        (st.changeList (atomSlot l.atom))[it.cidx]? = some it.pos ∧
        (e.prev.applyLit e.lit.lit).evalLit l = some false)) := by
  unfold explainLit at h
  split at h
  · rename_i hfalse
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, Or.inl ⟨rfl, rfl, ?_, rfl⟩⟩
    simpa using hfalse
  · rename_i hnot
    obtain ⟨hlit, j, hj, hget, hidx, e, he, hlev, hfalse⟩ := findExplainList_spec h
    have hmemList : it.pos ∈ (st.changeList (atomSlot l.atom)).toList :=
      List.mem_iff_getElem?.mpr ⟨j, hget⟩
    have hmem : it.pos ∈ st.changeList (atomSlot l.atom) := Array.mem_toList_iff.mp hmemList
    obtain ⟨_, e', he', hslot⟩ :=
      (hTI.changeIndex_mem (atomSlot l.atom) it.pos).1 hmem
    have heq : e' = e := by
      rw [he'] at he
      exact Option.some.inj he
    have hslot' : e.slot = atomSlot l.atom := by
      rw [← heq]
      exact hslot
    have hcidx : it.cidx = j := by omega
    refine ⟨hlit, Or.inr ⟨e, he, hlev.symm, hslot', hmem, ?_, hfalse⟩⟩
    rw [hcidx]
    simpa using hget

/-- `none` exactly when neither explanation branch applies. -/
theorem explainLit_none_iff {init : Array DomC} {st : EngineState p T} {l : Literal} :
    explainLit init st l = none ↔
      (init.getD (atomSlot l.atom) DomC.empty).evalLit l ≠ some false ∧
      ∀ pos ∈ st.changeList (atomSlot l.atom), ∀ e, st.trail[pos]? = some e →
        (e.prev.applyLit e.lit.lit).evalLit l ≠ some false := by
  unfold explainLit
  split
  · rename_i hd
    constructor
    · intro h; simp at h
    · intro ⟨hne, _⟩
      exact absurd (by simpa using hd) hne
  · rename_i hd
    have hnot : (init.getD (atomSlot l.atom) DomC.empty).evalLit l ≠ some false := by
      intro heq
      exact hd (by simpa [Array.getD_eq_getElem?_getD] using heq)
    constructor
    · intro h
      refine ⟨hnot, ?_⟩
      intro pos hmem e he
      exact (findExplainList_none_iff (tr := st.trail) (l := l)
        (ls := (st.changeList (atomSlot l.atom)).toList) (i := 0)).1 h
        pos (Array.mem_toList_iff.mpr hmem) e he
    · intro ⟨_, hall⟩
      exact (findExplainList_none_iff (tr := st.trail) (l := l)
        (ls := (st.changeList (atomSlot l.atom)).toList) (i := 0)).2
        (fun pos hp e he => hall pos (Array.mem_toList_iff.mp hp) e he)

/-- A non-Boolean compact domain has no Boolean fixed value. -/
theorem DomC.fixedValue_bool_eq_none_of_ne_bool {d : DomC} (h : ∀ b, d ≠ .bool b) :
    d.fixedValue = none ∨ ∃ i, d.fixedValue = some (.int i) := by
  cases d with
  | bool bits => exact absurd rfl (h bits)
  | bounds lo hi =>
      by_cases hh : lo == hi
      · exact Or.inr ⟨lo, by simp [DomC.fixedValue, hh]⟩
      · exact Or.inl (by simp [DomC.fixedValue, hh])
  | bitset lo words =>
      cases hlo : (DomC.bitset lo words).lo? <;> cases hhi : (DomC.bitset lo words).hi?
      all_goals simp only [DomC.fixedValue, hlo, hhi]
      all_goals first
        | exact Or.inl trivial
        | (split
           · exact Or.inr ⟨_, rfl⟩
           · exact Or.inl rfl)
  | boundsHoles lo hi holes =>
      cases hlo : (DomC.boundsHoles lo hi holes).lo? <;>
        cases hhi : (DomC.boundsHoles lo hi holes).hi?
      all_goals simp only [DomC.fixedValue, hlo, hhi]
      all_goals first
        | exact Or.inl trivial
        | (split
           · exact Or.inr ⟨_, rfl⟩
           · exact Or.inl rfl)

/-- A Boolean-equality literal is undefined on a non-Boolean domain. -/
theorem DomC.evalLit_boolEq_eq_none_of_nonbool {d : DomC} {s : Slot} {b : Bool}
    {pos : Bool} (h : ∀ bb, d ≠ .bool bb) :
    d.evalLit (⟨.boolEq s b, pos⟩ : Literal) = none := by
  rcases d.fixedValue_bool_eq_none_of_ne_bool h with h0 | ⟨i, hi⟩
  · simp [DomC.evalLit, h0]
  · simp [DomC.evalLit, hi]

/-- A definite false evaluation of a literal on a domain containing `v`
makes the atom defined at `v`. -/
theorem Atom.evalAtValue_ne_none_of_mem_evalLit_false {d : DomC} {l : Literal}
    {v : Value} (hm : d.mem v = true) (hf : d.evalLit l = some false) :
    l.atom.evalAtValue v ≠ none := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b =>
      cases v with
      | bool x => simp [Atom.evalAtValue]
      | int x =>
          exfalso
          have hnb : ∀ bb, d ≠ .bool bb := by
            intro bb hd
            subst hd
            simp [DomC.mem] at hm
          rw [DomC.evalLit_boolEq_eq_none_of_nonbool (b := b) hnb] at hf
          simp at hf
      | setOfInt x => simp [DomC.mem] at hm
      | array x => simp [DomC.mem] at hm
  | intLe s k =>
      cases v with
      | bool x => simp [Atom.evalAtValue, Value.intView]
      | int x => simp [Atom.evalAtValue, Value.intView]
      | setOfInt x => simp [DomC.mem] at hm
      | array x => simp [DomC.mem] at hm
  | intNe s k =>
      cases v with
      | bool x => simp [Atom.evalAtValue, Value.intView]
      | int x => simp [Atom.evalAtValue, Value.intView]
      | setOfInt x => simp [DomC.mem] at hm
      | array x => simp [DomC.mem] at hm

/-- Under definedness, negating a literal flips its value. -/
theorem Literal.valueHolds_negate_of_ne_none (l : Literal) (v : Value)
    (h : l.atom.evalAtValue v ≠ none) :
    l.negate.valueHolds v = !(l.valueHolds v) := by
  cases l with
  | mk atom pos =>
    rw [valueHolds_eq_map_beq, valueHolds_eq_map_beq]
    cases hdef : Atom.evalAtValue atom v with
    | none => exact absurd hdef h
    | some x =>
        cases pos <;> cases x <;> simp [Literal.negate, hdef]

/-- Under definedness, a negated literal is true exactly when the original
is false. -/
theorem Literal.valueHolds_negate_eq_true_iff (l : Literal) (v : Value)
    (h : l.atom.evalAtValue v ≠ none) :
    l.negate.valueHolds v = true ↔ l.valueHolds v = false := by
  rw [Literal.valueHolds_negate_of_ne_none l v h]
  cases l.valueHolds v <;> simp

/-! ## Item insertion -/

/-- Insert an item by appending it.

The earlier N1 spike replaced an existing occurrence with an earlier
explanation.  For soundness duplicates are harmless (clause semantics is
set-like), and appending makes membership and entailment immediate; the
analysis removes all copies of a resolved literal explicitly. -/
def addCItem (items : Array CItem) (it : CItem) : Array CItem :=
  items.push it

/-- Literal membership through `addCItem`. -/
theorem addCItem_mem_lit_iff {items : Array CItem} {it : CItem} {l : Literal} :
    l ∈ (addCItem items it).toList.map (fun x => x.lit) ↔
      l ∈ items.toList.map (fun x => x.lit) ∨ l = it.lit := by
  simp [addCItem, Array.toList_push, List.mem_map]

/-- Literal membership is monotone under `addCItem`. -/
theorem addCItem_mem_lit {items : Array CItem} {it : CItem} {l : Literal}
    (h : l ∈ items.toList.map (fun x => x.lit)) :
    l ∈ (addCItem items it).toList.map (fun x => x.lit) :=
  addCItem_mem_lit_iff.mpr (Or.inl h)

/-- Item membership through `addCItem`: every output item is old or the new
item. -/
theorem addCItem_mem {items : Array CItem} {it x : CItem}
    (h : x ∈ addCItem items it) : x ∈ items ∨ x = it := by
  unfold addCItem at h
  exact Array.mem_push.mp h

/-- `addCItem` preserves an explanation invariant. -/
theorem addCItem_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {it : CItem}
    (h : ∀ x, x ∈ items.toList → ItemExplained p init st x)
    (hit : ItemExplained p init st it) :
    ∀ x, x ∈ (addCItem items it).toList → ItemExplained p init st x := by
  intro x hx
  have hx' : x ∈ addCItem items it := Array.mem_toList_iff.mp hx
  rcases addCItem_mem hx' with hxold | rfl
  · exact h x (Array.mem_toList_iff.mpr hxold)
  · exact hit

/-- `addCItem` preserves the current-falsity invariant. -/
theorem addCItem_false {st : EngineState p T} {items : Array CItem} {it : CItem}
    (h : ∀ x, x ∈ items.toList → ItemFalse st x)
    (hit : ItemFalse st it) :
    ∀ x, x ∈ (addCItem items it).toList → ItemFalse st x := by
  intro x hx
  have hx' : x ∈ addCItem items it := Array.mem_toList_iff.mp hx
  rcases addCItem_mem hx' with hxold | rfl
  · exact h x (Array.mem_toList_iff.mpr hxold)
  · exact hit

/-! ## Runtime certificates -/

/-- The slot is in range and its compiled domain converts to `init[s]`. -/
def initSlotOKB (p : CompiledProblem DomConstraint) (init : Array DomC) (s : Nat) : Bool :=
  (s < p.domains.length) &&
    decide (DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))

theorem initSlotOKB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {s : Nat} (h : initSlotOKB p init s = true) :
    s < p.domains.length ∧
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) := by
  unfold initSlotOKB at h
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- The literal is false on the current live domains. -/
def domFalseB (st : EngineState p T) (l : Literal) : Bool :=
  (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l == some false

theorem domFalseB_spec {st : EngineState p T} {l : Literal} (h : domFalseB st l = true) :
    (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false :=
  beq_iff_eq.mp h

/-- Decidable version of `ItemExplained`. -/
def itemCheckB (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (it : CItem) : Bool :=
  let s := atomSlot it.lit.atom
  initSlotOKB p init s &&
  ((it.pos == st.trail.size && it.level == 0 &&
      ((init.getD s DomC.empty).evalLit it.lit == some false)) ||
   match st.trail[it.pos]? with
   | some e =>
       (e.level == it.level) && (e.slot == s) &&
       ((st.changeList s)[it.cidx]? == some it.pos) &&
       decide (e.prev = domAfter init st s it.cidx) &&
       ((e.prev.applyLit e.lit.lit).evalLit it.lit == some false)
   | none => false)

theorem itemCheckB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (h : itemCheckB p init st it = true) :
    ItemExplained p init st it := by
  unfold itemCheckB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hinit, hbody⟩ := h
  obtain ⟨hslot, hconv⟩ := initSlotOKB_spec hinit
  refine ⟨hslot, hconv, ?_⟩
  by_cases hpos : it.pos = st.trail.size
  · left
    have htr : st.trail[st.trail.size]? = none := Array.getElem?_eq_none (Nat.le_refl _)
    rw [hpos, htr] at hbody
    simp only [beq_self_eq_true, Bool.true_and, Bool.or_false, Bool.and_eq_true] at hbody
    exact ⟨hpos, by simpa [beq_iff_eq] using hbody.1,
      by simpa [beq_iff_eq] using hbody.2⟩
  · right
    have hne : (it.pos == st.trail.size) = false := by
      simpa [beq_iff_eq] using hpos
    rw [hne] at hbody
    simp only [Bool.false_and, Bool.false_or] at hbody
    cases htr : st.trail[it.pos]? with
    | none => rw [htr] at hbody; simp at hbody
    | some e =>
        rw [htr] at hbody
        have hbody' : e.level = it.level ∧ e.slot = atomSlot it.lit.atom ∧
            (st.changeList (atomSlot it.lit.atom))[it.cidx]? = some it.pos ∧
            e.prev = domAfter init st (atomSlot it.lit.atom) it.cidx ∧
            (e.prev.applyLit e.lit.lit).evalLit it.lit = some false := by
          simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using hbody
        exact ⟨e, rfl, hbody'.1, hbody'.2.1, hbody'.2.2.1, hbody'.2.2.2.1,
          hbody'.2.2.2.2⟩

/-- A structural kind test for trail atoms on a slot: on a Boolean initial
domain every literal is meaningful (Booleans have an integer view); on an
integer initial domain a Boolean pin has no meaning. -/
def atomKindOKB (d : DomC) (atom : Atom) : Bool :=
  match d with
  | .bool _ => true
  | _ => match atom with
    | .boolEq _ _ => false
    | _ => true

theorem atomKindOKB_spec {d : DomC} {atom : Atom} (h : atomKindOKB d atom = true)
    {v : Value} (hm : d.mem v = true) : atom.evalAtValue v ≠ none := by
  cases d <;> cases atom <;> cases v <;>
    simp [atomKindOKB, DomC.mem, Atom.evalAtValue, Value.intView] at h hm ⊢

/-- Every entry on the slot's change list is meaningful at every member of
the initial domain. -/
def slotKindOKB (init : Array DomC) (st : EngineState p T) (s : Nat) : Bool :=
  (st.changeList s).all fun p =>
    match st.trail[p]? with
    | some e => atomKindOKB (init.getD s DomC.empty) e.lit.lit.atom
    | none => true

theorem slotKindOKB_spec {init : Array DomC} {st : EngineState p T} {s : Nat}
    (h : slotKindOKB init st s = true) :
    ∀ p ∈ st.changeList s, ∀ e, st.trail[p]? = some e → ∀ v,
      (init.getD s DomC.empty).mem v = true → e.lit.lit.atom.evalAtValue v ≠ none := by
  intro p hp e he v hv
  have hp' : p ∈ (st.changeList s).toList := Array.mem_toList_iff.mpr hp
  have hall := (Array.all_eq_true'.mp h) p (by simpa using hp')
  simp only [he] at hall
  exact atomKindOKB_spec hall hv

/-- Every entry on the slot's change list exists and really belongs to that
slot.  The `none` case is a failure: a dangling position cannot be replayed,
so the chain certificate is refused. -/
def slotObsB (st : EngineState p T) (s : Nat) : Bool :=
  (st.changeList s).all fun p =>
    match st.trail[p]? with
    | some e => e.slot == s
    | none => false

theorem slotObsB_spec {st : EngineState p T} {s : Nat} (h : slotObsB st s = true) :
    ∀ p ∈ st.changeList s, ∃ e, st.trail[p]? = some e ∧ e.slot = s := by
  intro p hp
  have hp' : p ∈ (st.changeList s).toList := Array.mem_toList_iff.mpr hp
  have hall := (Array.all_eq_true'.mp h) p (by simpa using hp')
  cases he : st.trail[p]? with
  | none => simp [he] at hall
  | some e => exact ⟨e, rfl, beq_iff_eq.mp (by simpa [he] using hall)⟩

/-- Decidable sortedness of a change list. -/
def sortedB (a : Array Nat) : Bool := decide (a.toList.Pairwise (· < ·))

theorem sortedB_spec {a : Array Nat} (h : sortedB a = true) : SortedList a := by
  unfold sortedB at h
  exact of_decide_eq_true (p := a.toList.Pairwise (· < ·)) h

/-! ## Subsumption -/

/-- Subsumption fallback: the identity map.

A syntactic `litImpliesNot` filter would drop literals implied by
another clause literal.  Proving the filter step sound needs the reverse
direction of `litImpliesNot` (`b` true implies `a` false, true in every
accepted case but requiring a second copy of its long case analysis).  The
identity keeps every learned clause entailed; it only forgoes assertingness
gains on same-slot bound conflicts.  This is the documented fallback allowed
by N8 §B3. -/
def subsumeItems (items : Array CItem) : Array CItem := items

theorem subsumeItems_subset {items : Array CItem} {x : CItem}
    (h : x ∈ subsumeItems items) : x ∈ items := h

theorem subsumeStep_entailed {p : CompiledProblem DomConstraint} {items : Array CItem}
    {it : CItem}
    (h : Entailed p (items.toList.map (fun x => x.lit))) :
    Entailed p ((subsumeItems (items.push it)).toList.map (fun x => x.lit)) := by
  simpa [subsumeItems] using
    (show Entailed p (((items.push it).toList).map (fun x => x.lit)) from by
      intro b hb hacc
      obtain ⟨r, hr, hrt⟩ := h b hb hacc
      refine ⟨r, ?_, hrt⟩
      rw [Array.toList_push, List.map_append]
      exact List.mem_append_left _ hr)

theorem subsumeItems_entailed {p : CompiledProblem DomConstraint} {items : Array CItem}
    (h : Entailed p (items.toList.map (fun x => x.lit))) :
    Entailed p ((subsumeItems items).toList.map (fun x => x.lit)) := h

/-! ## Chain clauses -/

/-- The falsified literals of the slot's trail prefix up to `pos`, plus the
negation of the resolved conflict literal. -/
def chainReasonLits (st : EngineState p T) (slot : Nat) (pos : Nat)
    (b : Literal) : Array Literal :=
  let ls := (st.changeIndex.getD slot #[]).filterMap fun p =>
    if p ≤ pos then
      match st.trail[p]? with
      | some e => some e.lit.lit.negate
      | none => none
    else none
  #[b.negate] ++ ls

theorem mem_chainReasonLits {st : EngineState p T} {slot pos : Nat} {b q : Literal} :
    q ∈ (chainReasonLits st slot pos b).toList ↔
      q = b.negate ∨ ∃ p ∈ st.changeList slot, p ≤ pos ∧
        ∃ e, st.trail[p]? = some e ∧ q = e.lit.lit.negate := by
  unfold chainReasonLits
  rw [Array.mem_toList_iff, Array.mem_append, Array.mem_filterMap]
  have hsing : q ∈ #[b.negate] ↔ q = b.negate := by simp
  rw [hsing]
  constructor
  · rintro (rfl | ⟨p, hp, hf⟩)
    · exact Or.inl rfl
    · right
      refine ⟨p, hp, ?_, ?_⟩
      · by_cases hle : p ≤ pos
        · exact hle
        · simp [hle] at hf
      · by_cases hle : p ≤ pos
        · cases htr : st.trail[p]? with
          | none => simp [hle, htr] at hf
          | some e =>
              simp [hle, htr] at hf
              exact ⟨e, rfl, hf.symm⟩
        · simp [hle] at hf
  · intro h
    rcases h with rfl | ⟨p, hp, hle, e, he, rfl⟩
    · exact Or.inl (by simp)
    · right
      refine ⟨p, hp, ?_⟩
      simp [hle, he]

/-- The local chain certificate: sorted change list, every listed entry
belongs to the slot and is kind-compatible, and the resolved entry's undo
image is the replay of its prefix.  This is exactly what the analysis
runtime checks before taking the chain step. -/
structure ChainCert (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (slot : Nat) : Prop where
  slot_lt : slot < p.domains.length
  conv : DomC.ofDom? (p.domains.getD slot Dom.empty) = some (init.getD slot DomC.empty)
  sorted : SortedList (st.changeList slot)
  entries : ∀ q ∈ st.changeList slot,
    ∃ e, st.trail[q]? = some e ∧ e.slot = slot
  lit_slot : ∀ q ∈ st.changeList slot, ∀ e, st.trail[q]? = some e →
    atomSlot e.lit.lit.atom = slot
  kind : ∀ q ∈ st.changeList slot, ∀ e, st.trail[q]? = some e → ∀ v,
    (init.getD slot DomC.empty).mem v = true → e.lit.lit.atom.evalAtValue v ≠ none

/-- `atomSlot` is the `slot` field of an atom. -/
theorem atomSlot_eq_slot (a : Atom) : atomSlot a = a.slot := by
  cases a <;> rfl

/-- Extract the value at a slot from an assignment enumerated by a list of
domains. -/
theorem mem_allAssigns_getElem_mem {ds : List Domain} {a : Assignment} {k : Nat}
    (ha : a ∈ allAssigns ds) (hk : k < ds.length) :
    ∃ v, a[k]? = some v ∧ v ∈ ds.getD k DomainLike.empty := by
  induction ds generalizing a k with
  | nil => simp at hk
  | cons d rest ih =>
      obtain ⟨v, hv, a', ha', rfl⟩ :=
        LeanFzn.Solver.Propagation.mem_allAssigns_cons_iff.mp ha
      cases k with
      | zero => exact ⟨v, rfl, by simpa using hv⟩
      | succ k =>
          obtain ⟨w, hw, hmem⟩ := ih ha' (k := k) (by simpa using hk)
          exact ⟨w, by simpa using hw, by simpa using hmem⟩

/-- **B2, local form.**  The chain clause is entailed from the runtime
chain certificate plus the resolved entry's replay index.  This is the form
used by the analysis loop: the item carries the entry, its index in the
slot's change list, and `prev = domAfter ...`; the certificate carries the
initial-domain conversion, sortedness, entry existence, slot ownership and
kind discipline. -/
theorem chainReasonLits_entailed_of_cert {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {slot pos j : Nat} {b : Literal}
    {e : Entry} (hcert : ChainCert p init st slot)
    (hjget : (st.changeList slot)[j]? = some pos)
    (he : st.trail[pos]? = some e)
    (hprev : e.prev = domAfter init st slot j)
    (hbslot : atomSlot b.atom = slot)
    (hfalse : (e.prev.applyLit e.lit.lit).evalLit b = some false) :
    Entailed p (chainReasonLits st slot pos b).toList := by
  intro a ha hacc
  have hjlt : j < (st.changeList slot).size :=
    (Array.getElem?_eq_some_iff.mp hjget).1
  have hclk : (st.changeList slot).getD j 0 = pos := by
    rw [Array.getD_eq_getElem?_getD, hjget]
    rfl
  -- After the entry's literal, `b` is false.
  have hfalseD : (domAfter init st slot (j + 1)).evalLit b = some false := by
    rw [domAfter_succ init st slot j hjlt, hclk]
    unfold domStep
    rw [he, ← hprev]
    exact hfalse
  -- The accepted assignment's value on the slot.
  obtain ⟨v, hav, hvmem⟩ := mem_allAssigns_getElem_mem (ds := p.domains) ha hcert.slot_lt
  have hinitmem : (init.getD slot DomC.empty).mem v = true := by
    rw [DomC.mem_iff (p.domains.getD slot Dom.empty) (init.getD slot DomC.empty)
      hcert.conv v]
    exact hvmem
  have hinitWF : (init.getD slot DomC.empty).WF :=
    DomC.ofDom?_wf _ _ hcert.conv
  -- Prefix induction: either an earlier entry literal is false at `v`, or
  -- `v` survives the replay up to that point.
  have hinitmem0 : (domAfter init st slot 0).mem v = true := by
    rw [domAfter_zero]
    exact hinitmem
  have hprefix : ∀ j', j' ≤ j + 1 →
      (∃ i, i < j' ∧ ∃ ei, st.trail[(st.changeList slot).getD i 0]? = some ei ∧
        ei.lit.lit.valueHolds v = false) ∨
      (domAfter init st slot j').mem v = true := by
    intro j'
    induction j' with
    | zero => intro _; exact Or.inr hinitmem0
    | succ j' ih =>
        intro hj'
        have hj'le : j' ≤ j := by omega
        have hj'lt : j' < (st.changeList slot).size :=
          Nat.lt_of_le_of_lt hj'le hjlt
        rcases ih (by omega) with ⟨i, hi, ei, hei, hfalsei⟩ | hDjmem
        · exact Or.inl ⟨i, Nat.lt_succ_of_lt hi, ei, hei, hfalsei⟩
        · have hpjmem : (st.changeList slot).getD j' 0 ∈ st.changeList slot := by
            rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hj'lt]
            exact Array.getElem_mem hj'lt
          obtain ⟨ej, hej, _⟩ := hcert.entries ((st.changeList slot).getD j' 0) hpjmem
          cases hv : ej.lit.lit.valueHolds v with
          | true =>
              right
              rw [domAfter_succ init st slot j' hj'lt]
              unfold domStep
              rw [hej]
              rw [DomC.mem_applyLit _ _ (domAfter_WF hinitWF) v]
              exact ⟨hDjmem, hv⟩
          | false =>
              exact Or.inl ⟨j', Nat.lt_succ_self j', ej, hej, hv⟩
  rcases hprefix (j + 1) (Nat.le_refl _) with
    ⟨i, hilt, ei, hei, hfalsei⟩ | hDmem
  · -- An earlier entry literal is false at the value.
    have hile : i ≤ j := Nat.lt_succ_iff.mp hilt
    have hilt' : i < (st.changeList slot).size := Nat.lt_of_le_of_lt hile hjlt
    have hpimem : (st.changeList slot).getD i 0 ∈ st.changeList slot := by
      rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hilt']
      exact Array.getElem_mem hilt'
    have hpile : (st.changeList slot).getD i 0 ≤ pos := by
      rw [← hclk]
      exact SortedList.getD_le hcert.sorted hile hjlt
    have hin : ei.lit.lit.negate ∈ (chainReasonLits st slot pos b).toList := by
      rw [mem_chainReasonLits]
      exact Or.inr ⟨(st.changeList slot).getD i 0, hpimem, hpile, ei, hei, rfl⟩
    refine ⟨ei.lit.lit.negate, hin, ?_⟩
    have hlit_slot : atomSlot ei.lit.lit.atom = slot :=
      hcert.lit_slot _ hpimem ei hei
    have hslot : ei.lit.lit.atom.slot = slot := by
      rw [← atomSlot_eq_slot]
      exact hlit_slot
    have hav' : a[atomSlot ei.lit.lit.negate.atom]? = some v := by
      rw [atomSlot_eq_slot]
      rw [show ei.lit.lit.negate.atom.slot = slot by
        simpa [Literal.negate] using hslot]
      exact hav
    rw [Literal.eval_eq_valueHolds _ a hav']
    exact (Literal.valueHolds_negate_eq_true_iff ei.lit.lit v
      (hcert.kind _ hpimem ei hei v hinitmem)).mpr hfalsei
  · -- The value survives the prefix, where `b` is false.
    have heval := DomC.evalLit_false_sound (domAfter init st slot (j + 1)) b
      (domAfter_WF hinitWF) hfalseD v hDmem
    have hdef := Atom.evalAtValue_ne_none_of_mem_evalLit_false hDmem hfalseD
    have hneg : b.negate.valueHolds v = true :=
      (Literal.valueHolds_negate_eq_true_iff b v hdef).mpr heval
    refine ⟨b.negate, ?_, ?_⟩
    · rw [mem_chainReasonLits]
      exact Or.inl rfl
    · have hslot : b.atom.slot = slot := by
        rw [← atomSlot_eq_slot]
        exact hbslot
      have hav' : a[atomSlot b.negate.atom]? = some v := by
        rw [atomSlot_eq_slot]
        rw [show b.negate.atom.slot = slot by
          simpa [Literal.negate] using hslot]
        exact hav
      rw [Literal.eval_eq_valueHolds _ a hav']
      exact hneg

/-- **B2.**  The chain clause is entailed.  The hypotheses are the local
`ChainCert` (conversion of the slot's initial domain, sorted change list,
entry existence and slot ownership, and kind-compatibility of every listed
atom on the initial domain) together with the history fact that the
resolving entry's `prev` is the replay of the change-list prefix.  The
statement in N8 §B2 is missing `conv` and `kind`; without them the clause
is false: on an integer initial domain an entry literal `boolEq s false`
evaluates `none` on every value, so neither the literal nor its negation can
satisfy the clause.  `ChainCert` is the smallest practical correction and
is exactly what `analyze` checks at runtime. -/
theorem chainReasonLits_entailed
    (_hInit : InitInv p init) (hSH : SlotHistory init st) (_hTI : TrailInv st)
    (hcert : ChainCert p init st slot)
    (hpos : pos ∈ st.changeList slot) (e : Entry) (he : st.trail[pos]? = some e)
    (hbslot : atomSlot b.atom = slot)
    (hfalse : (e.prev.applyLit e.lit.lit).evalLit b = some false) :
    Entailed p (chainReasonLits st slot pos b).toList := by
  obtain ⟨j, hjget⟩ := Array.mem_iff_getElem?.mp hpos
  have hjlt : j < (st.changeList slot).size :=
    (Array.getElem?_eq_some_iff.mp hjget).1
  have hclk : (st.changeList slot).getD j 0 = pos := by
    rw [Array.getD_eq_getElem?_getD, hjget]
    rfl
  have hprev0 := hSH.prev_eq slot j hjlt
  dsimp only at hprev0
  have hprev : e.prev = domAfter init st slot j := by
    rw [hclk] at hprev0
    rw [Array.getD_eq_getElem?_getD, he] at hprev0
    simpa using hprev0
  exact chainReasonLits_entailed_of_cert hcert hjget he hprev hbslot hfalse


/-! ## Entailment under list inclusion -/

/-- A clause entailed by `p` remains entailed when literals are added. -/
theorem Entailed_of_mem_subset {p : CompiledProblem DomConstraint} {c c' : Clause}
    (h : Entailed p c) (hsub : ∀ l ∈ c, l ∈ c') : Entailed p c' := by
  intro b hb hacc
  obtain ⟨l, hl, hev⟩ := h b hb hacc
  exact ⟨l, hsub l hl, hev⟩

/-- Entailment is invariant under permutation of the clause literals. -/
theorem Entailed_of_perm {p : CompiledProblem DomConstraint} {c c' : Clause}
    (h : Entailed p c) (hp : c.Perm c') : Entailed p c' :=
  Entailed_of_mem_subset h (fun _l hl => (List.Perm.mem_iff hp).mp hl)

/-! ## Item removal -/

/-- Remove every item whose literal is `l`. -/
def removeLitItems (items : Array CItem) (l : Literal) : Array CItem :=
  items.filter (fun it => !litEqB it.lit l)

theorem removeLitItems_mem {items : Array CItem} {l : Literal} {x : CItem} :
    x ∈ removeLitItems items l ↔ x ∈ items ∧ x.lit ≠ l := by
  rw [removeLitItems, Array.mem_filter]
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨hx, ?_⟩
    intro hxl
    subst hxl
    simp [litEqB] at hp
  · rintro ⟨hx, hne⟩
    refine ⟨hx, ?_⟩
    simp [litEqB, hne]

theorem removeLitItems_lits (items : Array CItem) (l : Literal) :
    (removeLitItems items l).toList.map (fun it => it.lit) =
      (items.toList.map (fun it => it.lit)).filter (fun q => !litEqB q l) := by
  rw [removeLitItems, Array.toList_filter, List.filter_map]
  rfl

/-! ## Initial conflict items -/

/-- Both the explanation certificate and current falsity of an item. -/
def itemOKB (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (it : CItem) : Bool :=
  itemCheckB p init st it && domFalseB st it.lit

theorem itemOKB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (h : itemOKB p init st it = true) :
    ItemExplained p init st it ∧ ItemFalse st it := by
  unfold itemOKB at h
  rw [Bool.and_eq_true] at h
  exact ⟨itemCheckB_spec h.1, domFalseB_spec h.2⟩

/-- Explain every literal of the initial conflict clause.  Any missing or
unchecked explanation aborts the analysis (`none`). -/
def initialItems (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) : List Literal → Option (Array CItem)
  | [] => some #[]
  | l :: ls =>
      match explainLit init st l with
      | none => none
      | some it =>
          if itemOKB p init st it then
            match initialItems p init st ls with
            | none => none
            | some items => some (addCItem items it)
          else none

theorem initialItems_lit_mem {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List Literal} {items : Array CItem}
    (h : initialItems p init st ls = some items) :
    ∀ l ∈ ls, l ∈ items.toList.map (fun it => it.lit) := by
  induction ls generalizing items with
  | nil => intro l hl; simp at hl
  | cons a rest ih =>
      unfold initialItems at h
      split at h
      · simp at h
      · rename_i it hit
        by_cases hcheck : itemOKB p init st it = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              intro l hl
              rcases List.mem_cons.mp hl with rfl | hl
              · exact addCItem_mem_lit_iff.mpr (Or.inr (explainLit_lit hit).symm)
              · exact addCItem_mem_lit_iff.mpr (Or.inl (ih hrec l hl))
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List Literal} {items : Array CItem}
    (h : initialItems p init st ls = some items) :
    ∀ it, it ∈ items.toList → ItemExplained p init st it := by
  induction ls generalizing items with
  | nil =>
      intro it hit
      simp [initialItems] at h
      subst h
      simp at hit
  | cons a rest ih =>
      unfold initialItems at h
      split at h
      · simp at h
      · rename_i it hit
        by_cases hcheck : itemOKB p init st it = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              exact addCItem_explained (ih hrec) (itemOKB_spec hcheck).1
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List Literal} {items : Array CItem}
    (h : initialItems p init st ls = some items) :
    ∀ it, it ∈ items.toList → ItemFalse st it := by
  induction ls generalizing items with
  | nil =>
      intro it hit
      simp [initialItems] at h
      subst h
      simp at hit
  | cons a rest ih =>
      unfold initialItems at h
      split at h
      · simp at h
      · rename_i it hit
        by_cases hcheck : itemOKB p init st it = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              exact addCItem_false (ih hrec) (itemOKB_spec hcheck).2
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_entailed {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List Literal} {items : Array CItem}
    (hconf : Entailed p ls) (h : initialItems p init st ls = some items) :
    Entailed p (items.toList.map (fun it => it.lit)) :=
  Entailed_of_mem_subset hconf (fun l hl => initialItems_lit_mem h l hl)

theorem initialItems_inv {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List Literal} {items : Array CItem}
    (hconf : Entailed p ls) (h : initialItems p init st ls = some items) :
    ItemsInv p init st items where
  ent := initialItems_entailed hconf h
  explained := initialItems_explained h
  isFalse := initialItems_false h

/-! ## Chain certificate checks -/

/-- Every listed entry's literal reads the slot it is indexed under. -/
def litSlotOKB (st : EngineState p T) (s : Nat) : Bool :=
  (st.changeList s).all fun p =>
    match st.trail[p]? with
    | some e => atomSlot e.lit.lit.atom == s
    | none => true

theorem litSlotOKB_spec {st : EngineState p T} {s : Nat}
    (h : litSlotOKB st s = true) :
    ∀ p ∈ st.changeList s, ∀ e, st.trail[p]? = some e →
      atomSlot e.lit.lit.atom = s := by
  intro p hp e he
  have hp' : p ∈ (st.changeList s).toList := Array.mem_toList_iff.mpr hp
  have hall := (Array.all_eq_true'.mp h) p (by simpa using hp')
  simp only [he] at hall
  exact beq_iff_eq.mp hall

/-- All runtime facts needed by `chainReasonLits_entailed`. -/
def chainCertCheckB (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (s : Nat) : Bool :=
  initSlotOKB p init s && sortedB (st.changeList s) && slotObsB st s &&
    litSlotOKB st s && slotKindOKB init st s

theorem chainCertCheckB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {s : Nat} (h : chainCertCheckB p init st s = true) :
    ChainCert p init st s := by
  unfold chainCertCheckB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h4, hkind⟩ := h
  rw [Bool.and_eq_true] at h4
  obtain ⟨h3, hlit⟩ := h4
  rw [Bool.and_eq_true] at h3
  obtain ⟨h2, hobs⟩ := h3
  rw [Bool.and_eq_true] at h2
  obtain ⟨h1, hsorted⟩ := h2
  obtain ⟨hslot, hconv⟩ := initSlotOKB_spec h1
  exact
    { slot_lt := hslot
      conv := hconv
      sorted := sortedB_spec hsorted
      entries := slotObsB_spec hobs
      lit_slot := litSlotOKB_spec hlit
      kind := slotKindOKB_spec hkind }

/-! ## One resolution step -/

/-- The reason clause used by `resolveWith`: a stored/transient clause when
it contains the complement of the resolved literal, and `none` on an exact
miss (the chain clause is then used). -/
def exactReason {p : CompiledProblem DomConstraint} {T : LitTable}
    (b : Literal) (rc : Option (EClause p T)) : Option (EClause p T) :=
  match rc with
  | some c => if c.lits.any (fun q => litEqB q.lit b.negate) then some c else none
  | none => none

/-- Add the literals of a reason clause that are not the resolved
complement, explaining and checking each. -/
def addReasonLits (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (b : Literal) (acc : Array CItem) :
    List Literal → Except String (Array CItem)
  | [] => .ok acc
  | q :: qs =>
      if litEqB q b.negate then addReasonLits p init st b acc qs
      else
        match explainLit init st q with
        | none => .error s!"no explanation for {repr q}"
        | some ni =>
            if itemOKB p init st ni then
              addReasonLits p init st b (addCItem acc ni) qs
            else .error s!"unchecked item for {repr q}"


/-- A true `any` over the carried literals yields membership of the
complement in the decoded clause list. -/
theorem mem_of_any_litEqB {p : CompiledProblem DomConstraint} {T : LitTable}
    {c : EClause p T} {l : Literal}
    (h : c.lits.any (fun q => litEqB q.lit l) = true) :
    l ∈ c.lits.toList.map (fun q => q.lit) := by
  obtain ⟨i, hi, hq⟩ := Array.any_eq_true.mp h
  exact List.mem_map.mpr ⟨c.lits[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi),
      by simpa [litEqB] using hq⟩

/-- The literals produced by `addReasonLits` are exactly the accumulator
literals followed by the reason literals other than the resolved
complement. -/
theorem addReasonLits_lits_eq {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} :
    ∀ (ls : List Literal) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      out.toList.map (fun it => it.lit) =
        acc.toList.map (fun it => it.lit) ++
          ls.filter (fun q => !litEqB q b.negate)
  | [], acc, out, h => by
      simp [addReasonLits] at h
      subst h
      simp
  | q :: qs, acc, out, h => by
      unfold addReasonLits at h
      by_cases hq : litEqB q b.negate = true
      · rw [if_pos hq] at h
        rw [addReasonLits_lits_eq qs acc out h,
          List.filter_cons_of_neg (p := fun q => !litEqB q b.negate) (by simp [hq])]
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st ni = true
          · rw [if_pos hcheck] at h
            have hlit : ni.lit = q := explainLit_lit hni
            rw [addReasonLits_lits_eq qs (addCItem acc ni) out h,
              List.filter_cons_of_pos (p := fun q => !litEqB q b.negate) (by simp [hq])]
            simp [addCItem, hlit]
          · rw [if_neg hcheck] at h
            simp at h

/-- Every clause carried by an `EClause` is entailed at the literal level. -/
theorem eClause_entailed_lits {p : CompiledProblem DomConstraint} {T : LitTable}
    (c : EClause p T) :
    Entailed p (c.lits.toList.map (fun q => q.lit)) := by
  simpa [LitTable.decodeClause, LitTable.decode, PLit.decode] using c.ent

/-- `addReasonLits` preserves the explanation invariant. -/
theorem addReasonLits_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} :
    ∀ (ls : List Literal) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      (∀ x, x ∈ acc.toList → ItemExplained p init st x) →
      ∀ x, x ∈ out.toList → ItemExplained p init st x
  | [], acc, out, h, hacc => by
      simp [addReasonLits] at h
      subst h
      exact hacc
  | q :: qs, acc, out, h, hacc => by
      unfold addReasonLits at h
      by_cases hq : litEqB q b.negate = true
      · rw [if_pos hq] at h
        exact addReasonLits_explained qs acc out h hacc
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st ni = true
          · rw [if_pos hcheck] at h
            exact addReasonLits_explained qs (addCItem acc ni) out h
              (addCItem_explained hacc (itemOKB_spec hcheck).1)
          · rw [if_neg hcheck] at h
            simp at h

/-- `addReasonLits` preserves current falsity. -/
theorem addReasonLits_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} :
    ∀ (ls : List Literal) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      (∀ x, x ∈ acc.toList → ItemFalse st x) →
      ∀ x, x ∈ out.toList → ItemFalse st x
  | [], acc, out, h, hacc => by
      simp [addReasonLits] at h
      subst h
      exact hacc
  | q :: qs, acc, out, h, hacc => by
      unfold addReasonLits at h
      by_cases hq : litEqB q b.negate = true
      · rw [if_pos hq] at h
        exact addReasonLits_false qs acc out h hacc
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st ni = true
          · rw [if_pos hcheck] at h
            exact addReasonLits_false qs (addCItem acc ni) out h
              (addCItem_false hacc (itemOKB_spec hcheck).2)
          · rw [if_neg hcheck] at h
            simp at h

theorem removeLitItems_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {l : Literal}
    (h : ∀ x, x ∈ items.toList → ItemExplained p init st x) :
    ∀ x, x ∈ (removeLitItems items l).toList → ItemExplained p init st x := by
  intro x hx
  have hxarr : x ∈ removeLitItems items l := Array.mem_toList_iff.mp hx
  exact h x (Array.mem_toList_iff.mpr (removeLitItems_mem.mp hxarr).1)

theorem removeLitItems_false {p : CompiledProblem DomConstraint}
    {st : EngineState p T} {items : Array CItem} {l : Literal}
    (h : ∀ x, x ∈ items.toList → ItemFalse st x) :
    ∀ x, x ∈ (removeLitItems items l).toList → ItemFalse st x := by
  intro x hx
  have hxarr : x ∈ removeLitItems items l := Array.mem_toList_iff.mp hx
  exact h x (Array.mem_toList_iff.mpr (removeLitItems_mem.mp hxarr).1)

/-- Resolve the item `(b, pos)` out of `items`, using `rc` when it exposes
`b.negate` and the slot chain clause otherwise.  All copies of `b` are
removed; every other added literal is checked. -/
def resolveWith (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (items : Array CItem) (_i : Nat) (b : Literal)
    (pos : Nat) (rc : Option (EClause p T)) : Except String (Array CItem) :=
  match exactReason b rc with
  | some c =>
      addReasonLits p init st b (removeLitItems items b)
        (c.lits.toList.map (fun q => q.lit))
  | none =>
      if chainCertCheckB p init st (atomSlot b.atom) then
        addReasonLits p init st b (removeLitItems items b)
          (chainReasonLits st (atomSlot b.atom) pos b).toList
      else .error "chain certificate failed"

/-- Literal-level computation rule for `resolveWith`. -/
theorem resolveWith_lits_eq {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (h : resolveWith p init st items i b pos rc = .ok items') :
    items'.toList.map (fun it => it.lit) =
      (removeLitItems items b).toList.map (fun it => it.lit) ++
        (match exactReason b rc with
         | some c => (c.lits.toList.map (fun q => q.lit)).filter
             (fun q => !litEqB q b.negate)
         | none => (chainReasonLits st (atomSlot b.atom) pos b).toList.filter
             (fun q => !litEqB q b.negate)) := by
  unfold resolveWith at h
  cases hex : exactReason b rc with
  | some c =>
      simp only [hex] at h
      rw [addReasonLits_lits_eq _ _ _ h]
  | none =>
      simp only [hex] at h
      by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
      · rw [if_pos hcheck] at h
        rw [addReasonLits_lits_eq _ _ _ h]
      · rw [if_neg hcheck] at h
        simp at h



/-- An exact reason exposes the resolved complement. -/
theorem exactReason_some_any {p : CompiledProblem DomConstraint} {T : LitTable}
    {b : Literal} {rc : Option (EClause p T)} {c : EClause p T}
    (h : exactReason b rc = some c) :
    c.lits.any (fun q => litEqB q.lit b.negate) = true := by
  cases rc with
  | none => simp [exactReason] at h
  | some c' =>
      by_cases hany : c'.lits.any (fun q => litEqB q.lit b.negate) = true
      · simp [exactReason, hany] at h
        subst h
        exact hany
      · simp [exactReason, hany] at h

/-- A successful chain resolution carries the runtime chain certificate. -/
theorem chainCert_of_resolveWith_ok_none {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {items : Array CItem} {i : Nat}
    {b : Literal} {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (h : resolveWith p init st items i b pos rc = .ok items')
    (hn : exactReason b rc = none) :
    ChainCert p init st (atomSlot b.atom) := by
  unfold resolveWith at h
  simp only [hn] at h
  by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
  · exact chainCertCheckB_spec hcheck
  · rw [if_neg hcheck] at h
    simp at h

/-- **B3.**  One resolution step preserves entailment.  The reason side is
either an exact stored/transient clause exposing `b.negate`, or the slot
chain clause (whose entailment the caller obtains from B2). -/
theorem resolveWith_entailed {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (hitems : Entailed p (items.toList.map (fun it => it.lit)))
    (hbmem : b ∈ items.toList.map (fun it => it.lit))
    (hresolve : resolveWith p init st items i b pos rc = .ok items')
    (hexact : ∀ c, exactReason b rc = some c →
      Entailed p (c.lits.toList.map (fun q => q.lit)))
    (hchain : exactReason b rc = none →
      Entailed p (chainReasonLits st (atomSlot b.atom) pos b).toList) :
    Entailed p (items'.toList.map (fun it => it.lit)) := by
  have hstep := resolveWith_lits_eq hresolve
  cases hsrc : exactReason b rc with
  | some c =>
    have hany := exactReason_some_any hsrc
    have hnegmem := mem_of_any_litEqB hany
    have hent := hexact c hsrc
    have hres := resolve_entailed hitems hent hbmem hnegmem
    rw [hstep, hsrc, removeLitItems_lits]
    exact hres
  | none =>
    have hchainE := hchain hsrc
    have hnegmem : b.negate ∈ (chainReasonLits st (atomSlot b.atom) pos b).toList :=
      mem_chainReasonLits.mpr (Or.inl rfl)
    have hres := resolve_entailed hitems hchainE hbmem hnegmem
    rw [hstep, hsrc, removeLitItems_lits]
    exact hres


/-- `resolveWith` preserves the explanation invariant once the input has
it (the new items are checked by `itemOKB`). -/
theorem resolveWith_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (h : resolveWith p init st items i b pos rc = .ok items')
    (hacc : ∀ x, x ∈ (removeLitItems items b).toList →
      ItemExplained p init st x) :
    ∀ x, x ∈ items'.toList → ItemExplained p init st x := by
  unfold resolveWith at h
  cases hex : exactReason b rc with
  | some c =>
      simp only [hex] at h
      exact addReasonLits_explained _ _ _ h hacc
  | none =>
      simp only [hex] at h
      by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
      · rw [if_pos hcheck] at h
        exact addReasonLits_explained _ _ _ h hacc
      · rw [if_neg hcheck] at h
        simp at h

/-- `resolveWith` preserves current falsity. -/
theorem resolveWith_false {p : CompiledProblem DomConstraint}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (h : resolveWith p init st items i b pos rc = .ok items')
    (hacc : ∀ x, x ∈ (removeLitItems items b).toList → ItemFalse st x) :
    ∀ x, x ∈ items'.toList → ItemFalse st x := by
  unfold resolveWith at h
  cases hex : exactReason b rc with
  | some c =>
      simp only [hex] at h
      exact addReasonLits_false _ _ _ h hacc
  | none =>
      simp only [hex] at h
      by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
      · rw [if_pos hcheck] at h
        exact addReasonLits_false _ _ _ h hacc
      · rw [if_neg hcheck] at h
        simp at h

/-- **B3.**  A successful resolution step preserves the full item
invariant.  The caller supplies the chain entailment (B2) on the exact-miss
branch, which is the only branch that uses the chain clause. -/
theorem resolveWith_inv {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (hinv : ItemsInv p init st items)
    (hbmem : b ∈ items.toList.map (fun it => it.lit))
    (hresolve : resolveWith p init st items i b pos rc = .ok items')
    (hchain : exactReason b rc = none →
      Entailed p (chainReasonLits st (atomSlot b.atom) pos b).toList) :
    ItemsInv p init st items' where
  ent := resolveWith_entailed hinv.ent hbmem hresolve
    (fun c _ => eClause_entailed_lits c) hchain
  explained := resolveWith_explained hresolve (removeLitItems_explained hinv.explained)
  isFalse := resolveWith_false (init := init) hresolve (removeLitItems_false hinv.isFalse)

/-! ## Level-0 erasure -/

/-- **B4.**  A literal and its entailed unit negation can both be removed
from a clause: the unit resolves the literal away. -/
theorem entailed_of_entailed_cons_initial {p : CompiledProblem DomConstraint}
    {l : Literal} {D : Clause}
    (h : Entailed p (l :: D)) (hunit : Entailed p [l.negate]) :
    Entailed p D := by
  intro b hb hacc
  obtain ⟨x, hx, hev⟩ := h b hb hacc
  rcases List.mem_cons.mp hx with rfl | hx
  · obtain ⟨y, hy, hyv⟩ := hunit b hb hacc
    simp only [List.mem_singleton] at hy
    subst hy
    rw [Literal.eval_negate, hev] at hyv
    simp at hyv
  · exact ⟨x, hx, hev⟩

/-- **B4.**  An initial-domain falsity yields the entailed unit negation of
the literal.  Range and conversion facts are explicit: out-of-range slots
have no accepted value, so the statement is not made for them.  `InitInv`
is not needed: the conversion equation already says the compiled initial
domain is `init` at this slot, which is all the membership bridge uses. -/
theorem initialDomain_neg_entailed {p : CompiledProblem DomConstraint}
    {init : Array DomC} {l : Literal} {s : Nat}
    (hslot : s < p.domains.length)
    (hconv : DomC.ofDom? (p.domains.getD s Dom.empty) =
      some (init.getD s DomC.empty))
    (hls : atomSlot l.atom = s)
    (hfalse : (init.getD s DomC.empty).evalLit l = some false) :
    Entailed p [l.negate] := by
  intro a ha hacc
  obtain ⟨v, hav, hvmem⟩ := mem_allAssigns_getElem_mem (ds := p.domains) ha hslot
  have hinitmem : (init.getD s DomC.empty).mem v = true := by
    rw [DomC.mem_iff (p.domains.getD s Dom.empty) (init.getD s DomC.empty) hconv v]
    exact hvmem
  have hinitWF : (init.getD s DomC.empty).WF := DomC.ofDom?_wf _ _ hconv
  have hfalsev : l.valueHolds v = false :=
    DomC.evalLit_false_sound _ l hinitWF hfalse v hinitmem
  have hdef : l.atom.evalAtValue v ≠ none :=
    Atom.evalAtValue_ne_none_of_mem_evalLit_false hinitmem hfalse
  have havl : a[atomSlot l.negate.atom]? = some v := by
    rw [atomSlot_eq_slot]
    have hsl : l.negate.atom.slot = s := by
      rw [← atomSlot_eq_slot]
      simpa [Literal.negate] using hls
    rw [hsl]
    exact hav
  refine ⟨l.negate, by simp, ?_⟩
  rw [Literal.eval_eq_valueHolds _ a havl]
  exact (Literal.valueHolds_negate_eq_true_iff l v hdef).mpr hfalsev


/-! ## Final clause ordering -/

/-- Remove the item at index `i` (identity out of range). -/
def eraseCItemAt (items : Array CItem) (i : Nat) : Array CItem :=
  if h : i < items.size then items.eraseIdx i else items

theorem eraseCItemAt_toList (items : Array CItem) {i : Nat} (h : i < items.size) :
    (eraseCItemAt items i).toList = items.toList.eraseIdx i := by
  simp [eraseCItemAt, h, Array.toList_eraseIdx]

/-- A list with its `i`-th element moved to the front is a permutation. -/
theorem perm_getElem_cons_eraseIdx {α : Type} (l : List α) {i : Nat}
    (h : i < l.length) : (l[i] :: l.eraseIdx i).Perm l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
      cases i with
      | zero =>
          simp [List.eraseIdx_zero]
      | succ i =>
          have hi : i < t.length := by simpa using h
          have hget : (a :: t)[i + 1] = t[i] := rfl
          rw [hget]
          have herase : (a :: t).eraseIdx (i + 1) = a :: t.eraseIdx i := by
            rw [show a :: t = [a] ++ t by rfl, List.eraseIdx_append]
            simp
          rw [herase]
          exact (List.Perm.swap a t[i] (t.eraseIdx i)).trans (List.Perm.cons a (ih hi))

/-- Variant of `perm_getElem_cons_eraseIdx` stated through a `getElem?`
lookup, avoiding dependent-index proof friction. -/
theorem perm_getElem?_cons_eraseIdx {α : Type} (l : List α) {i : Nat} {x : α}
    (h : l[i]? = some x) : (x :: l.eraseIdx i).Perm l := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  have hx : l[i] = x := by
    have h' := h
    rw [List.getElem?_eq_getElem hi] at h'
    exact Option.some.inj h'
  rw [← hx]
  exact perm_getElem_cons_eraseIdx l hi

/-- The learned literals, with the asserting item first. -/
def finishOrder (items : Array CItem) (assertIdx : Option Nat) : Array Literal :=
  match assertIdx with
  | some i =>
      match items[i]? with
      | some it => #[it.lit] ++ (eraseCItemAt items i).map (fun x => x.lit)
      | none => items.map (fun it => it.lit)
  | none => items.map (fun it => it.lit)

theorem finishOrder_perm (items : Array CItem) (assertIdx : Option Nat) :
    (finishOrder items assertIdx).toList.Perm (items.toList.map (fun it => it.lit)) := by
  cases assertIdx with
  | none =>
      simp [finishOrder]
  | some i =>
      cases hget : items[i]? with
      | none =>
          simp [finishOrder, hget]
      | some it =>
          simp only [finishOrder, hget]
          have hi : i < items.size := (Array.getElem?_eq_some_iff.mp hget).1
          have hlist : items.toList[i]? = some it := by
            simpa using hget
          rw [Array.toList_append, Array.toList_map, eraseCItemAt_toList _ hi]
          simpa using (perm_getElem?_cons_eraseIdx items.toList hlist).map
            (fun it : CItem => it.lit)

/-! ## Current-level selection -/

/-- A position is a current-level trail candidate when its item is at the
current level and explained by a real trail entry (not the sentinel). -/
def currentCandidate (items : Array CItem) (level trailSize i : Nat) : Bool :=
  let it := items.getD i default
  it.level == level && it.pos < trailSize

/-- One step of the max-position scan. -/
def maxStep (items : Array CItem) (level trailSize : Nat)
    (best : Option Nat) (i : Nat) : Option Nat :=
  if currentCandidate items level trailSize i then
    match best with
    | none => some i
    | some j =>
        if (items.getD j default).pos < (items.getD i default).pos then some i
        else best
  else best

/-- Index of the current-level item with the largest explanation position.
Only real trail entries are considered (not the initial-domain sentinel). -/
def maxCurrentIdx (items : Array CItem) (level trailSize : Nat) : Option Nat :=
  (Array.range items.size).foldl (maxStep items level trailSize) none

/-- The scan invariant: the stored index is in range and is a candidate. -/
def MaxBest (items : Array CItem) (level trailSize : Nat) : Option Nat → Prop
  | none => True
  | some j => j < items.size ∧ currentCandidate items level trailSize j = true

theorem maxStep_spec {items : Array CItem} {level trailSize i : Nat}
    {best : Option Nat} (hi : i < items.size)
    (hb : MaxBest items level trailSize best) :
    MaxBest items level trailSize (maxStep items level trailSize best i) := by
  unfold maxStep
  split
  · rename_i hcand
    cases best with
    | none => exact ⟨hi, hcand⟩
    | some j =>
        dsimp only
        have hjlt : j < items.size := hb.1
        simp only [Array.getD_eq_getElem?_getD,
          Array.getElem?_eq_getElem hjlt, Option.getD_some]
        split
        · exact ⟨hi, hcand⟩
        · exact hb
  · exact hb

theorem maxCurrentIdx_spec {items : Array CItem} {level trailSize i : Nat}
    (h : maxCurrentIdx items level trailSize = some i) :
    i < items.size ∧ (items.getD i default).level = level ∧
      (items.getD i default).pos < trailSize := by
  unfold maxCurrentIdx at h
  have hfold : MaxBest items level trailSize
      ((Array.range items.size).foldl (maxStep items level trailSize) none) := by
    refine Array.foldl_induction (as := Array.range items.size)
      (motive := fun _ best => MaxBest items level trailSize best) ?_ ?_
    · trivial
    · intro k best hb
      apply maxStep_spec _ hb
      have hk : (Array.range items.size)[k] < items.size := by
        have hkEq : (Array.range items.size)[k] = k.val := Array.getElem_range k.isLt
        rw [hkEq]
        simpa [Array.size_range] using k.isLt
      simpa using hk
  rw [h] at hfold
  obtain ⟨hlt, hcand⟩ := hfold
  unfold currentCandidate at hcand
  rw [Bool.and_eq_true] at hcand
  exact ⟨hlt, beq_iff_eq.mp hcand.1, by simpa using hcand.2⟩

/-! ## Analysis result -/

/-- Literal-block distance of an analysed clause: the number of distinct
decision levels among its items.  The learned clause is built from exactly
these items, so this is the LBD of the learned clause.  The number is pure
policy metadata; no soundness argument reads it. -/
def lbdOfItems (items : Array CItem) : Nat :=
  (items.toList.map (fun it => it.level)).eraseDups.length

/-- The result of one conflict analysis.  `learned` and `asserting` carry
placeholder indices; the search re-interns them through the live table
before adding the clause or applying the assertion. -/
structure Analysis (p : CompiledProblem DomConstraint) (T : LitTable) where
  learned : Option (EClause p T)
  backjump : Nat
  asserting : Option PLit
  /-- Literal-block distance of the learned clause; `0` for a failed
  analysis or for an analysis that learned no clause. -/
  lbd : Nat := 0
  fuel : Nat
  ok : Bool
  why : String := ""

/-- Build the final learned clause and the asserting/backjump data.  The
clause is `items` with the asserting item moved to the front. -/
def finishAnalysis (p : CompiledProblem DomConstraint) (T : LitTable)
    (items : Array CItem) (assertIdx : Option Nat) (fuel : Nat)
    (h : Entailed p (items.toList.map (fun it => it.lit))) : Analysis p T :=
  let ordered := finishOrder items assertIdx
  let assertLit? :=
    match assertIdx with
    | some i => (items[i]?).map (fun (it : CItem) => it.lit)
    | none => none
  let backjump :=
    match assertIdx with
    | some i =>
        let ai := (items.getD i default).lit
        items.foldl (fun acc (it : CItem) =>
          if litEqB it.lit ai then acc
          else if acc < it.level then it.level else acc) 0
    | none => items.foldl (fun acc (it : CItem) =>
        if acc < it.level then it.level else acc) 0
  { learned := some (EClause.ofLiterals p T ordered.toList
      (Entailed_of_perm h (finishOrder_perm items assertIdx).symm))
    backjump := backjump
    asserting := assertLit?.map pLit
    lbd := lbdOfItems items
    fuel := fuel
    ok := true }


/-! ## Checked analysis results -/

/-- The soundness and operational contract every analysis result must
satisfy.  It is packaged with the loop so no separate induction over fuel
is needed: failures are vacuous, and successful results are built by
`finishAnalysis` from an entailed item clause. -/
structure AnalysisSpec (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (a : Analysis p T) : Prop where
  ok_iff : a.ok = true ↔ a.learned.isSome
  sound : ∀ ec, a.learned = some ec → Entailed p (T.decodeClause ec.lits)
  no_claim : a.ok = false → a.learned = none
  asserting_mem : ∀ ec l, a.learned = some ec → a.asserting = some l →
    l.lit ∈ ec.lits.toList.map PLit.decode
  /-- Every literal of the learned clause is false on the current live
  domains.  This is stronger than the §C contract: it needs no separate
  `ReasonLitsFalse` hypothesis because every added reason literal was
  checked with `itemOKB` when it entered the item set. -/
  lits_false : ∀ ec, a.learned = some ec →
    ∀ l ∈ ec.lits.toList.map PLit.decode,
      (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false

theorem AnalysisSpec.sound_ok {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} {a : Analysis p T} (hs : AnalysisSpec p T st a)
    (h : a.ok = true) :
    ∃ ec, a.learned = some ec ∧ Entailed p (T.decodeClause ec.lits) := by
  cases hl : a.learned with
  | none =>
      have hsome : a.learned.isSome = true := hs.ok_iff.mp h
      simp [hl] at hsome
  | some ec => exact ⟨ec, rfl, hs.sound ec hl⟩

/-- The give-up result: no clause, no claim. -/
def failAnalysis (p : CompiledProblem DomConstraint) (T : LitTable)
    (fuel : Nat) (why : String) : Analysis p T :=
  { learned := none, backjump := 0, asserting := none, fuel := fuel,
    ok := false, why := why }

theorem failAnalysis_spec {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (fuel : Nat) (why : String) :
    AnalysisSpec p T st (failAnalysis p T fuel why) := by
  constructor
  · simp [failAnalysis]
  · intro ec h
    simp [failAnalysis] at h
  · intro _
    rfl
  · intro ec l h
    simp [failAnalysis] at h
  · intro ec h
    simp [failAnalysis] at h

/-! ## Item-level helpers for the loop -/

theorem toList_eq_cons_tail_of_getElem?_zero {items : Array CItem} {it : CItem}
    (h : items[0]? = some it) : items.toList = it :: items.toList.tail := by
  have h' : items.toList[0]? = some it := by simpa using h
  cases hl : items.toList with
  | nil => simp [hl] at h'
  | cons a t =>
      simp only [hl, List.getElem?_cons_zero, Option.some.injEq] at h'
      subst h'
      rfl

theorem eraseCItemAt_zero_toList {items : Array CItem} {it : CItem}
    (h : items[0]? = some it) :
    (eraseCItemAt items 0).toList = items.toList.tail := by
  have h0 : 0 < items.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [eraseCItemAt_toList items h0]
  simp [List.eraseIdx_zero]

theorem mem_of_getElem?_zero {items : Array CItem} {it : CItem}
    (h : items[0]? = some it) : it ∈ items.toList := by
  obtain ⟨h0, hval⟩ := Array.getElem?_eq_some_iff.mp h
  rw [← hval]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem h0)

/-- Erasing a sentinel item preserves the item invariant, using the
entailed unit negation of the erased literal. -/
theorem eraseCItemAt_zero_inv {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {items : Array CItem} {it : CItem}
    (hinv : ItemsInv p init st items) (hget : items[0]? = some it)
    (hunit : Entailed p [it.lit.negate]) :
    ItemsInv p init st (eraseCItemAt items 0) where
  ent := by
    have hcons : items.toList = it :: items.toList.tail :=
      toList_eq_cons_tail_of_getElem?_zero hget
    rw [eraseCItemAt_zero_toList hget]
    have h := hinv.ent
    rw [hcons] at h
    exact entailed_of_entailed_cons_initial h hunit
  explained := by
    intro x hx
    have hx' : x ∈ items.toList.tail := by
      rwa [eraseCItemAt_zero_toList hget] at hx
    exact hinv.explained x (by
      rw [toList_eq_cons_tail_of_getElem?_zero hget]
      exact List.mem_of_mem_tail hx')
  isFalse := by
    intro x hx
    have hx' : x ∈ items.toList.tail := by
      rwa [eraseCItemAt_zero_toList hget] at hx
    exact hinv.isFalse x (by
      rw [toList_eq_cons_tail_of_getElem?_zero hget]
      exact List.mem_of_mem_tail hx')

/-- A sentinel item (false already in the initial domain) has an entailed
unit negation. -/
theorem sentinel_unit {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (hexp : ItemExplained p init st it)
    (hsent : it.pos = st.trail.size) : Entailed p [it.lit.negate] := by
  rcases hexp.expl with ⟨_, _, hfalse⟩ | ⟨e, he, _⟩
  · exact initialDomain_neg_entailed hexp.slot_lt hexp.conv rfl hfalse
  · rw [hsent] at he
    simp at he

/-- The chain clause of an item whose explanation is a real trail entry, using
the runtime chain certificate. -/
theorem chain_entailed_of_item {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {it : CItem} {e : Entry}
    (hcert : ChainCert p init st (atomSlot it.lit.atom))
    (hexp : ItemExplained p init st it)
    (he : st.trail[it.pos]? = some e)
    (hposne : it.pos ≠ st.trail.size) :
    Entailed p (chainReasonLits st (atomSlot it.lit.atom) it.pos it.lit).toList := by
  rcases hexp.expl with ⟨hpos, _⟩ | ⟨e', he', _, _, hcidx, hprev, hfalse⟩
  · exact absurd hpos hposne
  · have hee : e' = e := by
      rw [he'] at he
      exact Option.some.inj he
    subst hee
    exact chainReasonLits_entailed_of_cert hcert hcidx he' hprev rfl hfalse

/-! ## Final-clause membership -/

theorem mem_ofLiterals_lits_iff {p : CompiledProblem DomConstraint} {T : LitTable}
    {ls : List Literal} {h : Entailed p ls} {l : Literal} :
    l ∈ (EClause.ofLiterals p T ls h).lits.toList.map PLit.decode ↔ l ∈ ls := by
  simp [EClause.ofLiterals, EClause.ofLits, PLit.decode, pLit]

theorem mem_finishOrder_of_getElem? {items : Array CItem} {i : Nat} {it : CItem}
    (hget : items[i]? = some it) :
    it.lit ∈ (finishOrder items (some i)).toList := by
  simp [finishOrder, hget]

/-- Every result built by `finishAnalysis` satisfies the contract, provided
the final item set is false on the current domains. -/
theorem finishAnalysis_spec {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} {items : Array CItem} {assertIdx : Option Nat}
    {fuel : Nat} (hent : Entailed p (items.toList.map (fun it => it.lit)))
    (hfalse : ∀ it, it ∈ items.toList → ItemFalse st it) :
    AnalysisSpec p T st (finishAnalysis p T items assertIdx fuel hent) := by
  have hlearn : (finishAnalysis p T items assertIdx fuel hent).learned =
      some (EClause.ofLiterals p T (finishOrder items assertIdx).toList
        (Entailed_of_perm hent (finishOrder_perm items assertIdx).symm)) := rfl
  constructor
  · simp [finishAnalysis]
  · intro ec hec
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec]
    exact (EClause.ofLiterals p T (finishOrder items assertIdx).toList
      (Entailed_of_perm hent (finishOrder_perm items assertIdx).symm)).ent
  · intro h
    simp [finishAnalysis] at h
  · intro ec l hec has
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec]
    cases ha : assertIdx with
    | none =>
        have has' : (finishAnalysis p T items none fuel hent).asserting = some l := by
          simpa [ha] using has
        simp [finishAnalysis] at has'
    | some i =>
        cases hget : items[i]? with
        | none =>
            simp [finishAnalysis, ha, hget] at has
        | some it =>
            have hhas : l = pLit it.lit := by
              simp only [finishAnalysis, ha, hget, Option.map_some] at has
              exact (Option.some.inj has).symm
            subst hhas
            rw [mem_ofLiterals_lits_iff]
            exact mem_finishOrder_of_getElem? hget
  · intro ec hec l hl
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec] at hl
    rw [mem_ofLiterals_lits_iff] at hl
    have hmem : l ∈ items.toList.map (fun it => it.lit) :=
      (finishOrder_perm items assertIdx).mem_iff.mp hl
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hmem
    exact hfalse it hit

/-- Auxiliary bound for the asserting backjump fold: if every item is either
the asserting literal or sits strictly below the current level, the fold
cannot reach the current level. -/
private theorem foldl_backjump_lt_aux (l : List CItem) (ai : Literal) (L : Nat)
    (h : ∀ it ∈ l, litEqB it.lit ai = true ∨ it.level < L) :
    ∀ acc, acc < L →
      l.foldl (fun acc it =>
        if litEqB it.lit ai then acc
        else if acc < it.level then it.level else acc) acc < L := by
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons it rest ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      · intro x hx
        exact h x (List.mem_cons_of_mem _ hx)
      · by_cases hlit : litEqB it.lit ai = true
        · simpa [hlit] using hacc
        · simp only [hlit, Bool.false_eq_true, if_false]
          split
          · rcases h it (by simp) with hh | hh
            · simp [hlit] at hh
            · exact hh
          · exact hacc

/-- **§C, conditional form.**  If a `finishAnalysis` result asserts on an
item at the current level and every *other* item sits strictly below that
level, then its backjump is strictly below the current level.

The public `analyze` interface does not expose the final item array, and
uniqueness of the current-level item at `finishAnalysis` time is not part of
`ItemsInv`; the unconditional `analyze_backjump_lt` is therefore not stated
here.  N9 keeps the runtime `backjump < st.level` check as the guard. -/
theorem finishAnalysis_backjump_lt
    {p : CompiledProblem DomConstraint} {T : LitTable} {st : EngineState p T}
    {items : Array CItem} {i : Nat} {it : CItem} {fuel : Nat}
    {hent : Entailed p (items.toList.map (fun it => it.lit))}
    (hget : items[i]? = some it)
    (hlevel : it.level = st.level)
    (hothers : ∀ j (jt : CItem), items[j]? = some jt → j ≠ i →
      jt.level < st.level)
    (hpos : 0 < st.level) :
    (finishAnalysis p T items (some i) fuel hent).backjump < st.level := by
  have hd : items.getD i default = it := by
    rw [Array.getD_eq_getElem?_getD, hget]
    rfl
  have hfold := foldl_backjump_lt_aux items.toList it.lit st.level ?_ 0 hpos
  · dsimp only [finishAnalysis]
    rw [hd]
    rw [← Array.foldl_toList]
    exact hfold
  · intro jt hjt
    obtain ⟨j, hjget⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hjt)
    by_cases hji : j = i
    · left
      have hjeq : jt = it := by
        rw [hji] at hjget
        rw [hget] at hjget
        exact (Option.some.inj hjget).symm
      subst hjeq
      simp [litEqB]
    · right
      exact hothers j jt hjget hji

/-! ## The analysis loop -/

/-- One generalized first-UIP run.  The subtype carries the proof contract,
so the recursive cases return it unchanged. -/
def analyzeGo (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) :
    Nat → (items : Array CItem) → ItemsInv p init st items →
      { a : Analysis p T // AnalysisSpec p T st a }
  | 0, _, _ =>
      ⟨failAnalysis p T 0 "analysis fuel exhausted", failAnalysis_spec 0 _⟩
  | f + 1, items, hinv =>
      if hlev : st.level = 0 then
        match hget : items[0]? with
        | none =>
            ⟨finishAnalysis p T items none (f + 1) hinv.ent,
              finishAnalysis_spec hinv.ent hinv.isFalse⟩
        | some it =>
            if hsent : it.pos = st.trail.size then
              analyzeGo p T init st f (eraseCItemAt items 0)
                (eraseCItemAt_zero_inv hinv hget
                  (sentinel_unit (hinv.explained it (mem_of_getElem?_zero hget)) hsent))
            else
              match htr : st.trail[it.pos]? with
              | none =>
                  ⟨failAnalysis p T f s!"missing trail entry {it.pos}",
                    failAnalysis_spec f _⟩
              | some e =>
                  match e.reason with
                  | .decision =>
                      ⟨failAnalysis p T f "decision at level 0",
                        failAnalysis_spec f _⟩
                  | _ =>
                      match hres : resolveWith p init st items 0 it.lit it.pos
                          (reasonClause? st e.reason) with
                      | .error msg =>
                          ⟨failAnalysis p T f msg, failAnalysis_spec f _⟩
                      | .ok items' =>
                          analyzeGo p T init st f items'
                            (resolveWith_inv hinv
                              (List.mem_map.mpr
                                ⟨it, mem_of_getElem?_zero hget, rfl⟩)
                              hres
                              (fun hn => chain_entailed_of_item
                                (chainCert_of_resolveWith_ok_none hres hn)
                                (hinv.explained it (mem_of_getElem?_zero hget))
                                htr hsent))
      else
        match hmax : maxCurrentIdx items st.level st.trail.size with
        | none =>
            ⟨finishAnalysis p T items none (f + 1) hinv.ent,
              finishAnalysis_spec hinv.ent hinv.isFalse⟩
        | some i =>
            have hi : i < items.size := (maxCurrentIdx_spec hmax).1
            let it := items[i]
            match htr : st.trail[it.pos]? with
            | none =>
                ⟨failAnalysis p T f s!"missing trail entry {it.pos}",
                  failAnalysis_spec f _⟩
            | some e =>
                match e.reason with
                | .decision =>
                    ⟨finishAnalysis p T items (some i) (f + 1) hinv.ent,
                      finishAnalysis_spec hinv.ent hinv.isFalse⟩
                | _ =>
                    match hres : resolveWith p init st items i it.lit it.pos
                        (reasonClause? st e.reason) with
                    | .error msg =>
                        ⟨failAnalysis p T f msg, failAnalysis_spec f _⟩
                    | .ok items' =>
                        analyzeGo p T init st f items'
                          (resolveWith_inv hinv
                            (List.mem_map.mpr
                              ⟨it, Array.mem_toList_iff.mpr (Array.getElem_mem hi), rfl⟩)
                            hres
                            (fun hn => chain_entailed_of_item
                              (chainCert_of_resolveWith_ok_none hres hn)
                              (hinv.explained it
                                (Array.mem_toList_iff.mpr (Array.getElem_mem (maxCurrentIdx_spec hmax).1)))
                              htr
                              (by
                                have hlt := (maxCurrentIdx_spec hmax).2.2
                                have hgetD : items.getD i default = items[i] := by
                                  rw [Array.getD_eq_getElem?_getD,
                                    Array.getElem?_eq_getElem (maxCurrentIdx_spec hmax).1]
                                  rfl
                                have hposlt : it.pos < st.trail.size := by
                                  dsimp [it]
                                  rwa [← hgetD]
                                omega)))

/-- Analyze a conflict clause.  Missing explanations or exhausting the fuel
give up with no claim; a successful run carries an entailed learned clause. -/
def analyze (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) (conflict : EClause p T)
    (fuel : Nat) : Analysis p T :=
  match hinit : initialItems p init st
      (T.decodeClause conflict.lits) with
  | none => failAnalysis p T fuel "initial conflict explanation incomplete"
  | some items =>
      (analyzeGo p T init st fuel items
        (initialItems_inv conflict.ent hinit)).1

theorem analyze_of_initialItems_none {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {conflict : EClause p T} {fuel : Nat}
    (h : initialItems p init st (T.decodeClause conflict.lits) = none) :
    analyze p T init st conflict fuel =
      failAnalysis p T fuel "initial conflict explanation incomplete" := by
  unfold analyze
  split
  · rfl
  · rename_i hsome
    rw [h] at hsome
    cases hsome

theorem analyze_of_initialItems_some {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {conflict : EClause p T} {fuel : Nat} {items : Array CItem}
    (h : initialItems p init st (T.decodeClause conflict.lits) = some items) :
    analyze p T init st conflict fuel =
      (analyzeGo p T init st fuel items (initialItems_inv conflict.ent h)).1 := by
  unfold analyze
  split
  · rename_i hnone
    rw [h] at hnone
    cases hnone
  · rename_i items' hsome
    rw [h] at hsome
    injection hsome with heq
    subst heq
    have hp : (initialItems_inv conflict.ent hsome) =
        (initialItems_inv conflict.ent h) := Subsingleton.elim _ _
    rw [hp]

theorem analyze_sound {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {conflict : EClause p T}
    {fuel : Nat} (h : (analyze p T init st conflict fuel).ok = true) :
    ∃ ec, (analyze p T init st conflict fuel).learned = some ec ∧
      Entailed p (T.decodeClause ec.lits) := by
  by_cases hnone : initialItems p init st
      (T.decodeClause conflict.lits) = none
  · rw [analyze_of_initialItems_none hnone] at h ⊢
    simp [failAnalysis] at h
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hsome] at h ⊢
    exact (analyzeGo p T init st fuel items
      (initialItems_inv conflict.ent hsome)).2.sound_ok h

theorem analyze_learned_none_of_not_ok {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {conflict : EClause p T} {fuel : Nat}
    (h : (analyze p T init st conflict fuel).ok = false) :
    (analyze p T init st conflict fuel).learned = none := by
  by_cases hnone : initialItems p init st
      (T.decodeClause conflict.lits) = none
  · rw [analyze_of_initialItems_none hnone] at h ⊢
    rfl
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hsome] at h ⊢
    exact (analyzeGo p T init st fuel items
      (initialItems_inv conflict.ent hsome)).2.no_claim h

/-- Alias for the §C operational name. -/
theorem analyze_no_claim_on_failure {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {conflict : EClause p T} {fuel : Nat}
    (h : (analyze p T init st conflict fuel).ok = false) :
    (analyze p T init st conflict fuel).learned = none :=
  analyze_learned_none_of_not_ok h

theorem analyze_ok_learned {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {conflict : EClause p T}
    {fuel : Nat} :
    (analyze p T init st conflict fuel).ok = true ↔
      (analyze p T init st conflict fuel).learned.isSome := by
  by_cases hnone : initialItems p init st
      (T.decodeClause conflict.lits) = none
  · rw [analyze_of_initialItems_none hnone]
    simp [failAnalysis]
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hsome]
    exact (analyzeGo p T init st fuel items
      (initialItems_inv conflict.ent hsome)).2.ok_iff

theorem analyze_empty_unsat {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {conflict : EClause p T}
    {fuel : Nat} {ec : EClause p T}
    (hok : (analyze p T init st conflict fuel).ok = true)
    (hlearned : (analyze p T init st conflict fuel).learned = some ec)
    (hempty : ec.lits.isEmpty) : Entailed p [] := by
  obtain ⟨ec', hec', hent⟩ := analyze_sound hok
  rw [hlearned] at hec'
  rw [Option.some.injEq] at hec'
  subst hec'
  have hto : ec.lits.toList = [] := Array.toList_eq_nil_iff.mpr
    (Array.isEmpty_iff.mp hempty)
  have hdec : T.decodeClause ec.lits = [] := by
    simp [LitTable.decodeClause, hto]
  rwa [hdec] at hent

theorem analyze_asserting_mem {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {conflict : EClause p T}
    {fuel : Nat} {ec : EClause p T} {l : PLit}
    (hlearned : (analyze p T init st conflict fuel).learned = some ec)
    (hasserting : (analyze p T init st conflict fuel).asserting = some l) :
    l.lit ∈ ec.lits.toList.map PLit.decode := by
  by_cases hnone : initialItems p init st
      (T.decodeClause conflict.lits) = none
  · rw [analyze_of_initialItems_none hnone] at hlearned
    simp [failAnalysis] at hlearned
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hsome] at hlearned hasserting
    exact (analyzeGo p T init st fuel items
      (initialItems_inv conflict.ent hsome)).2.asserting_mem ec l hlearned hasserting

/-- **§C, stronger form.**  Every literal of the learned clause is false on
the current live domains.  No separate reason-falsity hypothesis is needed:
`analyzeGo` checks every item it adds with `itemOKB` (`itemCheckB` plus
`domFalseB`), so the item invariant carries current falsity throughout. -/
theorem analyze_learned_lits_false {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {conflict : EClause p T} {fuel : Nat} {ec : EClause p T}
    (hlearned : (analyze p T init st conflict fuel).learned = some ec) :
    ∀ l ∈ ec.lits.toList.map PLit.decode,
      (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  by_cases hnone : initialItems p init st
      (T.decodeClause conflict.lits) = none
  · rw [analyze_of_initialItems_none hnone] at hlearned
    simp [failAnalysis] at hlearned
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hsome] at hlearned
    exact (analyzeGo p T init st fuel items
      (initialItems_inv conflict.ent hsome)).2.lits_false ec hlearned

end LeanFzn.Engine

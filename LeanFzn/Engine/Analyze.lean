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
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet
import Std.Data.HashSet.Lemmas

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
  /-- Optional intern-index hint for the learned-clause fast path.  It is
  never trusted: canonicalisation revalidates it against the live table. -/
  pidx : Option Nat := none
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
            some { lit := l, pos := pos, level := e.level, cidx := i }
          else findExplainList tr l rest (i + 1)
      | none => findExplainList tr l rest (i + 1)

/-- Bounded explanation search starting at change-list index `i`.  Used when
the caller already knows a change-list index at which the literal is false
(the chain-reason literals are exactly the negations of their entries). -/
def findExplainFuel (tr : Array Entry) (l : Literal) (a : Array Nat)
    (i : Nat) : Nat → Option CItem
  | 0 => none
  | fuel + 1 =>
      if h : i < a.size then
        match tr[a[i]]? with
        | some e =>
            if (e.prev.applyLit e.lit.lit).evalLit l == some false then
              some { lit := l, pos := a[i], level := e.level, cidx := i }
            else findExplainFuel tr l a (i + 1) fuel
        | none => findExplainFuel tr l a (i + 1) fuel
      else none

theorem findExplainFuel_lit {tr : Array Entry} {l : Literal} {a : Array Nat}
    {i fuel : Nat} {it : CItem}
    (h : findExplainFuel tr l a i fuel = some it) : it.lit = l := by
  induction fuel generalizing i with
  | zero => simp [findExplainFuel] at h
  | succ f ih =>
      unfold findExplainFuel at h
      split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            rfl
          · exact ih h
        · exact ih h
      · simp at h

/-- Earliest explanation of a false literal: the initial domain, or the
first trail entry after which the slot domain falsifies it. -/
def explainLit (init : Array DomC) (st : EngineState p T) (l : Literal) :
    Option CItem :=
  if (init.getD (atomSlot l.atom) DomC.empty).evalLit l == some false then
    some { lit := l, pos := st.trail.size, level := 0, cidx := 0 }
  else
    findExplainList st.trail l (st.changeList (atomSlot l.atom)).toList 0

/-- Post-domain of the `k`-th change of slot `s`, read without replaying
`applyLit`: it is the next entry's undo image, or the live domain for the
final change.  Under `SlotHistory` this equals
`entry.prev.applyLit entry.lit.lit`, so explanation search can test the
stored domains directly. -/
def postDomAt (st : EngineState p T) (s : Slot) (k : Nat) : DomC :=
  let a := st.changeList s
  match a[k + 1]? with
  | some pos => (st.trail.getD pos default).prev
  | none => st.doms.getD s DomC.empty

/-- `postDomAt` is the replayed domain after change `k`: the next change's
stored undo image, or the live domain after the final change.  This is the
specification that justifies reading `postDomAt` instead of replaying
`applyLit` in explanation search. -/
theorem postDomAt_spec {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) {s : Slot} {k : Nat}
    (hk : k < (st.changeList s).size) :
    postDomAt st s k = domAfter init st s (k + 1) := by
  unfold postDomAt
  dsimp only
  by_cases hnext : k + 1 < (st.changeList s).size
  · have hget : (st.changeList s)[k + 1]? =
        some ((st.changeList s).getD (k + 1) 0) := by
      rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hnext]
      rfl
    rw [hget]
    exact hhist.prev_eq s (k + 1) hnext
  · have hsize : k + 1 = (st.changeList s).size := by omega
    have hnone : (st.changeList s)[k + 1]? = none := by
      rw [Array.getElem?_eq_none_iff]
      omega
    rw [hnone, hsize]
    dsimp only
    exact hhist.doms_eq s

/-- The entry-level form of `postDomAt`: it equals the entry's own undo
image with the entry literal applied, which is exactly what
`findExplainList` tests. -/
theorem postDomAt_entry_spec {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) (hTI : TrailInv st) {s : Slot} {k : Nat}
    (hk : k < (st.changeList s).size) :
    postDomAt st s k =
      (st.trail.getD ((st.changeList s).getD k 0) default).prev.applyLit
        (st.trail.getD ((st.changeList s).getD k 0) default).lit.lit := by
  let pos := (st.changeList s).getD k 0
  let e := st.trail.getD pos default
  have hmem : pos ∈ st.changeList s := by
    simpa [pos] using Array.getD_mem (a := st.changeList s) (i := k) hk
  obtain ⟨_, e', he', _⟩ := (hTI.changeIndex_mem s pos).1 hmem
  have he : st.trail[pos]? = some e := by
    simp [e, he']
  have hprev : e.prev = domAfter init st s k := by
    simpa [pos, e] using hhist.prev_eq s k hk
  rw [postDomAt_spec hhist hk, domAfter_succ init st s k hk, hprev]
  unfold domStep
  rw [he]

/-- Indexed explanation scan using `postDomAt` and the endpoint-local
`falsifiesLit` test.  It returns the same earliest candidate as
`findExplainList` whenever `postDomAt` agrees with the replayed
post-domain (the `SlotHistory` invariant), but allocates no intermediate
domain and does not scan the upper endpoint for a positive `posLe`. -/
def findExplainIdx (st : EngineState p T) (s : Slot) (l : Literal) :
    Nat → Nat → Option CItem
  | 0, _ => none
  | fuel + 1, i =>
      match (st.changeList s)[i]? with
      | some pos =>
          match st.trail[pos]? with
          | some e =>
              if (postDomAt st s i).falsifiesLit l then
                some { lit := l, pos := pos, level := e.level, cidx := i }
              else findExplainIdx st s l fuel (i + 1)
          | none => findExplainIdx st s l fuel (i + 1)
      | none => none

/-- Allocation-free explanation search used by the analysis hot path.
    The returned item is re-checked by `itemOKB` before use. -/
def explainLitFast (init : Array DomC) (st : EngineState p T) (l : Literal) :
    Option CItem :=
  if (init.getD (atomSlot l.atom) DomC.empty).evalLit l == some false then
    some { lit := l, pos := st.trail.size, level := 0, cidx := 0 }
  else
    let a := st.changeList (atomSlot l.atom)
    findExplainIdx st (atomSlot l.atom) l a.size 0

theorem findExplainIdx_lit {st : EngineState p T} {s : Slot} {l : Literal}
    {fuel i : Nat} {it : CItem}
    (h : findExplainIdx st s l fuel i = some it) : it.lit = l := by
  induction fuel generalizing i with
  | zero => simp [findExplainIdx] at h
  | succ f ih =>
      unfold findExplainIdx at h
      split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            rfl
          · exact ih h
        · exact ih h
      · simp at h

theorem explainLitFast_lit {init : Array DomC} {st : EngineState p T}
    {l : Literal} {it : CItem} (h : explainLitFast init st l = some it) :
    it.lit = l := by
  unfold explainLitFast at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact findExplainIdx_lit h
theorem findExplainIdx_eq_findExplainList_aux {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) (hTI : TrailInv st) (s : Slot) (l : Literal) :
    ∀ (fuel i : Nat), i + fuel = (st.changeList s).size →
      findExplainIdx st s l fuel i =
        findExplainList st.trail l ((st.changeList s).toList.drop i) i := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hi
      have hle : (st.changeList s).toList.length ≤ i := by
        simp
        omega
      have hnil : (st.changeList s).toList.drop i = [] :=
        List.drop_eq_nil_of_le hle
      simp [findExplainIdx, findExplainList, hnil]
  | succ f ih =>
      intro i hi
      have hlt : i < (st.changeList s).size := by omega
      have hlt' : i < (st.changeList s).toList.length := by simpa using hlt
      have hpos : (st.changeList s).getD i 0 = (st.changeList s)[i] := by
        rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hlt]
        rfl
      have hdrop : (st.changeList s).toList.drop i =
          (st.changeList s)[i] :: (st.changeList s).toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hlt']
        simp [Array.getElem_toList hlt']
      rw [hdrop]
      unfold findExplainIdx findExplainList
      rw [Array.getElem?_eq_getElem hlt]
      cases he : st.trail[(st.changeList s)[i]]? with
      | none =>
          simp only [he]
          exact ih (i + 1) (by omega)
      | some e =>
          simp only [he]
          have hpost := postDomAt_entry_spec hhist hTI (s := s) (k := i) hlt
          have hgd : st.trail.getD ((st.changeList s).getD i 0) default = e := by
            rw [hpos, Array.getD_eq_getElem?_getD, he]
            rfl
          rw [hgd] at hpost
          have hcond : (postDomAt st s i).falsifiesLit l =
              ((e.prev.applyLit e.lit.lit).evalLit l == some false) := by
            rw [hpost]
            by_cases hev : (e.prev.applyLit e.lit.lit).evalLit l = some false
            · have hf := (DomC.falsifiesLit_eq _ _).mpr hev
              simp [hf, hev]
            · have hf : (e.prev.applyLit e.lit.lit).falsifiesLit l = false := by
                rw [Bool.eq_false_iff]
                intro ht
                exact hev ((DomC.falsifiesLit_eq _ _).mp ht)
              have hb : ((e.prev.applyLit e.lit.lit).evalLit l == some false) = false := by
                rw [Bool.eq_false_iff]
                intro ht
                exact hev (beq_iff_eq.mp ht)
              simp [hf, hb]
          rw [hcond]
          by_cases hb : ((e.prev.applyLit e.lit.lit).evalLit l == some false) = true
          · simp [hb]
          · have hb' : ((e.prev.applyLit e.lit.lit).evalLit l == some false) = false := by
              rw [Bool.eq_false_iff]
              exact hb
            simp only [hb', Bool.false_eq_true, ite_false]
            exact ih (i + 1) (by omega)

theorem findExplainIdx_eq_findExplainList {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) (hTI : TrailInv st) (s : Slot) (l : Literal) :
    findExplainIdx st s l (st.changeList s).size 0 =
      findExplainList st.trail l ((st.changeList s).toList) 0 := by
  have h := findExplainIdx_eq_findExplainList_aux hhist hTI s l (st.changeList s).size 0 (by omega)
  simpa using h


/-- The fast scan agrees exactly with the original list scan (earliest
falsifying change), so the two explanations returned on any reachable state
are identical. -/
theorem explainLitFast_eq_explainLit {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) (hTI : TrailInv st) (l : Literal) :
    explainLitFast init st l = explainLit init st l := by
  unfold explainLitFast explainLit
  simp only [Array.getD_eq_getElem?_getD]
  by_cases h : (init[atomSlot l.atom]?.getD DomC.empty).evalLit l = some false
  · have hb : ((init[atomSlot l.atom]?.getD DomC.empty).evalLit l ==
        some false) = true := by simp [h]
    simp [hb]
  · have hb : ((init[atomSlot l.atom]?.getD DomC.empty).evalLit l ==
        some false) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      exact h (beq_iff_eq.mp ht)
    simp [hb, findExplainIdx_eq_findExplainList hhist hTI (atomSlot l.atom) l]



/-- `explainLit` with a known change-list lower bound.  Scanning starts at
`start`; the returned item records the absolute change-list index. -/
def explainLitFrom (init : Array DomC) (st : EngineState p T) (l : Literal)
    (start : Nat) : Option CItem :=
  if (init.getD (atomSlot l.atom) DomC.empty).evalLit l == some false then
    some { lit := l, pos := st.trail.size, level := 0, cidx := 0 }
  else
    let a := st.changeList (atomSlot l.atom)
    findExplainFuel st.trail l a start (a.size - start)

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

theorem explainLitFrom_lit {init : Array DomC} {st : EngineState p T}
    {l : Literal} {start : Nat} {it : CItem}
    (h : explainLitFrom init st l start = some it) : it.lit = l := by
  unfold explainLitFrom at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact findExplainFuel_lit h

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
  | sparse values =>
      dsimp only [DomC.fixedValue]
      cases hlo : arrayHead? values <;> cases hhi : arrayLast? values <;>
        simp only [hlo, hhi]
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

/-- The array mirror has the same length as the compiled domain list. -/
theorem domainsArray_size (p : CompiledProblem DomConstraint) :
    p.domainsArray.size = p.domains.length := by
  rw [← p.domainsArray_toList, Array.length_toList]

/-- The array mirror has the same defaulted lookups as the domain list. -/
theorem domainsArray_getD_eq (p : CompiledProblem DomConstraint) (s : Nat) :
    p.domainsArray.getD s Dom.empty = p.domains.getD s Dom.empty := by
  rw [Array.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    ← p.domainsArray_toList, Array.getElem?_toList]

/-- The initial converted domains are the `DomC.ofDom?` image of the
compiled domains at every slot.  `initState` establishes this once from
`convertDomains`; the search and analysis carry it as a proof-only argument,
so `itemCheckB` no longer reconverts a domain per explained literal. -/
structure InitConv (p : CompiledProblem DomConstraint) (init : Array DomC) : Prop where
  conv : ∀ s, s < p.domains.length →
    DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)

theorem InitConv.congr {p : CompiledProblem DomConstraint} {init init' : Array DomC}
    (h : InitConv p init) (heq : init' = init) : InitConv p init' := by
  subst heq
  exact h

/-- The slot is in range.  The conversion equation is supplied by
`InitConv`; this is the only part of the old `initSlotOKB` check that still
needs to run. -/
def initSlotRangeB (p : CompiledProblem DomConstraint) (s : Nat) : Bool :=
  s < p.domainsArray.size

theorem initSlotRangeB_spec {p : CompiledProblem DomConstraint} {s : Nat}
    (h : initSlotRangeB p s = true) : s < p.domains.length := by
  unfold initSlotRangeB at h
  rw [← domainsArray_size p]
  exact of_decide_eq_true h

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
  initSlotRangeB p s &&
  ((it.pos == st.trail.size && it.level == 0 &&
      ((init.getD s DomC.empty).evalLit it.lit == some false)) ||
   match st.trail[it.pos]? with
   | some e =>
       (e.level == it.level) && (e.slot == s) &&
       ((st.changeList s)[it.cidx]? == some it.pos) &&
       ((e.prev.applyLit e.lit.lit).evalLit it.lit == some false)
   | none => false)

/-- On a state with a consistent slot history, `itemCheckB` certifies
`ItemExplained`.  The undo image `e.prev` is not replayed: `hhist` supplies
the equation `e.prev = domAfter init st s it.cidx` once for every entry. -/
theorem itemCheckB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (hconv : InitConv p init)
    (hhist : SlotHistory init st)
    (h : itemCheckB p init st it = true) :
    ItemExplained p init st it := by
  unfold itemCheckB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hrange, hbody⟩ := h
  have hslot := initSlotRangeB_spec hrange
  have hconv' := hconv.conv (atomSlot it.lit.atom) hslot
  refine ⟨hslot, hconv', ?_⟩
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
            (e.prev.applyLit e.lit.lit).evalLit it.lit = some false := by
          simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using hbody
        have hcget := hbody'.2.2.1
        have hk : it.cidx < (st.changeList (atomSlot it.lit.atom)).size :=
          (Array.getElem?_eq_some_iff.mp hcget).1
        have hgd : (st.changeList (atomSlot it.lit.atom)).getD it.cidx 0 = it.pos := by
          rw [Array.getD_eq_getElem?_getD, hcget]
          rfl
        have htgd : st.trail.getD it.pos default = e := by
          rw [Array.getD_eq_getElem?_getD, htr]
          rfl
        have hprev : e.prev = domAfter init st (atomSlot it.lit.atom) it.cidx := by
          have hpv := hhist.prev_eq (atomSlot it.lit.atom) it.cidx hk
          simpa only [hgd, htgd] using hpv
        exact ⟨e, rfl, hbody'.1, hbody'.2.1, hcget, hprev,
          hbody'.2.2.2⟩

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

/-- Adjacent-pair check on a list: strictly increasing. -/
def sortedListB : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && sortedListB (y :: rest)

theorem sortedListB_pairwise {l : List Nat} (h : sortedListB l = true) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
          simp only [sortedListB, Bool.and_eq_true] at h
          rw [List.pairwise_cons]
          refine ⟨?_, ih h.2⟩
          have hxy : x < y := of_decide_eq_true h.1
          intro z hz
          have hpair := ih h.2
          rw [List.pairwise_cons] at hpair
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxy
          · exact Nat.lt_trans hxy (hpair.1 z hz)

/-- Linear-time sortedness check for a change list. -/
def sortedB (a : Array Nat) : Bool := sortedListB a.toList

theorem sortedB_spec {a : Array Nat} (h : sortedB a = true) : SortedList a := by
  unfold sortedB at h
  unfold SortedList
  exact sortedListB_pairwise h

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

/-- The chain-reason literal contributed by one change-list position, if any.
This is the `filterMap` body of `chainReasonLits`, factored out so the hinted
resolver can prove it emits the same literals. -/
def chainReasonAt (st : EngineState p T) (pos p : Nat) : Option Literal :=
  if p ≤ pos then
    match st.trail[p]? with
    | some e => some e.lit.lit.negate
    | none => none
  else none

theorem chainReasonLits_eq (st : EngineState p T) (slot pos : Nat) (b : Literal) :
    chainReasonLits st slot pos b =
      #[b.negate] ++ (st.changeIndex.getD slot #[]).filterMap (chainReasonAt st pos) :=
  rfl

/-- The filtered chain-reason literals are exactly the filtered literals of
the slot's change list, read through `chainReasonAt`.  The explicit
`b.negate` is removed by the filter. -/
theorem chainReasonLits_filter (st : EngineState p T) (slot pos : Nat) (b : Literal) :
    (chainReasonLits st slot pos b).toList.filter (fun q => !litEqB q b.negate) =
      (((st.changeIndex.getD slot #[]).toList.filterMap fun p =>
        if p ≤ pos then
          match st.trail[p]? with
          | some e => some e.lit.lit.negate
          | none => none
        else none)).filter (fun q => !litEqB q b.negate) := by
  unfold chainReasonLits
  rw [Array.toList_append, List.filter_append, Array.toList_filterMap]
  simp [litEqB]

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

/-! ## Duplicate removal -/

/-- The literal multiset of an item array, as a list. -/
def litSet (items : Array CItem) : List Literal :=
  items.toList.map (fun it => it.lit)

/-- The literal-equality relation used by item deduplication. -/
def sameLit (a b : CItem) : Bool := a.lit == b.lit

/-- Remove conflict items whose literal is already present, keeping the
first occurrence.  Duplicate items are semantically redundant (the learned
clause is a set and every item is independently explained), but they make
`scanCurrent` and `removeLitItems` rescan the same literal at every
resolution step.  This is the transparent reference body; compiled code uses
`dedupItemsFast` through the `@[csimp]` seam below. -/
def dedupItems (items : Array CItem) : Array CItem :=
  ⟨items.toList.eraseDupsBy sameLit⟩

/-- Fast compiled twin: one hash-set pass over the items, keeping the first
occurrence of each literal. -/
def dedupItemsGo (seen : Std.HashSet Literal) (acc : Array CItem) :
    List CItem → Array CItem
  | [] => acc
  | it :: rest =>
      if seen.contains it.lit then dedupItemsGo seen acc rest
      else dedupItemsGo (seen.insert it.lit) (acc.push it) rest

/-- One step of the array fold used by the compiled deduplication pass. -/
def dedupStep (st : Std.HashSet Literal × Array CItem) (it : CItem) :
    Std.HashSet Literal × Array CItem :=
  if st.1.contains it.lit then st
  else (st.1.insert it.lit, st.2.push it)

/-- Fast deduplication entry point.  It folds over the array directly so the
compiled pass does not materialise a list. -/
def dedupItemsFast (items : Array CItem) : Array CItem :=
  (items.foldl dedupStep (∅, #[])).2

/-- The array fold's second component is exactly the list-driven fast pass. -/
theorem foldl_dedupStep_snd (l : List CItem) (s : Std.HashSet Literal)
    (acc : Array CItem) :
    (l.foldl dedupStep (s, acc)).2 = dedupItemsGo s acc l := by
  induction l generalizing s acc with
  | nil => rfl
  | cons it rest ih =>
      rw [List.foldl_cons, dedupItemsGo]
      by_cases h : s.contains it.lit = true
      · rw [if_pos h]
        have hstep : dedupStep (s, acc) it = (s, acc) := by
          unfold dedupStep
          rw [if_pos h]
        rw [hstep]
        exact ih s acc
      · rw [if_neg h]
        have hstep : dedupStep (s, acc) it =
            (s.insert it.lit, acc.push it) := by
          unfold dedupStep
          rw [if_neg h]
        rw [hstep]
        exact ih _ _

/-- Every output of `dedupItemsGo` comes from the accumulator or the input
list. -/
theorem dedupItemsGo_mem {seen : Std.HashSet Literal} {acc : Array CItem}
    {l : List CItem} {x : CItem} (h : x ∈ dedupItemsGo seen acc l) :
    x ∈ acc ∨ x ∈ l := by
  induction l generalizing seen acc with
  | nil => exact Or.inl h
  | cons it rest ih =>
      unfold dedupItemsGo at h
      split at h
      · exact (ih h).imp id (List.mem_cons_of_mem _)
      · rcases ih h with hacc | hrest
        · rcases Array.mem_push.mp hacc with hold | heq
          · exact Or.inl hold
          · exact Or.inr (heq ▸ List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ hrest)

/-- Mapping the transparent deduplication to literals is exactly literal
deduplication. -/
theorem map_dedupItems_lit (l : List CItem) :
    (l.eraseDupsBy sameLit).map (fun it => it.lit) =
      (l.map (fun it => it.lit)).eraseDups := by
  induction hlen : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
      cases l with
      | nil => rfl
      | cons a as =>
          simp only [List.eraseDupsBy_cons, List.eraseDups_cons, List.map_cons]
          have hlt' : (as.filter (fun b => sameLit b a = false)).length < n := by
            have := List.length_filter_le (fun b => sameLit b a = false) as
            simp only [List.length_cons] at hlen
            omega
          rw [ih _ hlt' (as.filter (fun b => sameLit b a = false)) rfl]
          congr 1
          rw [List.filter_map]
          congr 1

/-- Literal membership through transparent deduplication is unchanged. -/
theorem dedupItems_lit_mem (items : Array CItem) (q : Literal) :
    q ∈ litSet (dedupItems items) ↔ q ∈ litSet items := by
  have h : (dedupItems items).toList.map (fun it => it.lit) =
      (items.toList.map (fun it => it.lit)).eraseDups :=
    map_dedupItems_lit items.toList
  simp only [litSet] at h ⊢
  rw [h, List.mem_eraseDups]

/-- Every element of `eraseDupsBy` comes from the input list. -/
theorem mem_of_mem_eraseDupsBy {l : List CItem} {x : CItem}
    (h : x ∈ l.eraseDupsBy sameLit) : x ∈ l := by
  induction hlen : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
      cases l with
      | nil => simp at h
      | cons a as =>
          rw [List.eraseDupsBy_cons] at h
          rcases List.mem_cons.mp h with heq | hmem
          · exact heq ▸ List.mem_cons_self ..
          · have hlt : (as.filter (fun b => sameLit b a = false)).length < n := by
              have := List.length_filter_le (fun b => sameLit b a = false) as
              simp only [List.length_cons] at hlen
              omega
            have hmem' := ih _ hlt hmem (l := as.filter (fun b => sameLit b a = false)) rfl
            exact List.mem_cons_of_mem _ (List.mem_filter.mp hmem').1

/-- Deduplication only removes copies: every surviving item was in the
input array. -/
theorem dedupItems_mem {items : Array CItem} {x : CItem}
    (h : x ∈ dedupItems items) : x ∈ items := by
  have h' : x ∈ items.toList.eraseDupsBy sameLit := Array.mem_toList_iff.mpr h
  exact Array.mem_toList_iff.mp (mem_of_mem_eraseDupsBy h')

/-- The `seen` set in the fast pass is exactly the literal set of the
accumulator. -/
theorem dedupItemsGo_litSet_push {seen : Std.HashSet Literal} {acc : Array CItem}
    {it : CItem} (hinv : ∀ x, x ∈ seen ↔ x ∈ litSet acc) :
    ∀ x, x ∈ seen.insert it.lit ↔ x ∈ litSet (acc.push it) := by
  intro x
  rw [Std.HashSet.mem_insert, hinv x]
  simp only [litSet, Array.toList_push, List.map_append, List.map_cons,
    List.map_nil, List.mem_append, List.mem_cons, beq_iff_eq]
  grind

/-- The fast pass computes the same list as filtering out already-seen
literals and then deduplicating the remainder. -/
theorem dedupItemsGo_eq_slow {seen : Std.HashSet Literal} {acc : Array CItem}
    {l : List CItem} (hinv : ∀ x, x ∈ seen ↔ x ∈ litSet acc) :
    dedupItemsGo seen acc l =
      (acc.toList ++ (l.filter (fun it => it.lit ∉ seen)).eraseDupsBy sameLit).toArray := by
  induction l generalizing seen acc with
  | nil => simp [dedupItemsGo]
  | cons it rest ih =>
      by_cases hseen : it.lit ∈ seen
      · have hcontains : seen.contains it.lit = true :=
          Std.HashSet.contains_iff_mem.mpr hseen
        rw [dedupItemsGo, if_pos hcontains, ih hinv]
        congr 1
        simp [hseen]
      · have hnot : ¬ seen.contains it.lit :=
          fun hc => hseen (Std.HashSet.contains_iff_mem.mp hc)
        rw [dedupItemsGo, if_neg hnot]
        have hinv' : ∀ x, x ∈ seen.insert it.lit ↔ x ∈ litSet (acc.push it) :=
          dedupItemsGo_litSet_push hinv
        rw [ih hinv', Array.toList_push]
        congr 1
        rw [List.filter_cons, if_pos (by simpa using hseen)]
        rw [List.eraseDupsBy_cons]
        have hfilter : rest.filter (fun x => x.lit ∉ seen.insert it.lit) =
            (rest.filter (fun x => x.lit ∉ seen)).filter
              (fun b => sameLit b it = false) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro x _
          by_cases hmem : x.lit ∈ seen
          · have hins : x.lit ∈ seen.insert it.lit :=
              Std.HashSet.mem_insert.mpr (Or.inr hmem)
            simp [hmem, hins, sameLit]
          · by_cases heq : x.lit = it.lit
            · simp [hmem, sameLit, heq, beq_iff_eq]
            · have hins : ¬ x.lit ∈ seen.insert it.lit := by
                intro h
                rcases (Std.HashSet.mem_insert.mp h) with hbeq | hmem'
                · exact heq (beq_iff_eq.mp hbeq).symm
                · exact hmem hmem'
              simp [hmem, hins, sameLit, heq]
        rw [hfilter]
        simp [List.append_assoc]

/-- The fast pass equals the transparent reference on the full array. -/
theorem dedupItemsFast_eq (items : Array CItem) :
    dedupItemsFast items = dedupItems items := by
  have h := dedupItemsGo_eq_slow (seen := ∅) (acc := #[]) (l := items.toList)
    (by intro x; simp [litSet])
  have hfilter : items.toList.filter
      (fun it => it.lit ∉ (∅ : Std.HashSet Literal)) = items.toList :=
    List.filter_eq_self.mpr (by intro x _; simp)
  rw [hfilter] at h
  unfold dedupItemsFast dedupItems
  rw [← Array.foldl_toList, foldl_dedupStep_snd]
  simpa using h

/-- Compiled code uses the hash-set pass; the kernel and every proof keep
using the transparent `eraseDupsBy` body. -/
@[csimp] theorem dedupItems_eq_fast : @dedupItems = @dedupItemsFast := by
  funext items
  exact (dedupItemsFast_eq items).symm

/-- Deduplication preserves the full item invariant. -/
theorem dedupItems_inv {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem}
    (hinv : ItemsInv p init st items) :
    ItemsInv p init st (dedupItems items) where
  ent := Entailed_of_mem_subset hinv.ent
    (fun l hl => (dedupItems_lit_mem items l).mpr hl)
  explained := fun x hx =>
    hinv.explained x (Array.mem_toList_iff.mpr
      (dedupItems_mem (Array.mem_toList_iff.mp hx)))
  isFalse := fun x hx =>
    hinv.isFalse x (Array.mem_toList_iff.mpr
      (dedupItems_mem (Array.mem_toList_iff.mp hx)))

/-- Deduplicate only once the working set has grown past `budget`, and then
allow another 50% growth before rebuilding.  A full hash-set rebuild at
every resolution step costs more than the rescans it saves; amortizing it
keeps the duplicate excess bounded while paying for the rebuild roughly
once per `0.5 * size / new-items` steps. -/
def dedupWithBudget (items : Array CItem) (budget : Nat) :
    Array CItem × Nat :=
  if items.size ≤ budget then (items, budget)
  else
    let d := dedupItems items
    (d, d.size + d.size / 2 + 16)

/-- The budgeted deduplication preserves the item invariant. -/
theorem dedupWithBudget_inv {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {items : Array CItem}
    {budget : Nat} (hinv : ItemsInv p init st items) :
    ItemsInv p init st (dedupWithBudget items budget).1 := by
  unfold dedupWithBudget
  split
  · exact hinv
  · exact dedupItems_inv hinv

/-- Initial duplicate budget after the mandatory first deduplication. -/
def initialBudget (items : Array CItem) : Nat :=
  let d := dedupItems items
  d.size + d.size / 2 + 16

/-! ## Initial conflict items -/

/-- Both the explanation certificate and current falsity of an item. -/
def itemOKB (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (it : CItem) : Bool :=
  itemCheckB p init st it && domFalseB st it.lit

theorem itemOKB_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (h : itemOKB p init st it = true) :
    ItemFalse st it := by
  unfold itemOKB at h
  rw [Bool.and_eq_true] at h
  exact domFalseB_spec h.2

theorem itemOKB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {it : CItem} (hconv : InitConv p init)
    (hhist : SlotHistory init st)
    (h : itemOKB p init st it = true) :
    ItemExplained p init st it ∧ ItemFalse st it := by
  unfold itemOKB at h
  rw [Bool.and_eq_true] at h
  exact ⟨itemCheckB_spec hconv hhist h.1, domFalseB_spec h.2⟩

/-- Explain every literal of the initial conflict clause.  Any missing or
unchecked explanation aborts the analysis (`none`). -/
def initialItems (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) : List PLit → Option (Array CItem)
  | [] => some #[]
  | q :: qs =>
      match explainLitFast init st q.lit with
      | none => none
      | some it =>
          if itemOKB p init st { it with pidx := some q.idx } then
            match initialItems p init st qs with
            | none => none
            | some items => some (addCItem items { it with pidx := some q.idx })
          else none

theorem initialItems_lit_mem {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List PLit} {items : Array CItem}
    (h : initialItems p init st ls = some items) :
    ∀ q ∈ ls, q.lit ∈ items.toList.map (fun it => it.lit) := by
  induction ls generalizing items with
  | nil => intro q hq; simp at hq
  | cons a rest ih =>
      unfold initialItems at h
      split at h
      · simp at h
      · rename_i it hit
        by_cases hcheck : itemOKB p init st { it with pidx := some a.idx } = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact addCItem_mem_lit_iff.mpr (Or.inr (by
                  simpa using (explainLitFast_lit hit).symm))
              · exact addCItem_mem_lit_iff.mpr (Or.inl (ih hrec q hq))
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List PLit} {items : Array CItem}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
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
        by_cases hcheck : itemOKB p init st { it with pidx := some a.idx } = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              exact addCItem_explained (ih hrec)
                (itemOKB_spec hconv hhist hcheck).1
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List PLit} {items : Array CItem}
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
        by_cases hcheck : itemOKB p init st { it with pidx := some a.idx } = true
        · rw [if_pos hcheck] at h
          cases hrec : initialItems p init st rest with
          | none => simp [hrec] at h
          | some items' =>
              simp [hrec] at h
              subst h
              exact addCItem_false (ih hrec) (itemOKB_false hcheck)
        · rw [if_neg hcheck] at h
          simp at h

theorem initialItems_entailed {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List PLit} {items : Array CItem}
    (hconf : Entailed p (ls.map PLit.decode))
    (h : initialItems p init st ls = some items) :
    Entailed p (items.toList.map (fun it => it.lit)) := by
  refine Entailed_of_mem_subset hconf ?_
  intro l hl
  rcases List.mem_map.mp hl with ⟨q, hq, rfl⟩
  exact initialItems_lit_mem h q hq

theorem initialItems_inv {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {ls : List PLit} {items : Array CItem}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hconf : Entailed p (ls.map PLit.decode)) (h : initialItems p init st ls = some items) :
    ItemsInv p init st items where
  ent := initialItems_entailed hconf h
  explained := initialItems_explained hconv hhist h
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

/-- One combined pass over a change list: entry existence and ownership,
literal slot, and kind compatibility.  A dangling position fails the check. -/
def slotEntryOKB (init : Array DomC) (st : EngineState p T) (s : Nat)
    (p : Nat) : Bool :=
  match st.trail[p]? with
  | some e =>
      (e.slot == s) && (atomSlot e.lit.lit.atom == s) &&
        atomKindOKB (init.getD s DomC.empty) e.lit.lit.atom
  | none => false

def entriesOKB (init : Array DomC) (st : EngineState p T) (s : Nat) : Bool :=
  (st.changeList s).all (slotEntryOKB init st s)

theorem entriesOKB_spec {init : Array DomC} {st : EngineState p T} {s : Nat}
    (h : entriesOKB init st s = true) :
    (∀ q ∈ st.changeList s, ∃ e, st.trail[q]? = some e ∧ e.slot = s) ∧
    (∀ q ∈ st.changeList s, ∀ e, st.trail[q]? = some e →
      atomSlot e.lit.lit.atom = s) ∧
    (∀ q ∈ st.changeList s, ∀ e, st.trail[q]? = some e → ∀ v,
      (init.getD s DomC.empty).mem v = true → e.lit.lit.atom.evalAtValue v ≠ none) := by
  have hall : ∀ q ∈ st.changeList s, slotEntryOKB init st s q = true := by
    intro q hq
    exact (Array.all_eq_true'.mp h) q (by simpa using (Array.mem_toList_iff.mpr hq))
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hq' := hall q hq
    unfold slotEntryOKB at hq'
    cases ht : st.trail[q]? with
    | none => simp [ht] at hq'
    | some e =>
        refine ⟨e, rfl, ?_⟩
        simp only [ht, Bool.and_eq_true] at hq'
        exact beq_iff_eq.mp hq'.1.1
  · intro q hq e he
    have hq' := hall q hq
    unfold slotEntryOKB at hq'
    rw [he] at hq'
    simp only [Bool.and_eq_true] at hq'
    exact beq_iff_eq.mp hq'.1.2
  · intro q hq e he v hv
    have hq' := hall q hq
    unfold slotEntryOKB at hq'
    rw [he] at hq'
    simp only [Bool.and_eq_true] at hq'
    exact atomKindOKB_spec hq'.2 hv

/-- All runtime facts needed by `chainReasonLits_entailed`. -/
def chainCertCheckB (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (s : Nat) : Bool :=
  initSlotRangeB p s && sortedB (st.changeList s) && entriesOKB init st s

theorem chainCertCheckB_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {s : Nat} (hconv : InitConv p init)
    (h : chainCertCheckB p init st s = true) :
    ChainCert p init st s := by
  unfold chainCertCheckB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h2, hentries⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h1, hsorted⟩ := h2
  have hslot := initSlotRangeB_spec h1
  obtain ⟨hent, hlit, hkind⟩ := entriesOKB_spec hentries
  exact
    { slot_lt := hslot
      conv := hconv.conv s hslot
      sorted := sortedB_spec hsorted
      entries := hent
      lit_slot := hlit
      kind := hkind }

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
    List PLit → Except String (Array CItem)
  | [] => .ok acc
  | q :: qs =>
      if litEqB q.lit b.negate then addReasonLits p init st b acc qs
      else
        match explainLitFast init st q.lit with
        | none => .error s!"no explanation for {repr q.lit}"
        | some ni =>
            if itemOKB p init st { ni with pidx := some q.idx } then
              addReasonLits p init st b
                (addCItem acc { ni with pidx := some q.idx }) qs
            else .error s!"unchecked item for {repr q.lit}"


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
    ∀ (ls : List PLit) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      out.toList.map (fun it => it.lit) =
        acc.toList.map (fun it => it.lit) ++
          (ls.map (fun q => q.lit)).filter (fun q => !litEqB q b.negate)
  | [], acc, out, h => by
      simp [addReasonLits] at h
      subst h
      simp
  | q :: qs, acc, out, h => by
      unfold addReasonLits at h
      by_cases hq : litEqB q.lit b.negate = true
      · rw [if_pos hq] at h
        rw [addReasonLits_lits_eq qs acc out h]
        simp [hq]
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st { ni with pidx := some q.idx } = true
          · rw [if_pos hcheck] at h
            have hlit : ni.lit = q.lit := explainLitFast_lit hni
            rw [addReasonLits_lits_eq qs (addCItem acc { ni with pidx := some q.idx }) out h]
            simp [addCItem, hlit, hq]
          · rw [if_neg hcheck] at h
            simp at h

/-- Every clause carried by an `EClause` is entailed at the literal level. -/
theorem eClause_entailed_lits {p : CompiledProblem DomConstraint} {T : LitTable}
    (c : EClause p T) :
    Entailed p (c.lits.toList.map (fun q => q.lit)) := by
  simpa [LitTable.decodeClause, LitTable.decode, PLit.decode] using c.ent

/-- The packed clause of an `EClause`, read at the decoded-literal level. -/
theorem EClause.ent_toList {p : CompiledProblem DomConstraint} {T : LitTable}
    (c : EClause p T) : Entailed p (c.lits.toList.map PLit.decode) := by
  change Entailed p (c.lits.toList.map (fun q => q.lit))
  simpa [LitTable.decodeClause, LitTable.decode] using c.ent

/-- `addReasonLits` preserves the explanation invariant. -/
theorem addReasonLits_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} (hconv : InitConv p init)
    (hhist : SlotHistory init st) :
    ∀ (ls : List PLit) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      (∀ x, x ∈ acc.toList → ItemExplained p init st x) →
      ∀ x, x ∈ out.toList → ItemExplained p init st x
  | [], acc, out, h, hacc => by
      simp [addReasonLits] at h
      subst h
      exact hacc
  | q :: qs, acc, out, h, hacc => by
      unfold addReasonLits at h
      by_cases hq : litEqB q.lit b.negate = true
      · rw [if_pos hq] at h
        exact addReasonLits_explained hconv hhist qs acc out h hacc
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st { ni with pidx := some q.idx } = true
          · rw [if_pos hcheck] at h
            exact addReasonLits_explained hconv hhist qs
              (addCItem acc { ni with pidx := some q.idx }) out h
              (addCItem_explained hacc (itemOKB_spec hconv hhist hcheck).1)
          · rw [if_neg hcheck] at h
            simp at h

/-- `addReasonLits` preserves current falsity. -/
theorem addReasonLits_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} :
    ∀ (ls : List PLit) (acc out : Array CItem),
      addReasonLits p init st b acc ls = .ok out →
      (∀ x, x ∈ acc.toList → ItemFalse st x) →
      ∀ x, x ∈ out.toList → ItemFalse st x
  | [], acc, out, h, hacc => by
      simp [addReasonLits] at h
      subst h
      exact hacc
  | q :: qs, acc, out, h, hacc => by
      unfold addReasonLits at h
      by_cases hq : litEqB q.lit b.negate = true
      · rw [if_pos hq] at h
        exact addReasonLits_false qs acc out h hacc
      · rw [if_neg hq] at h
        split at h
        · simp at h
        · rename_i ni hni
          by_cases hcheck : itemOKB p init st { ni with pidx := some q.idx } = true
          · rw [if_pos hcheck] at h
            exact addReasonLits_false qs
              (addCItem acc { ni with pidx := some q.idx }) out h
              (addCItem_false hacc (itemOKB_false hcheck))
          · rw [if_neg hcheck] at h
            simp at h

/-- Intern-index hint for the negation of a packed literal, read from the
negation cache.  The cache is only a hint: canonicalisation revalidates the
index against the live table. -/
def negHint (T : LitTable) (l : PLit) : Option Nat :=
  match T.neg[l.idx]? with
  | some (j + 1) => some j
  | _ => none

/-- Hinted chain resolution: scan the slot's change list in order and
explain each entry's negated literal starting at that entry's own
change-list index.  Entry `i` makes `e.lit.lit.negate` false, so the hint
is the exact earliest index; the scan is constant-time instead of a fresh
scan from zero. -/
def addChainGo (p : CompiledProblem DomConstraint) (init : Array DomC)
    (st : EngineState p T) (b : Literal) (slot pos : Nat)
    (acc : Array CItem) : List Nat → Nat → Except String (Array CItem)
  | [], _ => .ok acc
  | p_i :: rest, i =>
      if p_i ≤ pos then
        match st.trail[p_i]? with
        | some e =>
            if litEqB e.lit.lit.negate b.negate then
              addChainGo p init st b slot pos acc rest (i + 1)
            else
              match explainLitFrom init st e.lit.lit.negate i with
              | none => .error s!"no explanation for {repr e.lit.lit.negate}"
              | some ni =>
                  if itemOKB p init st { ni with pidx := negHint st.table e.lit } then
                    addChainGo p init st b slot pos
                      (addCItem acc { ni with pidx := negHint st.table e.lit }) rest (i + 1)
                  else .error s!"unchecked item for {repr e.lit.lit.negate}"
        | none => addChainGo p init st b slot pos acc rest (i + 1)
      else addChainGo p init st b slot pos acc rest (i + 1)

theorem addChainGo_lits_eq {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} {slot pos : Nat} :
    ∀ (ls : List Nat) (i : Nat) (acc out : Array CItem),
      addChainGo p init st b slot pos acc ls i = .ok out →
      out.toList.map (fun it => it.lit) =
        acc.toList.map (fun it => it.lit) ++
          (ls.filterMap (chainReasonAt st pos)).filter (fun q => !litEqB q b.negate)
  | [], i, acc, out, h => by
      simp [addChainGo] at h
      subst h
      simp
  | p_i :: rest, i, acc, out, h => by
      unfold addChainGo at h
      by_cases hp : p_i ≤ pos
      · rw [if_pos hp] at h
        split at h
        · rename_i e htr
          by_cases hq : litEqB e.lit.lit.negate b.negate = true
          · rw [if_pos hq] at h
            rw [addChainGo_lits_eq rest (i + 1) acc out h]
            simp [chainReasonAt, hp, htr, hq]
          · rw [if_neg hq] at h
            split at h
            · simp at h
            · rename_i ni hni
              by_cases hcheck : itemOKB p init st { ni with pidx := negHint st.table e.lit } = true
              · rw [if_pos hcheck] at h
                have hlit : ni.lit = e.lit.lit.negate := explainLitFrom_lit hni
                rw [addChainGo_lits_eq rest (i + 1) (addCItem acc { ni with pidx := negHint st.table e.lit }) out h]
                simp [chainReasonAt, hp, htr, hq, addCItem, hlit]
              · rw [if_neg hcheck] at h
                simp at h
        · rename_i htr
          rw [addChainGo_lits_eq rest (i + 1) acc out h]
          simp [chainReasonAt, hp, htr]
      · rw [if_neg hp] at h
        rw [addChainGo_lits_eq rest (i + 1) acc out h]
        simp [chainReasonAt, hp]

theorem addChainGo_explained {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} {slot pos : Nat}
    (hconv : InitConv p init) (hhist : SlotHistory init st) :
    ∀ (ls : List Nat) (i : Nat) (acc out : Array CItem),
      addChainGo p init st b slot pos acc ls i = .ok out →
      (∀ x, x ∈ acc.toList → ItemExplained p init st x) →
      ∀ x, x ∈ out.toList → ItemExplained p init st x
  | [], i, acc, out, h, hacc => by
      simp [addChainGo] at h
      subst h
      exact hacc
  | p_i :: rest, i, acc, out, h, hacc => by
      unfold addChainGo at h
      by_cases hp : p_i ≤ pos
      · rw [if_pos hp] at h
        split at h
        · rename_i e htr
          by_cases hq : litEqB e.lit.lit.negate b.negate = true
          · rw [if_pos hq] at h
            exact addChainGo_explained hconv hhist rest (i + 1) acc out h hacc
          · rw [if_neg hq] at h
            split at h
            · simp at h
            · rename_i ni hni
              by_cases hcheck : itemOKB p init st { ni with pidx := negHint st.table e.lit } = true
              · rw [if_pos hcheck] at h
                exact addChainGo_explained hconv hhist rest (i + 1) (addCItem acc { ni with pidx := negHint st.table e.lit }) out h
                  (addCItem_explained hacc (itemOKB_spec hconv hhist hcheck).1)
              · rw [if_neg hcheck] at h
                simp at h
        · rename_i htr
          exact addChainGo_explained hconv hhist rest (i + 1) acc out h hacc
      · rw [if_neg hp] at h
        exact addChainGo_explained hconv hhist rest (i + 1) acc out h hacc

theorem addChainGo_false {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {b : Literal} {slot pos : Nat} :
    ∀ (ls : List Nat) (i : Nat) (acc out : Array CItem),
      addChainGo p init st b slot pos acc ls i = .ok out →
      (∀ x, x ∈ acc.toList → ItemFalse st x) →
      ∀ x, x ∈ out.toList → ItemFalse st x
  | [], i, acc, out, h, hacc => by
      simp [addChainGo] at h
      subst h
      exact hacc
  | p_i :: rest, i, acc, out, h, hacc => by
      unfold addChainGo at h
      by_cases hp : p_i ≤ pos
      · rw [if_pos hp] at h
        split at h
        · rename_i e htr
          by_cases hq : litEqB e.lit.lit.negate b.negate = true
          · rw [if_pos hq] at h
            exact addChainGo_false rest (i + 1) acc out h hacc
          · rw [if_neg hq] at h
            split at h
            · simp at h
            · rename_i ni hni
              by_cases hcheck : itemOKB p init st { ni with pidx := negHint st.table e.lit } = true
              · rw [if_pos hcheck] at h
                exact addChainGo_false rest (i + 1) (addCItem acc { ni with pidx := negHint st.table e.lit }) out h
                  (addCItem_false hacc (itemOKB_false hcheck))
              · rw [if_neg hcheck] at h
                simp at h
        · rename_i htr
          exact addChainGo_false rest (i + 1) acc out h hacc
      · rw [if_neg hp] at h
        exact addChainGo_false rest (i + 1) acc out h hacc

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
      addReasonLits p init st b (removeLitItems items b) c.lits.toList
  | none =>
      if chainCertCheckB p init st (atomSlot b.atom) then
        addChainGo p init st b (atomSlot b.atom) pos (removeLitItems items b)
          (st.changeList (atomSlot b.atom)).toList 0
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
        rw [addChainGo_lits_eq _ _ _ _ h, chainReasonLits_filter]
        rfl
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
    (hconv : InitConv p init)
    (h : resolveWith p init st items i b pos rc = .ok items')
    (hn : exactReason b rc = none) :
    ChainCert p init st (atomSlot b.atom) := by
  unfold resolveWith at h
  simp only [hn] at h
  by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
  · exact chainCertCheckB_spec hconv hcheck
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
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (h : resolveWith p init st items i b pos rc = .ok items')
    (hacc : ∀ x, x ∈ (removeLitItems items b).toList →
      ItemExplained p init st x) :
    ∀ x, x ∈ items'.toList → ItemExplained p init st x := by
  unfold resolveWith at h
  cases hex : exactReason b rc with
  | some c =>
      simp only [hex] at h
      exact addReasonLits_explained hconv hhist _ _ _ h hacc
  | none =>
      simp only [hex] at h
      by_cases hcheck : chainCertCheckB p init st (atomSlot b.atom) = true
      · rw [if_pos hcheck] at h
        exact addChainGo_explained hconv hhist _ _ _ _ h hacc
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
        exact addChainGo_false _ _ _ _ h hacc
      · rw [if_neg hcheck] at h
        simp at h

/-- **B3.**  A successful resolution step preserves the full item
invariant.  The caller supplies the chain entailment (B2) on the exact-miss
branch, which is the only branch that uses the chain clause. -/
theorem resolveWith_inv {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} {items : Array CItem} {i : Nat} {b : Literal}
    {pos : Nat} {rc : Option (EClause p T)} {items' : Array CItem}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hinv : ItemsInv p init st items)
    (hbmem : b ∈ items.toList.map (fun it => it.lit))
    (hresolve : resolveWith p init st items i b pos rc = .ok items')
    (hchain : exactReason b rc = none →
      Entailed p (chainReasonLits st (atomSlot b.atom) pos b).toList) :
    ItemsInv p init st items' where
  ent := resolveWith_entailed hinv.ent hbmem hresolve
    (fun c _ => eClause_entailed_lits c) hchain
  explained := resolveWith_explained hconv hhist hresolve (removeLitItems_explained hinv.explained)
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

/-- The empty compact domain contains no value. -/
theorem DomC.empty_mem_false (v : Value) : DomC.empty.mem v = false := by
  cases v with
  | int i =>
      simp only [DomC.empty, DomC.mem]
      by_cases h1 : 1 ≤ i
      · have h2 : ¬ i ≤ 0 := by omega
        simp [h1, h2]
      · simp [h1]
  | bool b => rfl
  | setOfInt s => rfl
  | array a => rfl

/-- A live domain containing a value is well-formed: an out-of-range slot
reads as `DomC.empty`, which contains nothing. -/
theorem dom_WF_of_mem {st : EngineState p T} (hWF : DomsWF st) {s : Nat} {v : Value}
    (hmem : (st.doms.getD s DomC.empty).mem v = true) :
    (st.doms.getD s DomC.empty).WF := by
  by_cases hs : s < st.doms.size
  · exact hWF s hs
  · have hd : st.doms.getD s DomC.empty = DomC.empty :=
      Array.getD_eq_default_of_size_le st.doms (Nat.le_of_not_lt hs) DomC.empty
    rw [hd, DomC.empty_mem_false] at hmem
    exact absurd hmem (by simp)

/-- A literal that is definitely false on the live root domains has an
entailed negation.  `RootDomInv` supplies the accepted value inside the
domain; the in-range slot hypothesis makes that value the slot's value in
the assignment. -/
theorem evalLit_false_entailed_neg {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {l : Literal} {s : Nat}
    (hdom : RootDomInv p init st) (hlev : st.level = 0) (hWF : DomsWF st)
    (hslot : s < p.domains.length) (hls : atomSlot l.atom = s)
    (hfalse : (st.doms.getD s DomC.empty).evalLit l = some false) :
    Entailed p [l.negate] := by
  intro b hb hacc
  obtain ⟨v, hbv, _⟩ := mem_allAssigns_getElem_mem hb hslot
  have hmem : (st.doms.getD s DomC.empty).mem v = true :=
    hdom hlev b hb hacc s hslot v hbv
  have hdWF : (st.doms.getD s DomC.empty).WF := dom_WF_of_mem hWF hmem
  have hfalsev : l.valueHolds v = false :=
    DomC.evalLit_false_sound _ l hdWF hfalse v hmem
  have hdef : l.atom.evalAtValue v ≠ none :=
    Atom.evalAtValue_ne_none_of_mem_evalLit_false hmem hfalse
  have havl : b[atomSlot l.negate.atom]? = some v := by
    rw [atomSlot_eq_slot]
    have hsl : l.negate.atom.slot = s := by
      rw [← atomSlot_eq_slot]
      simpa [Literal.negate] using hls
    rw [hsl]
    exact hbv
  refine ⟨l.negate, by simp, ?_⟩
  rw [Literal.eval_eq_valueHolds _ b havl]
  exact (Literal.valueHolds_negate_eq_true_iff l v hdef).mpr hfalsev

/-- A conflict item at the root level whose literal is still false on the
live domains has an entailed unit negation.  This is the fact R2 uses to
delete level-zero items from a learned clause. -/
theorem item_entailed_neg {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {it : CItem}
    (hdom : RootDomInv p init st) (hlev : st.level = 0) (hWF : DomsWF st)
    (hexp : ItemExplained p init st it) (hfalse : ItemFalse st it) :
    Entailed p [it.lit.negate] :=
  evalLit_false_entailed_neg hdom hlev hWF hexp.slot_lt rfl hfalse


/-! ## Semantic root facts -/

/-- A literal that is not true on any accepted assignment.  This is weaker
than `Entailed p [l.negate]`: it also covers out-of-range slots whose atom
has no value in any accepted assignment. -/
def NotTrueEntailed (p : CompiledProblem DomConstraint) (l : Literal) : Prop :=
  ∀ b ∈ allAssigns p.domains, accepts p b = true → l.eval b ≠ some true

/-- An entailed unit negation makes the literal not true. -/
theorem notTrueEntailed_of_entailed_neg {p : CompiledProblem DomConstraint}
    {l : Literal} (h : Entailed p [l.negate]) : NotTrueEntailed p l := by
  intro b hb hacc hev
  obtain ⟨x, hx, hxv⟩ := h b hb hacc
  simp only [List.mem_singleton] at hx
  subst hx
  rw [Literal.eval_negate, hev] at hxv
  simp at hxv

/-- If an entailed clause has all its non-`l` literals not true, then `l` is
entailed.  Membership of `l` in the clause is not required: the excluded
middle either produces the witness `l` or shows that no accepted assignment
exists. -/
theorem entailed_unit_of_notTrue {p : CompiledProblem DomConstraint}
    {c : Clause} {l : Literal}
    (h : Entailed p c) (hc : ∀ m ∈ c, m ≠ l → NotTrueEntailed p m) :
    Entailed p [l] := by
  intro b hb hacc
  obtain ⟨m, hm, hmv⟩ := h b hb hacc
  by_cases hml : m = l
  · subst hml
    exact ⟨m, by simp, hmv⟩
  · exact absurd hmv (hc m hm hml b hb hacc)

/-- If a clause is entailed and every non-head literal is entailed false,
then the head literal is entailed. -/
theorem entailed_unit_of_entailed_neg {p : CompiledProblem DomConstraint}
    {l : Literal} {ls : List Literal}
    (h : Entailed p (l :: ls))
    (hls : ∀ m ∈ ls, Entailed p [m.negate]) :
    Entailed p [l] := by
  refine entailed_unit_of_notTrue h ?_
  intro m hm hne
  rcases List.mem_cons.mp hm with rfl | hm
  · exact absurd rfl hne
  · exact notTrueEntailed_of_entailed_neg (hls m hm)

/-! ## The root trail invariant -/

/-- Every level-zero trail entry is a unit consequence of the problem and
lives on its own atom's slot.  Slot coherence is needed by the replay: a
change listed for slot `s` is an entry whose literal is read from slot `s`. -/
def RootTrail (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) : Prop :=
  ∀ (i : Nat) (e : Entry), st.trail[i]? = some e → e.level = 0 →
    Entailed p [e.lit.lit] ∧ e.slot = e.lit.lit.atom.slot

/-- Membership in `allAssigns` fixes the assignment length. -/
theorem allAssigns_length_eq {ds : List Domain} {a : Assignment}
    (ha : a ∈ allAssigns ds) : a.length = ds.length :=
  (allAssigns_fits ds a ha).1

/-! ## Level monotonicity along the trail -/

/-- Trail entries are pushed at the current decision level and the trail is
only ever truncated from the right, so decision levels never decrease along
trail positions.  R2 needs this to replay the level-zero prefix of a slot's
change list while the search sits above level zero. -/
def LevelMono (st : EngineState p T) : Prop :=
  ∀ (i j : Nat) (e1 e2 : Entry), st.trail[i]? = some e1 →
    st.trail[j]? = some e2 → i ≤ j → e1.level ≤ e2.level

/-- Replaying a prefix of the change list starting from the converted initial
domain never loses the value of an accepted root assignment.  The caller
supplies the level-zero fact for every entry that the replay touches;
`RootTrail` then turns each applied literal into a unit consequence. -/
theorem domAfter_mem_of_prefix {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T}
    (hTI : TrailInv st) (hroot : RootTrail p T st) (hconv : InitConv p init)
    {b : Assignment} (hb : b ∈ allAssigns p.domains) (hacc : accepts p b = true)
    {s : Nat} (hsl : s < p.domains.length) :
    ∀ {m : Nat}, m ≤ (st.changeList s).size →
      (∀ k, k < m → ∀ e,
        st.trail[(st.changeList s).getD k 0]? = some e → e.level = 0) →
      ∀ {v : Value}, b[s]? = some v → (domAfter init st s m).mem v = true := by
  intro m
  induction m with
  | zero =>
      intro _ _ v hbv
      rw [domAfter_zero]
      obtain ⟨v0, hb0, hv0⟩ := mem_allAssigns_getElem_mem hb hsl
      have hveq : v0 = v := by
        rw [hbv] at hb0
        exact (Option.some.inj hb0).symm
      rw [← hveq]
      rw [DomC.mem_iff (p.domains.getD s Dom.empty) (init.getD s DomC.empty)
        (hconv.conv s hsl) v0]
      exact hv0
  | succ m ih =>
      intro hm hpre v hbv
      have hk : m < (st.changeList s).size := by omega
      rw [domAfter_succ (init := init) (st := st) (s := s) (k := m) hk]
      have hmem : (st.changeList s).getD m 0 ∈ st.changeList s :=
        Array.getD_mem hk
      obtain ⟨_, e, he, hesl⟩ :=
        (hTI.changeIndex_mem s ((st.changeList s).getD m 0)).1 hmem
      have hih : (domAfter init st s m).mem v = true :=
        ih (by omega) (fun k hk' e' he' => hpre k (by omega) e' he') hbv
      have hinitWF : (init.getD s DomC.empty).WF :=
        DomC.ofDom?_wf _ _ (hconv.conv s hsl)
      have hdWF : (domAfter init st s m).WF :=
        domAfter_WF (init := init) (st := st) (s := s) (k := m) hinitWF
      simp only [domStep]
      rw [he]
      rw [DomC.mem_applyLit _ _ hdWF v]
      refine ⟨hih, ?_⟩
      have hele : e.level = 0 := hpre m (by omega) e he
      obtain ⟨hent, hslot⟩ := hroot ((st.changeList s).getD m 0) e he hele
      obtain ⟨x, hx, hxv⟩ := hent b hb hacc
      simp only [List.mem_singleton] at hx
      subst hx
      have hb_atom : b[e.lit.lit.atom.slot]? = some v := by
        rw [← hslot, hesl]
        exact hbv
      rw [Literal.eval_eq_valueHolds _ b hb_atom] at hxv
      exact hxv

/-! ## Entailed unit negations for level-zero items -/

/-- For an item explained by a real trail entry, the change-list indices
below `cidx` name trail positions strictly before the item's entry, and
level monotonicity makes every such entry level zero. -/
theorem prefix_levels_of_item {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {it : CItem} {e : Entry}
    (hTI : TrailInv st) (hmono : LevelMono st)
    (hexp : ItemExplained p init st it)
    (he : st.trail[it.pos]? = some e) (hlev : it.level = 0) :
    ∀ k, k < it.cidx → ∀ e',
      st.trail[(st.changeList (atomSlot it.lit.atom)).getD k 0]? = some e' →
      e'.level = 0 := by
  intro k hk e' he'
  rcases hexp.expl with hsent | hentry
  · obtain ⟨hpos, _, _⟩ := hsent
    exact absurd hpos (by
      have := (Array.getElem?_eq_some_iff.mp he).1
      omega)
  · obtain ⟨e0, he0, hele, _, hcidx, _, _⟩ := hentry
    have hcidx_lt : it.cidx < (st.changeList (atomSlot it.lit.atom)).size :=
      (Array.getElem?_eq_some_iff.mp hcidx).1
    have hcidx_val : (st.changeList (atomSlot it.lit.atom)).getD it.cidx 0 = it.pos := by
      rw [Array.getD_eq_getElem?_getD, hcidx, Option.getD_some]
    have hlt : (st.changeList (atomSlot it.lit.atom)).getD k 0 < it.pos := by
      rw [← hcidx_val]
      exact SortedList.getD_lt (hTI.changeIndex_sorted (atomSlot it.lit.atom)) hk hcidx_lt
    have hle := hmono _ _ e' e0 he' he0 (Nat.le_of_lt hlt)
    omega

/-- A level-zero conflict item has an entailed unit negation, at any current
decision level.  The sentinel branch is initial-domain falsity; the entry
branch replays the level-zero prefix of the slot's change list and uses the
entailed literal of the explaining entry. -/
theorem item_entailed_neg_of_level0 {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {it : CItem}
    (hTI : TrailInv st) (hmono : LevelMono st)
    (hroot : RootTrail p T st) (hconv : InitConv p init)
    (hexp : ItemExplained p init st it) (hlev : it.level = 0) :
    Entailed p [it.lit.negate] := by
  rcases hexp.expl with hsent | hentry
  · obtain ⟨_, _, hfalse⟩ := hsent
    exact initialDomain_neg_entailed hexp.slot_lt hexp.conv rfl hfalse
  · obtain ⟨e, he, hele, hslot, hcidx, hprev, hfalseapp⟩ := hentry
    intro b hb hacc
    obtain ⟨v, hbv, _⟩ := mem_allAssigns_getElem_mem hb hexp.slot_lt
    have hcidx_lt : it.cidx < (st.changeList (atomSlot it.lit.atom)).size :=
      (Array.getElem?_eq_some_iff.mp hcidx).1
    have hmemprev : e.prev.mem v = true := by
      rw [hprev]
      exact domAfter_mem_of_prefix hTI hroot hconv hb hacc hexp.slot_lt
        (m := it.cidx) (by omega)
        (prefix_levels_of_item hTI hmono hexp he hlev) hbv
    have hele0 : e.level = 0 := by omega
    obtain ⟨hent, hslotE⟩ := hroot it.pos e he hele0
    obtain ⟨x, hx, hxv⟩ := hent b hb hacc
    simp only [List.mem_singleton] at hx
    subst hx
    have hb_atom : b[e.lit.lit.atom.slot]? = some v := by
      rw [← hslotE, hslot]
      exact hbv
    rw [Literal.eval_eq_valueHolds _ b hb_atom] at hxv
    have hinitWF : (init.getD (atomSlot it.lit.atom) DomC.empty).WF :=
      DomC.ofDom?_wf _ _ hexp.conv
    have hWFprev : e.prev.WF := by
      rw [hprev]
      exact domAfter_WF (init := init) (st := st) (s := atomSlot it.lit.atom)
        (k := it.cidx) hinitWF
    have hWFapp : (e.prev.applyLit e.lit.lit).WF :=
      DomC.applyLit_WF _ e.lit.lit hWFprev
    have hmemapp : (e.prev.applyLit e.lit.lit).mem v = true := by
      rw [DomC.mem_applyLit _ _ hWFprev v]
      exact ⟨hmemprev, hxv⟩
    have hfalsev : it.lit.valueHolds v = false :=
      DomC.evalLit_false_sound _ it.lit hWFapp hfalseapp v hmemapp
    have hdef : it.lit.atom.evalAtValue v ≠ none :=
      Atom.evalAtValue_ne_none_of_mem_evalLit_false hmemapp hfalseapp
    refine ⟨it.lit.negate, by simp, ?_⟩
    have hbneg : b[atomSlot it.lit.negate.atom]? = some v := by
      simpa [Literal.negate] using hbv
    rw [Literal.eval_eq_valueHolds _ b hbneg]
    exact (Literal.valueHolds_negate_eq_true_iff it.lit v hdef).mpr hfalsev

/-! ## The root invariant bundle -/

/-- Everything conflict analysis needs to turn a level-zero item into an
entailed unit negation.  `conv` is state-independent; `trail_inv`,
`level_mono` and `root` are the engine invariants threaded through search.
Proof-only: no runtime field is read. -/
structure RootInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) : Prop where
  /-- Slot-domain history and trail validity. -/
  hist : HistInv init st
  /-- The initial domains are exactly the converted compiled domains. -/
  init_inv : InitInv p init
  /-- The live intern table is well formed, including its negation cache. -/
  table_inv : st.table.Inv
  /-- Every literal stored in a clause is interned in the live table. -/
  lits_wf : st.db.LitsWF st.table
  /-- Decision levels never decrease along the trail. -/
  level_mono : LevelMono st
  /-- Every level-zero trail entry is a unit consequence. -/
  root : RootTrail p T st
  /-- The initial-domain conversion bridge for accepted assignments. -/
  conv : InitConv p init
  /-- The clause database structural invariant, needed to turn watched-clause
  propagations into entailed units. -/
  db_inv : st.db.Inv

/-- A level-zero item of an analysis whose state satisfies `RootInv` has an
entailed unit negation. -/
theorem RootInv.item_unit {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T} {it : CItem}
    (hinv : RootInv p T init st) (hexp : ItemExplained p init st it)
    (hlev : it.level = 0) : Entailed p [it.lit.negate] :=
  _root_.LeanFzn.Engine.item_entailed_neg_of_level0 hinv.hist.2 hinv.level_mono
    hinv.root hinv.conv hexp hlev

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

/-- Every literal of `finishOrder` comes from an item. -/
theorem finishOrder_mem {items : Array CItem} {assertIdx : Option Nat} {l : Literal}
    (h : l ∈ (finishOrder items assertIdx).toList) :
    ∃ it ∈ items.toList, it.lit = l := by
  have hp := (List.Perm.mem_iff (finishOrder_perm items assertIdx)).mp h
  exact List.mem_map.mp hp

/-- The kept items of the final learned clause: the asserting item (when
present) first, then every item at a non-zero decision level.  Level-zero
items are erased by R2; duplicates of the asserting literal are redundant and
are erased with them. -/
def finishItems (items : Array CItem) (assertIdx : Option Nat) : Array CItem :=
  match assertIdx with
  | some i =>
      match items[i]? with
      | some it =>
          #[it] ++ (items.filter (fun x => !litEqB x.lit it.lit)).filter
            (fun x => x.level != 0)
      | none => items.filter (fun x => x.level != 0)
  | none => items.filter (fun x => x.level != 0)

/-- The asserting item is always kept. -/
theorem mem_finishItems_of_getElem? {items : Array CItem} {i : Nat} {it : CItem}
    (hget : items[i]? = some it) :
    it ∈ (finishItems items (some i)).toList := by
  rw [finishItems, hget]
  simp

/-- Every kept item comes from the original item set. -/
theorem finishItems_mem {items : Array CItem} {assertIdx : Option Nat} {x : CItem}
    (h : x ∈ (finishItems items assertIdx).toList) : x ∈ items.toList := by
  cases assertIdx with
  | none =>
      simp only [finishItems, Array.toList_filter] at h
      exact (List.mem_filter.mp h).1
  | some i =>
      cases hget : items[i]? with
      | none =>
          simp only [finishItems, hget, Array.toList_filter] at h
          exact (List.mem_filter.mp h).1
      | some it =>
          simp only [finishItems, hget, Array.toList_append] at h
          rcases List.mem_append.mp h with h | h
          · have hx : x = it := by simpa using h
            subst hx
            obtain ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp hget
            rw [← hval]
            exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
          · rw [Array.toList_filter, Array.toList_filter] at h
            exact (List.mem_filter.mp (List.mem_filter.mp h).1).1

/-- If the asserting-backjump fold reaches zero, every item that is not
syntactically equal to the asserting literal sits at level zero. -/
theorem foldl_backjump_eq_zero {l : List CItem} {ai : Literal} {acc : Nat}
    (h : l.foldl (fun acc (it : CItem) =>
      if litEqB it.lit ai then acc
      else if acc < it.level then it.level else acc) acc = 0) :
    acc = 0 ∧ ∀ it ∈ l, litEqB it.lit ai = true ∨ it.level = 0 := by
  induction l generalizing acc with
  | nil => exact ⟨h, by simp⟩
  | cons a t ih =>
      rw [List.foldl_cons] at h
      have hle : acc ≤ (if litEqB a.lit ai then acc
          else if acc < a.level then a.level else acc) := by
        by_cases hlit : litEqB a.lit ai = true
        · simp [hlit]
        · simp only [hlit, Bool.false_eq_true, if_false]
          split <;> omega
      obtain ⟨h0, hrest⟩ := ih h
      have hacc0 : acc = 0 := by omega
      refine ⟨hacc0, ?_⟩
      intro it hit
      rcases List.mem_cons.mp hit with heq | hit
      · subst heq
        by_cases hlit : litEqB it.lit ai = true
        · exact Or.inl hlit
        · right
          simp only [hlit, Bool.false_eq_true, if_false] at h0
          rw [hacc0] at h0
          split at h0 <;> omega
      · exact hrest it hit

/-- An asserting-fold whose items are all the asserting literal or at level
zero stays at zero. -/
theorem foldl_backjump_zero_of_lits {l : List CItem} {ai : Literal}
    (h : ∀ it ∈ l, litEqB it.lit ai = true ∨ it.level = 0) :
    l.foldl (fun acc (it : CItem) =>
      if litEqB it.lit ai then acc
      else if acc < it.level then it.level else acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.foldl_cons]
      have ha := h a (by simp)
      have hstep : (if litEqB a.lit ai then 0
          else if 0 < a.level then a.level else 0) = 0 := by
        rcases ha with hh | hh <;> simp [hh]
      rw [hstep]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A zero backjump means `finishItems` keeps only the asserting item. -/
theorem finishItems_eq_singleton_of_backjump_zero {items : Array CItem}
    {i : Nat} {it : CItem} (hget : items[i]? = some it)
    (hbj : items.foldl (fun acc (x : CItem) =>
      if litEqB x.lit it.lit then acc
      else if acc < x.level then x.level else acc) 0 = 0) :
    finishItems items (some i) = #[it] := by
  rw [finishItems, hget]
  have hnil : (items.filter (fun x => !litEqB x.lit it.lit)).filter
      (fun x => x.level != 0) = #[] := by
    rw [Array.eq_empty_iff_forall_not_mem]
    intro x hx
    have hx' := (Array.mem_toList_iff).mpr hx
    rw [Array.toList_filter, Array.toList_filter] at hx'
    obtain ⟨hx1, hxlev⟩ := List.mem_filter.mp hx'
    obtain ⟨hxmem, hxlit⟩ := List.mem_filter.mp hx1
    rw [← Array.foldl_toList] at hbj
    obtain ⟨-, hall⟩ :=
      foldl_backjump_eq_zero (l := items.toList) (ai := it.lit) (acc := 0) hbj
    rcases hall x hxmem with hh | hh
    · have hfalse : (!litEqB x.lit it.lit) = false := by rw [hh]; simp
      rw [hfalse] at hxlit
      cases hxlit
    · have hfalse : (x.level != 0) = false := by simp [hh]
      rw [hfalse] at hxlev
      cases hxlev
  simp [hnil]

/-- Erasing the level-zero items preserves entailment: every erased item's
negation is entailed, so the erased literal is never true on an accepted
assignment and is not the witness of the original clause. -/
theorem finishItems_entailed {p : CompiledProblem DomConstraint}
    {items : Array CItem}
    (h : Entailed p (items.toList.map (fun it => it.lit)))
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (assertIdx : Option Nat) :
    Entailed p ((finishItems items assertIdx).toList.map (fun it => it.lit)) := by
  intro b hb hacc
  obtain ⟨m, hm, hmv⟩ := h b hb hacc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
  have hnot : x.level = 0 → False := by
    intro h0
    exact notTrueEntailed_of_entailed_neg (hunit x hx h0) b hb hacc hmv
  cases assertIdx with
  | none =>
      have hlevel : x.level ≠ 0 := fun h0 => hnot h0
      refine ⟨x.lit, ?_, hmv⟩
      rw [List.mem_map]
      refine ⟨x, ?_, rfl⟩
      rw [finishItems, Array.toList_filter]
      exact List.mem_filter.mpr ⟨hx, by simpa using hlevel⟩
  | some i =>
      cases hget : items[i]? with
      | none =>
          have hlevel : x.level ≠ 0 := fun h0 => hnot h0
          refine ⟨x.lit, ?_, hmv⟩
          rw [List.mem_map]
          refine ⟨x, ?_, rfl⟩
          rw [finishItems, hget, Array.toList_filter]
          exact List.mem_filter.mpr ⟨hx, by simpa using hlevel⟩
      | some it =>
          by_cases heq : litEqB x.lit it.lit = true
          · have hxl : x.lit = it.lit := by simpa [litEqB] using heq
            refine ⟨it.lit, ?_, ?_⟩
            · rw [List.mem_map]
              exact ⟨it, mem_finishItems_of_getElem? hget, rfl⟩
            · rw [← hxl]
              exact hmv
          · have hlevel : x.level ≠ 0 := fun h0 => hnot h0
            have hkeep : (!litEqB x.lit it.lit) = true := by simpa using heq
            refine ⟨x.lit, ?_, hmv⟩
            rw [List.mem_map]
            refine ⟨x, ?_, rfl⟩
            rw [finishItems, hget, Array.toList_append]
            refine List.mem_append.mpr (Or.inr ?_)
            rw [Array.toList_filter, Array.toList_filter]
            exact List.mem_filter.mpr
              ⟨List.mem_filter.mpr ⟨hx, hkeep⟩, by simpa using hlevel⟩

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

/-- One-pass current-level scan: the newest candidate (largest trail
position), the first candidate, and whether every candidate has the same
literal.  The first-UIP stop needs exactly the last two facts, so this
replaces the separate `maxCurrentIdx` and `uniqueCurrentLit` scans. -/
structure CurScan where
  best : Option Nat := none
  first : Option Nat := none
  same : Bool := true

def curStep (items : Array CItem) (level trailSize : Nat)
    (acc : CurScan) (i : Nat) : CurScan :=
  if currentCandidate items level trailSize i then
    let it := items.getD i default
    let best :=
      match acc.best with
      | none => some i
      | some j =>
          if (items.getD j default).pos < it.pos then some i else some j
    { best := best
      first := match acc.first with | none => some i | some f => some f
      same := match acc.first with
        | none => true
        | some f => acc.same && litEqB it.lit (items.getD f default).lit }
  else acc

/-- The scan invariant: the stored index is in range and is a candidate. -/
def CurBest (items : Array CItem) (level trailSize : Nat) (s : CurScan) : Prop :=
  match s.best with
  | none => True
  | some j => j < items.size ∧ currentCandidate items level trailSize j = true

theorem curStep_spec {items : Array CItem} {level trailSize i : Nat}
    {acc : CurScan} (hi : i < items.size)
    (hb : CurBest items level trailSize acc) :
    CurBest items level trailSize (curStep items level trailSize acc i) := by
  unfold curStep
  split
  · rename_i hcand
    dsimp only
    cases hbest : acc.best with
    | none => exact ⟨hi, hcand⟩
    | some j =>
        unfold CurBest at hb
        rw [hbest] at hb
        dsimp only
        have hjlt : j < items.size := hb.1
        simp only [Array.getD_eq_getElem?_getD,
          Array.getElem?_eq_getElem hjlt, Option.getD_some]
        split
        · exact ⟨hi, hcand⟩
        · exact hb
  · exact hb

/-- Scan indices `i, i+1, ..., i+n-1` in ascending order, folding with
`curStep`.  This avoids allocating an `Array.range` on every analysis step.
`hbound` (kept in the spec) is `i + n ≤ items.size`. -/
def scanFrom (items : Array CItem) (level trailSize : Nat) :
    Nat → Nat → CurScan → CurScan
  | 0, _, acc => acc
  | n + 1, i, acc =>
      scanFrom items level trailSize n (i + 1) (curStep items level trailSize acc i)

def scanCurrent (items : Array CItem) (level trailSize : Nat) : CurScan :=
  scanFrom items level trailSize items.size 0 {}

theorem scanFrom_best {items : Array CItem} {level trailSize n i : Nat}
    {acc : CurScan} (hbound : i + n ≤ items.size)
    (hacc : CurBest items level trailSize acc) :
    CurBest items level trailSize (scanFrom items level trailSize n i acc) := by
  induction n generalizing i acc with
  | zero => simpa [scanFrom] using hacc
  | succ n ih =>
      rw [scanFrom]
      refine ih (i := i + 1) (acc := curStep items level trailSize acc i) ?_ ?_
      · omega
      · exact curStep_spec (by omega) hacc

theorem scanCurrent_best_spec {items : Array CItem} {level trailSize i : Nat}
    (h : (scanCurrent items level trailSize).best = some i) :
    i < items.size ∧ (items.getD i default).level = level ∧
      (items.getD i default).pos < trailSize := by
  unfold scanCurrent at h
  have hfold : CurBest items level trailSize
      (scanFrom items level trailSize items.size 0 {}) :=
    scanFrom_best (items := items) (n := items.size) (i := 0) (acc := {})
      (by omega) trivial
  have hb := hfold
  unfold CurBest at hb
  rw [h] at hb
  obtain ⟨hlt, hcand⟩ := hb
  unfold currentCandidate at hcand
  rw [Bool.and_eq_true] at hcand
  exact ⟨hlt, beq_iff_eq.mp hcand.1, by simpa using hcand.2⟩

/-- Index of the current-level item with the largest explanation position.
Only real trail entries are considered (not the initial-domain sentinel). -/
def maxCurrentIdx (items : Array CItem) (level trailSize : Nat) : Option Nat :=
  (Array.range items.size).foldl (maxStep items level trailSize) none

/-- The selected current-level literal is the only current-level literal.
Duplicates of the same literal do not count as different items: clause
semantics is set-like, and `finishAnalysis` already ignores all items whose
literal equals the asserting literal when it computes the backjump. -/
def uniqueCurrentLit (items : Array CItem) (level trailSize i : Nat) : Bool :=
  (Array.range items.size).all fun j =>
    if currentCandidate items level trailSize j then
      litEqB (items.getD j default).lit (items.getD i default).lit
    else true

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
  /-- Size of the item clause before post-analysis minimization.  Diagnostic
  policy metadata only. -/
  litsBefore : Nat := 0
  /-- Literals whose slots receive the activity bump.  This is the
  unminimized clause for a minimizing analysis, preserving the historical
  bump count, and the learned clause otherwise.  Policy metadata only. -/
  bumpLits : Array PLit := #[]
  fuel : Nat
  ok : Bool
  why : String := ""

/-- Pack the kept items for the learned clause, carrying each item's intern
hint.  The hint is untrusted: `canonClause` validates it against the live
table before reuse. -/
def packedItems (items : Array CItem) : Array PLit :=
  items.map fun it => { idx := it.pidx.getD 0, lit := it.lit }

/-- Decoding a packed item array returns the item literals. -/
theorem packedItems_lits (items : Array CItem) :
    (packedItems items).toList.map PLit.decode = items.toList.map (fun it => it.lit) := by
  unfold packedItems
  rw [Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro it _
  rfl

/-- Literal membership through `packedItems`. -/
theorem mem_packedItems_lits_iff {items : Array CItem} {l : Literal} :
    l ∈ (packedItems items).toList.map PLit.decode ↔
      l ∈ items.toList.map (fun it => it.lit) := by
  rw [packedItems_lits]

/-- The learned clause of a finished analysis.  Its packed literals carry
the item intern hints; canonicalisation revalidates every hint. -/
def finishClause (p : CompiledProblem DomConstraint) (T : LitTable)
    (items : Array CItem) (assertIdx : Option Nat)
    (h : Entailed p (items.toList.map (fun it => it.lit)))
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate]) :
    EClause p T :=
  EClause.ofLits p T (packedItems (finishItems items assertIdx)) (by
    rw [LitTable.decodeClause]
    change Entailed p ((packedItems (finishItems items assertIdx)).toList.map PLit.decode)
    rw [packedItems_lits]
    exact finishItems_entailed h hunit assertIdx)

/-- Build the final learned clause and the asserting/backjump data.  The
learned clause is the asserting item (when present) first, then every item at
a non-zero decision level; level-zero items are erased because their negations
are entailed.  The policy fields (`backjump`, `lbd`, `bumpLits`,
`litsBefore`) still use the unerased item set, so erasure cannot change the
search policy. -/
def finishAnalysis (p : CompiledProblem DomConstraint) (T : LitTable)
    (items : Array CItem) (assertIdx : Option Nat) (fuel : Nat)
    (h : Entailed p (items.toList.map (fun it => it.lit)))
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (why : String := "") : Analysis p T :=
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
  { learned := some (finishClause p T items assertIdx h hunit)
    backjump := backjump
    asserting := assertLit?.map pLit
    lbd := lbdOfItems items
    litsBefore := items.size
    bumpLits := ordered.map pLit
    fuel := fuel
    ok := true
    why := why }


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
  /-- A learned clause with no backjump is a root unit: its asserting
  literal is entailed by the problem. -/
  unit_at_root : ∀ ec l, a.learned = some ec → a.asserting = some l →
    a.backjump = 0 → Entailed p [l.lit]

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
  · intro ec l h
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
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (hfalse : ∀ it, it ∈ items.toList → ItemFalse st it) (why : String := "") :
    AnalysisSpec p T st
      (finishAnalysis p T items assertIdx fuel hent hunit why) := by
  have hlearn : (finishAnalysis p T items assertIdx fuel hent hunit why).learned =
      some (finishClause p T items assertIdx hent hunit) := rfl
  constructor
  · simp [finishAnalysis]
  · intro ec hec
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec]
    exact (finishClause p T items assertIdx hent hunit).ent
  · intro h
    simp [finishAnalysis] at h
  · intro ec l hec has
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec]
    cases ha : assertIdx with
    | none =>
        have has' : (finishAnalysis p T items none fuel hent hunit why).asserting = some l := by
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
            change it.lit ∈ (packedItems (finishItems items (some i))).toList.map PLit.decode
            rw [mem_packedItems_lits_iff]
            exact List.mem_map.mpr ⟨it, mem_finishItems_of_getElem? hget, rfl⟩
  · intro ec hec l hl
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    rw [← hec] at hl
    change l ∈ (packedItems (finishItems items assertIdx)).toList.map PLit.decode at hl
    rw [mem_packedItems_lits_iff] at hl
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hl
    exact hfalse it (finishItems_mem hit)
  · intro ec l hec has hbj
    rw [hlearn] at hec
    rw [Option.some.injEq] at hec
    cases ha : assertIdx with
    | none =>
        have has' : (finishAnalysis p T items none fuel hent hunit why).asserting = some l := by
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
            have hbjfold : items.foldl (fun acc (x : CItem) =>
                if litEqB x.lit it.lit then acc
                else if acc < x.level then x.level else acc) 0 = 0 := by
              simpa [finishAnalysis, ha, hget] using hbj
            have hfin : finishItems items (some i) = #[it] :=
              finishItems_eq_singleton_of_backjump_zero hget hbjfold
            have hentit : Entailed p [it.lit] := by
              have h := finishItems_entailed (p := p) (items := items)
                (assertIdx := some i) hent hunit
              rw [hfin] at h
              simpa using h
            rw [hhas]
            simpa [pLit] using hentit

/-! ## Post-analysis clause minimization -/

/-- A literal is syntactically implied false by its own negation. -/
theorem litImpliesNot_negate_self (l : Literal) : litImpliesNot l.negate l = true := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intLe s k => cases pos <;> simp [litImpliesNot, Literal.negate]
  | intNe s v => cases pos <;> simp [litImpliesNot, Literal.negate]
  | boolEq s b => cases pos <;> simp [litImpliesNot, Literal.negate]

/-- Kind compatibility of an item's literal with its initial domain.  This is
the runtime side condition that makes the literal total on accepted
assignments, which the minimization soundness proof needs for its witness. -/
def minKindB (init : Array DomC) (it : CItem) : Bool :=
  atomKindOKB (init.getD (atomSlot it.lit.atom) DomC.empty) it.lit.atom

/-- `q` is a kept item whose negation syntactically implies `it`'s literal
false.  Since clause semantics is set-like, a dropped item that has such a
witness in the kept set contributes nothing to the clause. -/
def minWitnessB (init : Array DomC) (q it : CItem) : Bool :=
  minKindB init q && litImpliesNot q.lit.negate it.lit

/-- Every syntactic implication is between literals on the same slot. -/
theorem litImpliesNot_eq_false_of_slot_ne {a b : Literal}
    (h : atomSlot a.atom ≠ atomSlot b.atom) : litImpliesNot a b = false := by
  obtain ⟨aa, ap⟩ := a
  obtain ⟨ba, bp⟩ := b
  cases aa <;> cases ba <;> simp [litImpliesNot, atomSlot] at h ⊢ <;>
    (intro hst; exact absurd hst h)

theorem litImpliesNot_slot_eq {a b : Literal} (h : litImpliesNot a b = true) :
    atomSlot a.atom = atomSlot b.atom := by
  by_cases hslot : atomSlot a.atom = atomSlot b.atom
  · exact hslot
  · rw [litImpliesNot_eq_false_of_slot_ne hslot] at h
    exact (Bool.false_ne_true h).elim

/-- A successful witness implies that the two literals are on one slot.  The
runtime scan checks this cheap equality before the full implication test. -/
theorem minWitnessB_slot_eq {init : Array DomC} {q it : CItem}
    (h : minWitnessB init q it = true) :
    (atomSlot q.lit.atom == atomSlot it.lit.atom) = true := by
  have h' : litImpliesNot q.lit.negate it.lit = true := by
    have hc := h
    simp only [minWitnessB, Bool.and_eq_true] at hc
    exact hc.2
  have hslot := litImpliesNot_slot_eq h'
  simpa [Literal.negate, beq_iff_eq] using hslot

/-- Keep `it` unless an already-kept item witnesses it away.  The kept set is
append-only: earlier items are never removed.  The slot test is a cheap
pre-filter: every successful `minWitnessB` is on the same slot, so it can
only reduce the number of full implication tests. -/
def minStepL (init : Array DomC) (acc : List CItem) (it : CItem) : List CItem :=
  if acc.any (fun q =>
      (atomSlot q.lit.atom == atomSlot it.lit.atom) && minWitnessB init q it) then acc
  else acc ++ [it]

/-- Greedy clause minimization over `rest`, accumulating the kept items in
`acc`. -/
def minGoL (init : Array DomC) : List CItem → List CItem → List CItem
  | acc, [] => acc
  | acc, it :: rest => minGoL init (minStepL init acc it) rest

theorem mem_minStepL_acc {init : Array DomC} {acc : List CItem} {it : CItem}
    {x : CItem} (h : x ∈ minStepL init acc it) : x ∈ acc ∨ x = it := by
  unfold minStepL at h
  split at h
  · exact Or.inl h
  · rw [List.mem_append, List.mem_singleton] at h
    exact h

theorem mem_minStepL_of_acc {init : Array DomC} {acc : List CItem} {it : CItem}
    {x : CItem} (h : x ∈ acc) : x ∈ minStepL init acc it := by
  unfold minStepL
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_minGoL_of_acc {init : Array DomC} {acc rest : List CItem} {x : CItem}
    (h : x ∈ acc) : x ∈ minGoL init acc rest := by
  induction rest generalizing acc with
  | nil => exact h
  | cons it rest ih => exact ih (mem_minStepL_of_acc h)

/-- The greedy minimization keeps a subset of the original items and every
dropped item has a witness in the final kept set. -/
theorem minGoL_spec (init : Array DomC) (orig : List CItem) :
    ∀ (acc rest : List CItem),
      (∀ x ∈ acc, x ∈ orig) →
      (∀ x ∈ rest, x ∈ orig) →
      (∀ x ∈ orig, x ∈ acc ∨ x ∈ rest ∨
        ∃ q ∈ acc, minWitnessB init q x = true) →
      (∀ x ∈ minGoL init acc rest, x ∈ orig) ∧
      (∀ x ∈ orig, x ∉ minGoL init acc rest →
        ∃ q ∈ minGoL init acc rest, minWitnessB init q x = true) := by
  intro acc rest
  induction rest generalizing acc with
  | nil =>
      intro hacc hrest hall
      constructor
      · simpa [minGoL] using hacc
      · intro x hxorig hxnot
        rcases hall x hxorig with h | h | h
        · exact absurd h hxnot
        · simp at h
        · exact h
  | cons it rest ih =>
      intro hacc hrest hall
      have hit_orig : it ∈ orig := hrest it (by simp)
      have hrest' : ∀ x ∈ rest, x ∈ orig := fun x hx => hrest x (by simp [hx])
      have hacc' : ∀ x ∈ minStepL init acc it, x ∈ orig := by
        intro x hx
        rcases mem_minStepL_acc hx with h | rfl
        · exact hacc x h
        · exact hit_orig
      have hall' : ∀ x ∈ orig, x ∈ minStepL init acc it ∨ x ∈ rest ∨
          ∃ q ∈ minStepL init acc it, minWitnessB init q x = true := by
        intro x hx
        rcases hall x hx with h | h | h
        · exact Or.inl (mem_minStepL_of_acc h)
        · rcases List.mem_cons.mp h with rfl | h
          · unfold minStepL
            split
            · rename_i hany
              obtain ⟨q, hqmem, hqw⟩ := List.any_eq_true.mp hany
              exact Or.inr (Or.inr ⟨q, hqmem, by
                have hq' : (atomSlot q.lit.atom == atomSlot x.lit.atom) = true ∧
                    minWitnessB init q x = true := by
                  simpa using hqw
                exact hq'.2⟩)
            · exact Or.inl (List.mem_append_right _ (by simp))
          · exact Or.inr (Or.inl h)
        · obtain ⟨q, hqacc, hq⟩ := h
          exact Or.inr (Or.inr ⟨q, mem_minStepL_of_acc hqacc, hq⟩)
      exact ih (minStepL init acc it) hacc' hrest' hall'

/-! ## Fast minimization state (R3)

`minStepL` scans the whole kept list for every candidate and appends with `++`
when it keeps one, which is quadratic in the clause size.  The runtime twin
below keeps the same list plus a `slot → kept items` map.  A witness can only
come from the same slot (`minWitnessB_slot_eq`), so scanning that bucket is
equivalent to scanning the full kept list.  The twin is registered with
`@[csimp]`; every proof keeps using `minGoL`. -/

/-- Kept items together with a per-slot index of those same items. -/
structure MinState where
  items : List CItem
  bySlot : Std.HashMap Nat (List CItem)

/-- Append `it` to its slot's bucket, preserving kept order. -/
def minStatePush (m : Std.HashMap Nat (List CItem)) (it : CItem) :
    Std.HashMap Nat (List CItem) :=
  m.insert (atomSlot it.lit.atom)
    (m.getD (atomSlot it.lit.atom) [] ++ [it])

/-- Index an existing kept list. -/
def MinState.ofList (acc : List CItem) : MinState :=
  { items := acc, bySlot := acc.foldl minStatePush ∅ }

/-- Every bucket is exactly the kept list filtered to that slot. -/
def MinState.Inv (a : MinState) : Prop :=
  ∀ s, a.bySlot.getD s [] =
    a.items.filter (fun q => (atomSlot q.lit.atom == s))

theorem minStatePush_getD (m : Std.HashMap Nat (List CItem)) (it : CItem) (s : Nat) :
    (minStatePush m it).getD s [] =
      if atomSlot it.lit.atom == s then
        m.getD (atomSlot it.lit.atom) [] ++ [it]
      else m.getD s [] := by
  unfold minStatePush
  exact Std.HashMap.getD_insert

theorem minState_fold_getD (l : List CItem) (m : Std.HashMap Nat (List CItem))
    (d : List CItem)
    (h : ∀ s, m.getD s [] = d.filter (fun q => (atomSlot q.lit.atom == s)))
    (s : Nat) :
    (l.foldl minStatePush m).getD s [] =
      (d ++ l).filter (fun q => (atomSlot q.lit.atom == s)) := by
  induction l generalizing d m with
  | nil => simpa using h s
  | cons it rest ih =>
      have hstep : ∀ t, (minStatePush m it).getD t [] =
          (d ++ [it]).filter (fun q => (atomSlot q.lit.atom == t)) := by
        intro t
        rw [minStatePush_getD]
        by_cases ht : t = atomSlot it.lit.atom
        · subst t
          simp [h (atomSlot it.lit.atom), List.filter_append]
        · have hbeq : (atomSlot it.lit.atom == t) = false := by
            rw [beq_eq_false_iff_ne]
            exact fun hs => ht hs.symm
          simp [hbeq, h t, List.filter_append]
      rw [← List.singleton_append, ← List.append_assoc]
      exact ih (d := d ++ [it]) (m := minStatePush m it) hstep

theorem MinState.inv_ofList (acc : List CItem) : (MinState.ofList acc).Inv := by
  intro s
  dsimp only [MinState.ofList, MinState.Inv]
  have h0 : ∀ t, (∅ : Std.HashMap Nat (List CItem)).getD t [] =
      ([] : List CItem).filter (fun q => (atomSlot q.lit.atom == t)) := by
    intro t
    rw [Std.HashMap.getD_empty]
    rfl
  simpa using minState_fold_getD acc ∅ [] h0 s

/-- One greedy step over the indexed state. -/
def minStepA (init : Array DomC) (a : MinState) (it : CItem) : MinState :=
  let s := atomSlot it.lit.atom
  if (a.bySlot.getD s []).any (fun q => minWitnessB init q it) then a
  else
    { items := a.items ++ [it]
      bySlot := minStatePush a.bySlot it }

theorem minStepA_guard (init : Array DomC) (a : MinState) (h : a.Inv)
    (it : CItem) :
    (a.bySlot.getD (atomSlot it.lit.atom) []).any
        (fun q => minWitnessB init q it) =
      a.items.any (fun q =>
        (atomSlot q.lit.atom == atomSlot it.lit.atom) && minWitnessB init q it) := by
  rw [h (atomSlot it.lit.atom), List.any_filter]

theorem minStepA_items (init : Array DomC) (a : MinState) (h : a.Inv) (it : CItem) :
    (minStepA init a it).items = minStepL init a.items it := by
  have hg := minStepA_guard init a h it
  simp only [minStepA, minStepL]
  rw [hg]
  split <;> rfl

theorem minStepA_inv (init : Array DomC) (a : MinState) (h : a.Inv) (it : CItem) :
    (minStepA init a it).Inv := by
  intro t
  simp only [minStepA]
  split
  · exact h t
  · by_cases ht : t = atomSlot it.lit.atom
    · subst t
      rw [minStatePush_getD]
      simp only [beq_self_eq_true, ite_true]
      rw [h (atomSlot it.lit.atom), List.filter_append]
      simp
    · have hbeq : (atomSlot it.lit.atom == t) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hs => ht hs.symm
      rw [minStatePush_getD]
      simp only [hbeq]
      rw [h t, List.filter_append]
      simp [hbeq]

/-- Greedy minimization over the indexed state. -/
def minGoA (init : Array DomC) (a : MinState) : List CItem → List CItem
  | [] => a.items
  | it :: rest => minGoA init (minStepA init a it) rest

theorem minGoA_eq_minGoL (init : Array DomC) (rest : List CItem) :
    ∀ (a : MinState) (acc : List CItem), a.items = acc → a.Inv →
      minGoA init a rest = minGoL init acc rest := by
  induction rest with
  | nil =>
      intro a acc hitems _
      simp [minGoA, minGoL, hitems]
  | cons it rest ih =>
      intro a acc hitems hinv
      have hstep := minStepA_items init a hinv it
      have hinv' := minStepA_inv init a hinv it
      show minGoA init (minStepA init a it) rest =
        minGoL init (minStepL init acc it) rest
      exact ih (minStepA init a it) (minStepL init acc it)
        (by rw [hstep, hitems]) hinv'

/-- The map-backed minimizer returns exactly `minGoL`'s list. -/
def minGoFast (init : Array DomC) (acc rest : List CItem) : List CItem :=
  minGoA init (MinState.ofList acc) rest

/-- Compiled code uses the map-backed minimizer; proofs keep `minGoL`. -/
@[csimp] theorem minGoL_eq_minGoFast : @minGoL = @minGoFast := by
  funext init acc rest
  exact (minGoA_eq_minGoL init rest (MinState.ofList acc) acc rfl
    (MinState.inv_ofList acc)).symm

/-- Item order for minimization: the asserting item first, when present. -/
def minimizeOrder (items : Array CItem) (assertIdx : Option Nat) : List CItem :=
  match assertIdx with
  | some i =>
      match items[i]? with
      | some it => it :: items.toList.eraseIdx i
      | none => items.toList
  | none => items.toList

theorem minimizeOrder_perm (items : Array CItem) (assertIdx : Option Nat) :
    (minimizeOrder items assertIdx).Perm items.toList := by
  unfold minimizeOrder
  cases assertIdx with
  | none => simp
  | some i =>
      cases hget : items[i]? with
      | none => simp [hget]
      | some it =>
          simp only [hget]
          have hi : i < items.size := (Array.getElem?_eq_some_iff.mp hget).1
          have hlist : items.toList[i]? = some it := by simpa using hget
          simpa using (perm_getElem?_cons_eraseIdx items.toList hlist).map
            (fun it : CItem => it)

/-- Total evaluation for a kind-compatible literal at a converted slot. -/
theorem Literal.eval_isSome_of_kind {p : CompiledProblem DomConstraint}
    {init : Array DomC} {l : Literal}
    (hslot : atomSlot l.atom < p.domains.length)
    (hconv : DomC.ofDom? (p.domains.getD (atomSlot l.atom) Dom.empty) =
      some (init.getD (atomSlot l.atom) DomC.empty))
    (hkind : atomKindOKB (init.getD (atomSlot l.atom) DomC.empty) l.atom = true) :
    ∀ a ∈ allAssigns p.domains, (l.eval a).isSome = true := by
  intro a ha
  obtain ⟨v, hav, hvmem⟩ := mem_allAssigns_getElem_mem (ds := p.domains) ha hslot
  have hinitmem : (init.getD (atomSlot l.atom) DomC.empty).mem v = true := by
    rw [DomC.mem_iff (p.domains.getD (atomSlot l.atom) Dom.empty)
      (init.getD (atomSlot l.atom) DomC.empty) hconv v]
    exact hvmem
  have hdef := atomKindOKB_spec hkind hinitmem
  obtain ⟨atom, pos⟩ := l
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hav
  have hav' : a[atom.slot]? = some v := by
    simpa only [atomSlot_eq_slot] using hav
  have hlt_a : atom.slot < a.length := by
    simpa only [atomSlot_eq_slot] using hlt
  have hget_a : a[atom.slot] = v := (List.getElem?_eq_some_iff.mp hav').2
  have hsome : (Atom.evalAtValue atom v).isSome = true := by
    cases h : Atom.evalAtValue atom v with
    | none => exact absurd h hdef
    | some x => rfl
  rw [Literal.eval, Atom.eval_eq_evalAtValue atom a hlt_a, hget_a]
  simpa using hsome

/-- Remove literals that a kept literal syntactically forces false.  The
witness is required to be kind compatible with the initial domain so its
evaluation is total on every accepted assignment. -/
theorem Entailed_of_litWitness {p : CompiledProblem DomConstraint}
    {init : Array DomC} {c c' : Clause}
    (h : Entailed p c)
    (hwit : ∀ l ∈ c, l ∉ c' → ∃ q ∈ c',
      atomKindOKB (init.getD (atomSlot q.atom) DomC.empty) q.atom = true ∧
      litImpliesNot q.negate l = true)
    (hconv : ∀ q ∈ c', atomSlot q.atom < p.domains.length ∧
      DomC.ofDom? (p.domains.getD (atomSlot q.atom) Dom.empty) =
        some (init.getD (atomSlot q.atom) DomC.empty)) :
    Entailed p c' := by
  intro b hb hacc
  by_cases hsat : c'.SatisfiedBy b
  · exact hsat
  · obtain ⟨l, hl, hltrue⟩ := h b hb hacc
    by_cases hlmem : l ∈ c'
    · exact absurd ⟨l, hlmem, hltrue⟩ hsat
    · obtain ⟨q, hqmem, hqkind, hqimp⟩ := hwit l hl hlmem
      obtain ⟨hqslot, hqconv⟩ := hconv q hqmem
      have hqsome := Literal.eval_isSome_of_kind hqslot hqconv hqkind b hb
      obtain ⟨x, hqx⟩ := Option.isSome_iff_exists.mp hqsome
      have hqfalse : q.eval b = some false := by
        cases x with
        | true => exact absurd ⟨q, hqmem, hqx⟩ hsat
        | false => exact hqx
      have hqneg : q.negate.eval b = some true :=
        Literal.eval_negate_false_iff q b |>.mpr hqfalse
      have hfalse := litImpliesNot_sound hqimp b hqneg
      rw [hltrue] at hfalse
      simp at hfalse

/-- Minimized result of the ordered items.  The first two ordered items are
left untouched: they are the two watched literals of the stored clause, so
minimization never changes the initial watch pair. -/
def minimizeItemsAux (init : Array DomC) (order : List CItem) : Array CItem :=
  match order with
  | a :: b :: rest => (minGoL init [a, b] rest).toArray
  | _ => order.toArray

/-- Run the minimization over the items, asserting item first when present.
The assertion index `some i` becomes `some 0` because the asserting item is
placed first and never removed. -/
def minimizeItems (init : Array DomC) (items : Array CItem)
    (assertIdx : Option Nat) : Array CItem × Option Nat :=
  let res := minimizeItemsAux init (minimizeOrder items assertIdx)
  match assertIdx with
  | some i =>
      match items[i]? with
      | some _ => (res, some 0)
      | none => (res, none)
  | none => (res, none)

theorem minimizeItems_fst (init : Array DomC) (items : Array CItem)
    (assertIdx : Option Nat) :
    (minimizeItems init items assertIdx).1 =
      minimizeItemsAux init (minimizeOrder items assertIdx) := by
  unfold minimizeItems
  cases assertIdx with
  | none => rfl
  | some i =>
      cases h : items[i]? with
      | none => simp [h]
      | some it => simp [h]

theorem minGoL_cons_head (init : Array DomC) (it : CItem) (acc rest : List CItem) :
    ∃ tail, minGoL init (it :: acc) rest = it :: tail := by
  induction rest generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons x rest ih =>
      unfold minGoL
      have hstep : minStepL init (it :: acc) x =
          it :: (if (it :: acc).any (fun q =>
              (atomSlot q.lit.atom == atomSlot x.lit.atom) && minWitnessB init q x)
            then acc else acc ++ [x]) := by
        unfold minStepL
        split <;> simp
      rw [hstep]
      exact ih (if (it :: acc).any (fun q =>
          (atomSlot q.lit.atom == atomSlot x.lit.atom) && minWitnessB init q x)
        then acc else acc ++ [x])

theorem minimizeItems_getElem_zero {init : Array DomC} {items : Array CItem}
    {i : Nat} {it : CItem} (hget : items[i]? = some it) :
    (minimizeItems init items (some i)).1[0]? = some it := by
  rw [minimizeItems_fst]
  have horder : minimizeOrder items (some i) = it :: items.toList.eraseIdx i := by
    simp [minimizeOrder, hget]
  rw [horder]
  cases htail : items.toList.eraseIdx i with
  | nil => simp [minimizeItemsAux, htail]
  | cons b rest =>
      obtain ⟨tail, htail'⟩ := minGoL_cons_head init it [b] rest
      simp only [minimizeItemsAux, htail]
      rw [htail']
      simp

theorem minimizeItems_snd_some {init : Array DomC} {items : Array CItem}
    {i : Nat} {it : CItem} (hget : items[i]? = some it) :
    (minimizeItems init items (some i)).2 = some 0 := by
  unfold minimizeItems
  rw [show minimizeOrder items (some i) = it :: items.toList.eraseIdx i by
    simp [minimizeOrder, hget]]
  simp [hget]

theorem minimizeItems_subset {init : Array DomC} {items : Array CItem}
    {assertIdx : Option Nat} {x : CItem}
    (h : x ∈ (minimizeItems init items assertIdx).1.toList) :
    x ∈ items.toList := by
  let order := minimizeOrder items assertIdx
  have hperm : order.Perm items.toList := minimizeOrder_perm items assertIdx
  have hres : x ∈ (minimizeItemsAux init order).toList := by
    simpa [minimizeItems_fst, order] using h
  cases hcase : order with
  | nil => simp [minimizeItemsAux, hcase] at hres
  | cons a rest =>
      cases hrestEq : rest with
      | nil =>
          have hx : x ∈ order := by
            simpa [hcase, hrestEq, minimizeItemsAux] using hres
          exact hperm.mem_iff.mp hx
      | cons b rest' =>
          have hacc : ∀ y ∈ [a, b], y ∈ order := by
            intro y hy
            rw [hcase, hrestEq]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
            rcases hy with rfl | rfl
            · simp
            · simp
          have hrest : ∀ y ∈ rest', y ∈ order := by
            intro y hy
            rw [hcase, hrestEq]
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact Or.inr (Or.inr hy)
          have hall : ∀ y ∈ order, y ∈ [a, b] ∨ y ∈ rest' ∨
              ∃ q ∈ [a, b], minWitnessB init q y = true := by
            intro y hy
            rw [hcase, hrestEq] at hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
            rcases hy with rfl | rfl | hy
            · simp
            · simp
            · exact Or.inr (Or.inl hy)
          have hspec := (minGoL_spec init order [a, b] rest'
            hacc hrest hall).1
          have hxres : x ∈ (minGoL init [a, b] rest').toArray.toList := by
            simpa [hcase, hrestEq, minimizeItemsAux] using hres
          exact hperm.mem_iff.mp (hspec x (by simpa using hxres))

theorem minimizeItems_entailed {p : CompiledProblem DomConstraint}
    {init : Array DomC} {st : EngineState p T} {items : Array CItem}
    {assertIdx : Option Nat} (hinv : ItemsInv p init st items) :
    Entailed p
      ((minimizeItems init items assertIdx).1.toList.map (fun it => it.lit)) := by
  let order := minimizeOrder items assertIdx
  have hperm : order.Perm items.toList := minimizeOrder_perm items assertIdx
  have horder : Entailed p (order.map (fun it => it.lit)) :=
    Entailed_of_perm hinv.ent (hperm.symm.map (fun it => it.lit))
  rw [minimizeItems_fst]
  change Entailed p ((minimizeItemsAux init order).toList.map (fun it => it.lit))
  cases hcase : order with
  | nil => simpa [minimizeItemsAux, hcase] using horder
  | cons a rest =>
      cases hrestEq : rest with
      | nil => simpa [minimizeItemsAux, hcase, hrestEq] using horder
      | cons b rest' =>
          simp only [minimizeItemsAux, hcase, hrestEq]
          have hacc : ∀ y ∈ [a, b], y ∈ order := by
            intro y hy
            rw [hcase, hrestEq]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
            rcases hy with rfl | rfl
            · simp
            · simp
          have hrest : ∀ y ∈ rest', y ∈ order := by
            intro y hy
            rw [hcase, hrestEq]
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact Or.inr (Or.inr hy)
          have hall : ∀ y ∈ order, y ∈ [a, b] ∨ y ∈ rest' ∨
              ∃ q ∈ [a, b], minWitnessB init q y = true := by
            intro y hy
            rw [hcase, hrestEq] at hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
            rcases hy with rfl | rfl | hy
            · simp
            · simp
            · exact Or.inr (Or.inl hy)
          have hspec := minGoL_spec init order [a, b] rest' hacc hrest hall
          apply Entailed_of_litWitness (c := order.map (fun it => it.lit)) horder
          · intro l hl hlnot
            obtain ⟨x, hxorder, rfl⟩ := List.mem_map.mp hl
            have hxnotres : x ∉ (minGoL init [a, b] rest').toArray.toList := by
              intro hxres
              exact hlnot (List.mem_map.mpr ⟨x, by simpa using hxres, rfl⟩)
            obtain ⟨q, hqres, hqw⟩ :=
              hspec.2 x (by simpa [hcase, hrestEq] using hxorder) hxnotres
            have hqw' : minKindB init q = true ∧
                litImpliesNot q.lit.negate x.lit = true := by
              simpa [minWitnessB] using hqw
            refine ⟨q.lit, List.mem_map.mpr ⟨q, by simpa using hqres, rfl⟩,
              hqw'.1, hqw'.2⟩
          · intro l hl
            obtain ⟨q, hqres, rfl⟩ := List.mem_map.mp hl
            have hqorder : q ∈ order := hspec.1 q (by simpa using hqres)
            have hqitems : q ∈ items.toList := hperm.mem_iff.mp hqorder
            have hexp := hinv.explained q hqitems
            exact ⟨hexp.slot_lt, hexp.conv⟩

/-- Finish an analysis after duplicate/implied-literal minimization. -/
def finishAnalysisMin (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) (items : Array CItem)
    (assertIdx : Option Nat) (fuel : Nat) (hinv : ItemsInv p init st items)
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (why : String := "") : Analysis p T :=
  let m := minimizeItems init items assertIdx
  finishAnalysis p T m.1 m.2 fuel (minimizeItems_entailed hinv)
    (fun it hit hlev => hunit it (minimizeItems_subset hit) hlev) why

theorem finishAnalysisMin_spec {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {items : Array CItem}
    {assertIdx : Option Nat} {fuel : Nat} (hinv : ItemsInv p init st items)
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (why : String := "") :
    AnalysisSpec p T st
      (finishAnalysisMin p T init st items assertIdx fuel hinv hunit why) := by
  unfold finishAnalysisMin
  exact finishAnalysis_spec (minimizeItems_entailed hinv)
    (fun it hit hlev => hunit it (minimizeItems_subset hit) hlev)
    (fun it hit => hinv.isFalse it (minimizeItems_subset hit)) why

/-- The minimized asserting-backjump is zero whenever the original one is
zero and the asserting item exists. -/
theorem minimize_backjump_eq_zero_some {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {items : Array CItem} {i : Nat} {it : CItem} {fuel : Nat}
    {hinv : ItemsInv p init st items}
    {hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate]}
    {why : String} (hget : items[i]? = some it)
    (hbj : (finishAnalysis p T items (some i) fuel hinv.ent hunit why).backjump = 0) :
    (finishAnalysisMin p T init st items (some i) fuel hinv hunit why).backjump = 0 := by
  have hai : (items[i]?.getD default).lit = it.lit := by
    simp [hget]
  have hbjlist : items.toList.foldl (fun acc (x : CItem) =>
      if litEqB x.lit it.lit then acc
      else if acc < x.level then x.level else acc) 0 = 0 := by
    simpa [finishAnalysis, Array.getD_eq_getD_getElem?, hai] using hbj
  obtain ⟨-, hall⟩ :=
    foldl_backjump_eq_zero (l := items.toList) (ai := it.lit) (acc := 0) hbjlist
  have hmget : (minimizeItems init items (some i)).1[0]? = some it :=
    minimizeItems_getElem_zero hget
  have hmsnd : (minimizeItems init items (some i)).2 = some 0 :=
    minimizeItems_snd_some hget
  have hmai : ((minimizeItems init items (some i)).1.getD 0 default).lit = it.lit := by
    simp [Array.getD_eq_getD_getElem?, hmget]
  unfold finishAnalysisMin
  dsimp only
  rw [hmsnd]
  simp only [finishAnalysis]
  rw [hmai]
  rw [← Array.foldl_toList]
  exact foldl_backjump_zero_of_lits (ai := it.lit)
    (fun x hx => hall x (minimizeItems_subset hx))

/-- Minimization variant that keeps the backjump and LBD computed from the
original item set.  The learned clause is still the minimized one, but the
search policy (backjump level and clause-deletion bucket) follows the
unminimized analysis, so minimization cannot move the backtrack target. -/
def finishAnalysisMinKeep (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) (items : Array CItem)
    (assertIdx : Option Nat) (fuel : Nat) (hinv : ItemsInv p init st items)
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (why : String := "") : Analysis p T :=
  let a := finishAnalysisMin p T init st items assertIdx fuel hinv hunit why
  { a with
    backjump := (finishAnalysis p T items assertIdx fuel hinv.ent hunit why).backjump
    lbd := lbdOfItems items
    litsBefore := items.size
    bumpLits := items.map (fun it => pLit it.lit) }

theorem finishAnalysisMinKeep_spec {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {items : Array CItem} {assertIdx : Option Nat} {fuel : Nat}
    (hinv : ItemsInv p init st items)
    (hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate])
    (why : String := "") :
    AnalysisSpec p T st
      (finishAnalysisMinKeep p T init st items assertIdx fuel hinv hunit why) := by
  have h := finishAnalysisMin_spec (p := p) (T := T) (init := init) (st := st)
    (items := items) (assertIdx := assertIdx) (fuel := fuel) hinv hunit why
  have hunitroot : ∀ ec l,
      (finishAnalysisMinKeep p T init st items assertIdx fuel hinv hunit why).learned = some ec →
      (finishAnalysisMinKeep p T init st items assertIdx fuel hinv hunit why).asserting = some l →
      (finishAnalysisMinKeep p T init st items assertIdx fuel hinv hunit why).backjump = 0 →
      Entailed p [l.lit] := by
   intro ec l hec has hbj
   have hec' : (finishAnalysisMin p T init st items assertIdx fuel hinv hunit why).learned
       = some ec := by
     simpa [finishAnalysisMinKeep] using hec
   have has' : (finishAnalysisMin p T init st items assertIdx fuel hinv hunit why).asserting
       = some l := by
     simpa [finishAnalysisMinKeep] using has
   have hbj' : (finishAnalysis p T items assertIdx fuel hinv.ent hunit why).backjump = 0 := by
     simpa [finishAnalysisMinKeep] using hbj
   have hmin0 : (finishAnalysisMin p T init st items assertIdx fuel hinv hunit why).backjump
       = 0 := by
     cases ha : assertIdx with
     | none =>
         exfalso
         rw [ha] at has'
         have hass : (finishAnalysisMin p T init st items none fuel hinv hunit why).asserting
             = none := by
           simp [finishAnalysisMin, minimizeItems, finishAnalysis]
         rw [hass] at has'
         simp at has'
     | some i =>
         cases hget : items[i]? with
         | none =>
             exfalso
             rw [ha] at has'
             have hass : (finishAnalysisMin p T init st items (some i) fuel hinv hunit why).asserting
                 = none := by
               simp [finishAnalysisMin, minimizeItems, hget, finishAnalysis]
             rw [hass] at has'
             simp at has'
         | some it =>
             exact minimize_backjump_eq_zero_some (p := p) (T := T) (init := init)
               (st := st) (items := items) (i := i) (it := it) (fuel := fuel)
               (hinv := hinv) (hunit := hunit) (why := why) hget
               (by simpa [ha] using hbj')
   exact h.unit_at_root ec l hec' has' hmin0
  exact { ok_iff := h.ok_iff
          sound := h.sound
          no_claim := h.no_claim
          asserting_mem := h.asserting_mem
          lits_false := h.lits_false
          unit_at_root := hunitroot }

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
    {hunit : ∀ it ∈ items.toList, it.level = 0 → Entailed p [it.lit.negate]}
    (hget : items[i]? = some it)
    (hlevel : it.level = st.level)
    (hothers : ∀ j (jt : CItem), items[j]? = some jt → j ≠ i →
      jt.level < st.level)
    (hpos : 0 < st.level) :
    (finishAnalysis p T items (some i) fuel hent hunit).backjump < st.level := by
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
    (init : Array DomC) (st : EngineState p T) (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st) :
    Nat → Nat → (items : Array CItem) → ItemsInv p init st items →
      { a : Analysis p T // AnalysisSpec p T st a }
  | 0, _, _, _ =>
      ⟨failAnalysis p T 0 "analysis fuel exhausted", failAnalysis_spec 0 _⟩
  | f + 1, budget, items, hinv =>
      if hlev : st.level = 0 then
        match hget : items[0]? with
        | none =>
            ⟨finishAnalysisMinKeep p T init st items none (f + 1) hinv
                (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev),
              finishAnalysisMinKeep_spec hinv
                (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev)⟩
        | some it =>
            if hsent : it.pos = st.trail.size then
              analyzeGo p T init st hconv hhist hroot f budget (eraseCItemAt items 0)
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
                          analyzeGo p T init st hconv hhist hroot f
                            (dedupWithBudget items' budget).2
                            (dedupWithBudget items' budget).1
                            (dedupWithBudget_inv (resolveWith_inv hconv hhist hinv
                              (List.mem_map.mpr
                                ⟨it, mem_of_getElem?_zero hget, rfl⟩)
                              hres
                              (fun hn => chain_entailed_of_item
                                (chainCert_of_resolveWith_ok_none hconv hres hn)
                                (hinv.explained it (mem_of_getElem?_zero hget))
                                htr hsent)))
      else
        let sc := scanCurrent items st.level st.trail.size
        match hmax : sc.best with
        | none =>
            ⟨finishAnalysisMinKeep p T init st items none (f + 1) hinv
                (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev),
              finishAnalysisMinKeep_spec hinv
                (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev)⟩
        | some i =>
            have hi : i < items.size := (scanCurrent_best_spec hmax).1
            if _hsame : sc.same = true then
              -- First-UIP stop: every current-level candidate has the same
              -- literal, so the selected one is asserting after backjumping
              -- below the current level.
              ⟨finishAnalysisMinKeep p T init st items (some i) (f + 1) hinv
                  (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev)
                  "first-UIP",
                finishAnalysisMinKeep_spec hinv
                  (fun it hit hlev => hroot.item_unit (hinv.explained it hit) hlev)
                  "first-UIP"⟩
            else
              let it := items[i]
              match htr : st.trail[it.pos]? with
              | none =>
                  ⟨failAnalysis p T f s!"missing trail entry {it.pos}",
                    failAnalysis_spec f _⟩
              | some e =>
                  match hres : resolveWith p init st items i it.lit it.pos
                      (reasonClause? st e.reason) with
                  | .error msg =>
                      ⟨failAnalysis p T f msg, failAnalysis_spec f _⟩
                  | .ok items' =>
                      analyzeGo p T init st hconv hhist hroot f
                        (dedupWithBudget items' budget).2
                        (dedupWithBudget items' budget).1
                        (dedupWithBudget_inv (resolveWith_inv hconv hhist hinv
                          (List.mem_map.mpr
                            ⟨it, Array.mem_toList_iff.mpr (Array.getElem_mem hi), rfl⟩)
                          hres
                          (fun hn => chain_entailed_of_item
                            (chainCert_of_resolveWith_ok_none hconv hres hn)
                            (hinv.explained it
                              (Array.mem_toList_iff.mpr (Array.getElem_mem (scanCurrent_best_spec hmax).1)))
                            htr
                            (by
                              have hlt := (scanCurrent_best_spec hmax).2.2
                              have hgetD : items.getD i default = items[i] := by
                                rw [Array.getD_eq_getElem?_getD,
                                  Array.getElem?_eq_getElem (scanCurrent_best_spec hmax).1]
                                rfl
                              have hposlt : it.pos < st.trail.size := by
                                dsimp [it]
                                rwa [← hgetD]
                              omega))))

/-- Analyze a conflict clause.  Missing explanations or exhausting the fuel
give up with no claim; a successful run carries an entailed learned clause. -/
def analyze (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (st : EngineState p T) (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    (conflict : EClause p T) (fuel : Nat) : Analysis p T :=
  match hinit : initialItems p init st conflict.lits.toList with
  | none => failAnalysis p T fuel "initial conflict explanation incomplete"
  | some items =>
      (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
        (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hinit))).1

theorem analyze_of_initialItems_none {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat}
    (h : initialItems p init st conflict.lits.toList = none) :
    analyze p T init st hconv hhist hroot conflict fuel =
      failAnalysis p T fuel "initial conflict explanation incomplete" := by
  unfold analyze
  split
  · rfl
  · rename_i hsome
    rw [h] at hsome
    cases hsome

theorem analyze_of_initialItems_some {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat} {items : Array CItem}
    (h : initialItems p init st conflict.lits.toList = some items) :
    analyze p T init st hconv hhist hroot conflict fuel =
      (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
        (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList h))).1 := by
  unfold analyze
  split
  · rename_i hnone
    rw [h] at hnone
    cases hnone
  · rename_i items' hsome
    rw [h] at hsome
    injection hsome with heq
    subst heq
    have hp : (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome)) =
        (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList h)) := Subsingleton.elim _ _
    rw [hp]

theorem analyze_sound {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat}
    (h : (analyze p T init st hconv hhist hroot conflict fuel).ok = true) :
    ∃ ec, (analyze p T init st hconv hhist hroot conflict fuel).learned = some ec ∧
      Entailed p (T.decodeClause ec.lits) := by
  by_cases hnone : initialItems p init st conflict.lits.toList = none
  · rw [analyze_of_initialItems_none hconv hhist hroot hnone] at h ⊢
    simp [failAnalysis] at h
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hconv hhist hroot hsome] at h ⊢
    exact (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome))).2.sound_ok h

theorem analyze_learned_none_of_not_ok {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat}
    (h : (analyze p T init st hconv hhist hroot conflict fuel).ok = false) :
    (analyze p T init st hconv hhist hroot conflict fuel).learned = none := by
  by_cases hnone : initialItems p init st conflict.lits.toList = none
  · rw [analyze_of_initialItems_none hconv hhist hroot hnone] at h ⊢
    rfl
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hconv hhist hroot hsome] at h ⊢
    exact (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome))).2.no_claim h

/-- Alias for the §C operational name. -/
theorem analyze_no_claim_on_failure {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat}
    (h : (analyze p T init st hconv hhist hroot conflict fuel).ok = false) :
    (analyze p T init st hconv hhist hroot conflict fuel).learned = none :=
  analyze_learned_none_of_not_ok hconv hhist hroot h

theorem analyze_ok_learned {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat} :
    (analyze p T init st hconv hhist hroot conflict fuel).ok = true ↔
      (analyze p T init st hconv hhist hroot conflict fuel).learned.isSome := by
  by_cases hnone : initialItems p init st conflict.lits.toList = none
  · rw [analyze_of_initialItems_none hconv hhist hroot hnone]
    simp [failAnalysis]
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hconv hhist hroot hsome]
    exact (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome))).2.ok_iff

theorem analyze_empty_unsat {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    {conflict : EClause p T}
    {fuel : Nat} {ec : EClause p T}
    (hok : (analyze p T init st hconv hhist hroot conflict fuel).ok = true)
    (hlearned : (analyze p T init st hconv hhist hroot conflict fuel).learned = some ec)
    (hempty : ec.lits.isEmpty) : Entailed p [] := by
  obtain ⟨ec', hec', hent⟩ := analyze_sound hconv hhist hroot hok
  rw [hlearned] at hec'
  rw [Option.some.injEq] at hec'
  subst hec'
  have hto : ec.lits.toList = [] := Array.toList_eq_nil_iff.mpr
    (Array.isEmpty_iff.mp hempty)
  have hdec : T.decodeClause ec.lits = [] := by
    simp [LitTable.decodeClause, hto]
  rwa [hdec] at hent

theorem analyze_asserting_mem {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    {conflict : EClause p T}
    {fuel : Nat} {ec : EClause p T} {l : PLit}
    (hlearned : (analyze p T init st hconv hhist hroot conflict fuel).learned = some ec)
    (hasserting : (analyze p T init st hconv hhist hroot conflict fuel).asserting = some l) :
    l.lit ∈ ec.lits.toList.map PLit.decode := by
  by_cases hnone : initialItems p init st conflict.lits.toList = none
  · rw [analyze_of_initialItems_none hconv hhist hroot hnone] at hlearned
    simp [failAnalysis] at hlearned
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hconv hhist hroot hsome] at hlearned hasserting
    exact (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome))).2.asserting_mem ec l hlearned hasserting

/-- **§C, stronger form.**  Every literal of the learned clause is false on
the current live domains.  No separate reason-falsity hypothesis is needed:
`analyzeGo` checks every item it adds with `itemOKB` (`itemCheckB` plus
`domFalseB`), so the item invariant carries current falsity throughout. -/
theorem analyze_learned_lits_false {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hconv : InitConv p init) (hhist : SlotHistory init st)
    (hroot : RootInv p T init st)
    {conflict : EClause p T} {fuel : Nat} {ec : EClause p T}
    (hlearned : (analyze p T init st hconv hhist hroot conflict fuel).learned = some ec) :
    ∀ l ∈ ec.lits.toList.map PLit.decode,
      (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  by_cases hnone : initialItems p init st conflict.lits.toList = none
  · rw [analyze_of_initialItems_none hconv hhist hroot hnone] at hlearned
    simp [failAnalysis] at hlearned
  · obtain ⟨items, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [analyze_of_initialItems_some hconv hhist hroot hsome] at hlearned
    exact (analyzeGo p T init st hconv hhist hroot fuel (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hsome))).2.lits_false ec hlearned

/-- The full `AnalysisSpec` for `analyze`. -/
theorem analyze_spec {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (hconv : InitConv p init)
    (hhist : SlotHistory init st) (hroot : RootInv p T init st)
    (conflict : EClause p T) (fuel : Nat) :
    AnalysisSpec p T st (analyze p T init st hconv hhist hroot conflict fuel) := by
  unfold analyze
  split
  · exact failAnalysis_spec _ _
  · rename_i items hinit
    exact (analyzeGo p T init st hconv hhist hroot fuel
      (initialBudget (dedupItems items)) (dedupItems items)
      (dedupItems_inv (initialItems_inv hconv hhist conflict.ent_toList hinit))).2

end LeanFzn.Engine

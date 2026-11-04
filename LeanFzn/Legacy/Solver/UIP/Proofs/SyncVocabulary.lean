/-
File: LeanFzn/Solver/UIP/Proofs/SyncVocabulary.lean

Purpose (R1d): the literal-pool bridges for the frame/trail synchronisation
(`Propagation/FrameSync.lean`): every literal `syncSlot`/`syncAll` pushes
lies in `litPool orig` (hence in every extension `litPoolWith extra orig`),
so the trail vocabulary is preserved by the synchronised steps. The
value-literal pool bridges formerly in `CanonicalTrailVocabulary` live here
(they are needed by the earlier vocabulary consumers).

NO `sorry`, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Legacy.Solver.Propagation.FrameSync
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The value-literal pool bridges -/

/-- In-range `getD` reads the element. -/
theorem getD_eq_getElem_of_lt {α : Type} {l : List α} {i : Nat} {d : α}
    (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem slotAtomPool_mem_atomPoolBase_aux (ds : List Domain) :
    ∀ (off s : Nat) (a : Atom), s < ds.length →
      a ∈ slotAtomPool (off + s) (ds.getD s Dom.empty) → a ∈ atomPoolBase off ds := by
  induction ds with
  | nil =>
      intro off s a hs
      exact absurd hs (by simp)
  | cons d ds ih =>
      intro off s a hs h
      cases s with
      | zero =>
          have h1 : (d :: ds).getD 0 Dom.empty = d := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_cons_zero]
            rfl
          have h' : a ∈ slotAtomPool off d := by rwa [h1] at h
          exact List.mem_append_left _ h'
      | succ s =>
          have h1 : (d :: ds).getD (s + 1) Dom.empty = ds.getD s Dom.empty := by
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_cons_succ]
          have hs' : s < ds.length := by simpa using hs
          have h2 : off + (s + 1) = (off + 1) + s := by omega
          have h' : a ∈ slotAtomPool ((off + 1) + s) (ds.getD s Dom.empty) := by
            rwa [h1, h2] at h
          exact List.mem_append_right _ (ih (off + 1) s a hs' h')

/-- A slot atom drawn from the slot's own domain is in the base atom pool. -/
theorem slotAtomPool_mem_atomPoolBase {ds : List Domain} {s : Nat} {a : Atom}
    (hs : s < ds.length) (h : a ∈ slotAtomPool s (ds.getD s Dom.empty)) :
    a ∈ atomPoolBase 0 ds :=
  slotAtomPool_mem_atomPoolBase_aux ds 0 s a hs (by simpa using h)

/-- Both Boolean polarities of a slot's pin atom are pooled, for every
domain (a Boolean pin never needs a value representative). -/
theorem boolEq_mem_slotAtomPool (s : Nat) (d : Domain) (b : Bool) :
    Atom.boolEq s b ∈ slotAtomPool s d :=
  List.mem_append_left _ (by cases b <;> simp)

/-- A value-removal atom at a domain value is pooled. -/
theorem intNe_mem_slotAtomPool {s : Nat} {d : Domain} {i : Int}
    (h : i ∈ vocabDomInts d) : Atom.intNe s i ∈ slotAtomPool s d :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, h, rfl⟩)

/-- **THE PIN-LITERAL POOL BRIDGE**: a `valueLiteral` output of a value
present at slot `s` of the box normalizes into the pool. -/
theorem valueLiteral_norm_mem_litPool {orig : List Domain} {s : Nat}
    {v : Value} {l : Literal} (hs : s < orig.length)
    (hv : v ∈ orig.getD s Dom.empty) (hl : valueLiteral s v = some l) :
    l.norm ∈ litPool orig := by
  have hslot : orig.getD s Dom.empty = orig[s] := getD_eq_getElem_of_lt hs
  rw [hslot] at hv
  cases v with
  | bool b =>
      have hb : l = posBool s b := by simpa [valueLiteral] using hl.symm
      subst hb
      have ha : Atom.boolEq s b ∈ slotAtomPool s (orig.getD s Dom.empty) := by
        rw [hslot]
        exact boolEq_mem_slotAtomPool s (orig[s]) b
      show posLit (Atom.boolEq s b) ∈ litPool orig
      exact posLit_mem (List.mem_append_left _
        (slotAtomPool_mem_atomPoolBase hs ha))
  | int i =>
      have hi : l = negNe s i := by simpa [valueLiteral] using hl.symm
      subst hi
      have hvE : Value.int i ∈ Dom.enum orig[s] :=
        (DomainLike.mem_iff _ _).mp hv
      have ha : Atom.intNe s i ∈ slotAtomPool s (orig.getD s Dom.empty) := by
        rw [hslot]
        exact intNe_mem_slotAtomPool
          (List.mem_filterMap.mpr ⟨Value.int i, hvE, rfl⟩)
      show negLit (Atom.intNe s i) ∈ litPool orig
      exact negLit_mem (List.mem_append_left _
        (slotAtomPool_mem_atomPoolBase hs ha))
  | setOfInt _ => simp [valueLiteral] at hl
  | array _ => simp [valueLiteral] at hl


/-! ## §2 The synchronised literals are pooled -/

/-- Order literals at a threshold of the slot's own domain are pooled. -/
theorem order_mem_litPool {orig : List Domain} {s : Nat} {k : Int}
    (hs : s < orig.length) (hk : k ∈ threshPool (orig.getD s Dom.empty)) :
    posLe s k ∈ litPool orig ∧ negLe s k ∈ litPool orig := by
  have ha : Atom.intLe s k ∈ slotAtomPool s (orig.getD s Dom.empty) :=
    List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, hk, rfl⟩))
  have hb : Atom.intLe s k ∈ atomPool orig :=
    List.mem_append_left _ (slotAtomPool_mem_atomPoolBase hs ha)
  exact ⟨posLit_mem hb, negLit_mem hb⟩

theorem syncCands_mem_litPool {orig : List Domain}
    {f : BranchFrame} {s : Nat} :
    ∀ lit ∈ syncCands orig f s, lit.norm ∈ litPool orig := by
  intro lit hlit
  obtain ⟨hs, d, -, h⟩ := syncCands_cases hlit
  rcases h with ⟨lo, -, hlo, rfl⟩ | ⟨hi, -, hhi, rfl⟩ | ⟨i, -, hi, rfl⟩ | ⟨b, -, rfl⟩ |
    ⟨lo, hi, h0, -, -, hh0, rfl⟩
  · exact (order_mem_litPool hs (pred_mem_threshPool hlo)).2
  · exact (order_mem_litPool hs (self_mem_threshPool hhi)).1
  · have ha : Atom.intNe s i ∈ slotAtomPool s (orig.getD s Dom.empty) :=
      intNe_mem_slotAtomPool hi
    have hb : Atom.intNe s i ∈ atomPool orig :=
      List.mem_append_left _ (slotAtomPool_mem_atomPoolBase hs ha)
    exact negLit_mem hb
  · have ha : Atom.boolEq s b ∈ slotAtomPool s (orig.getD s Dom.empty) :=
      boolEq_mem_slotAtomPool s _ b
    have hb : Atom.boolEq s b ∈ atomPool orig :=
      List.mem_append_left _ (slotAtomPool_mem_atomPoolBase hs ha)
    exact posLit_mem hb
  · have ha : Atom.intNe s h0 ∈ slotAtomPool s (orig.getD s Dom.empty) :=
      intNe_mem_slotAtomPool hh0
    have hb : Atom.intNe s h0 ∈ atomPool orig :=
      List.mem_append_left _ (slotAtomPool_mem_atomPoolBase hs ha)
    exact posLit_mem hb

/-- `syncSlot` only adds pooled entries (at any pool containing `litPool`). -/
theorem syncSlot_trail_vocab {leaf : Assignment → Bool} {orig : List Domain}
    (bs : BranchState leaf) (s : Nat)
    {P : List Literal} (hP : ∀ l ∈ litPool orig, l ∈ P)
    (hbs : ∀ e ∈ bs.trail, e.literal.norm ∈ P) :
    ∀ e ∈ (syncSlot orig bs s).trail, e.literal.norm ∈ P :=
  syncSlot_trail_prop orig bs s (Q := fun l => l.norm ∈ P)
    (fun lit hlit => by
      simpa [Literal.norm_idem] using hP _ (syncCands_mem_litPool lit hlit))
    hbs

theorem syncAll_trail_vocab {leaf : Assignment → Bool} {orig : List Domain}
    (bs : BranchState leaf)
    {P : List Literal} (hP : ∀ l ∈ litPool orig, l ∈ P)
    (hbs : ∀ e ∈ bs.trail, e.literal.norm ∈ P) :
    ∀ e ∈ (syncAll orig bs).trail, e.literal.norm ∈ P :=
  syncAll_trail_prop orig bs (Q := fun l => l.norm ∈ P)
    (fun i _ lit hlit => by
      simpa [Literal.norm_idem] using hP _ (syncCands_mem_litPool lit hlit))
    hbs

end LeanFzn.Solver.UIP

/-
File: LeanFzn/Solver/UIP/LiteralPool.lean

Purpose:
  The finite literal pool of a fixed input, in a module BELOW
  `SchedulerState` so the scheduler initializer can prime its runtime
  membership cache (`PoolCache`) without importing the proof-layer
  `Proofs/SchedulerVocabulary.lean`.  The definitions are the landed
  pool vocabulary (moved verbatim out of SchedulerVocabulary): the
  threshold representative set, the slot/atom pools, the Boolean-flip
  image, and the four-polarity literal pool.  All pool theorems remain in
  `SchedulerVocabulary`, which imports this module transitively through
  `SchedulerState`.

Dependencies:
  - LeanFzn.Solver.Propagation.Operations: `Value.intView`, `Literal`,
    `memIntViewB`.
  - Std.Data.HashSet: the learned-key index (`hashSetOfList`).  The pool
    cache itself is structural (no hash set of the 13M-literal pool).

DAG:
  Operations -> LiteralPool -> SchedulerState -> SchedulerVocabulary.
-/

import LeanFzn.Solver.Propagation.Operations
import Std.Data.HashSet
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

/-! ## The finite threshold representative set -/

/-- Integer view of a domain, in order. -/
def vocabDomInts (d : Domain) : List Int := (Dom.enum d).filterMap Value.intView

/-- Finite representative set of order thresholds for one slot: the
    domain's integer values plus their predecessors (the `lo - 1` shape
    and the `min - 1` sentinel). -/
def threshPool (d : Domain) : List Int :=
  vocabDomInts d ++ (vocabDomInts d).map (fun i => i - 1)

/-! ## The finite literal pool -/

/-- Flip the Boolean value of a pin; identity on order and removal atoms.
    Pooling this image explicitly keeps `Literal.norm` of a negative
    Boolean pin inside the pool without any index inversion. -/
def _root_.LeanFzn.Solver.Propagation.Atom.boolFlip : Atom → Atom
  | .boolEq s b => .boolEq s (!b)
  | a => a

/-- Atoms attachable to one slot from one domain: Boolean pins in both
    polarities at every slot, order atoms at the representative
    thresholds, and value-removal atoms at the domain's integer values. -/
def slotAtomPool (s : Nat) (d : Domain) : List Atom :=
  [Atom.boolEq s true, Atom.boolEq s false]
    ++ (threshPool d).map (Atom.intLe s)
    ++ (vocabDomInts d).map (Atom.intNe s)

/-- Atom pool of a list of domains, indexed by slot position. -/
def atomPoolBase (s : Nat) : List Domain → List Atom
  | [] => []
  | d :: ds => slotAtomPool s d ++ atomPoolBase (s + 1) ds

/-- Atom pool of a fixed input, closed under `Atom.boolFlip` by
    construction (the flip image is appended explicitly), so no index
    inversion is needed to flip a pooled pin. -/
def atomPool (orig : List Domain) : List Atom :=
  atomPoolBase 0 orig ++ (atomPoolBase 0 orig).map Atom.boolFlip

/-! ### Pool constructor blocks -/

def posLit (a : Atom) : Literal := ⟨a, true⟩

def negLit (a : Atom) : Literal := ⟨a, false⟩

def flipPosLit (a : Atom) : Literal := ⟨a.boolFlip, true⟩

def flipNegLit (a : Atom) : Literal := ⟨a.boolFlip, false⟩

/-- Literal pool: positive and negative blocks, plus the Boolean-flip
    image (normal forms of negative Boolean pins) in both polarities.
    Every atom occurs in both polarities; `atomPool` is flip-closed, so
    the flip blocks are closed too. -/
def litPool (orig : List Domain) : List Literal :=
  (atomPool orig).map posLit ++ (atomPool orig).map negLit
    ++ (atomPool orig).map flipPosLit ++ (atomPool orig).map flipNegLit

/-! ## The executable membership cache -/

/-- Build a hash set from a list (last occurrence wins; membership is the
    list membership). -/
def hashSetOfList {α : Type} [BEq α] [Hashable α] (xs : List α) :
    Std.HashSet α :=
  xs.foldl (fun s x => s.insert x) ∅

theorem hashSetOfList_mem {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (xs : List α) (x : α) :
    x ∈ hashSetOfList xs ↔ x ∈ xs := by
  unfold hashSetOfList
  suffices h : ∀ (s : Std.HashSet α) (ys : List α),
      x ∈ ys.foldl (fun s y => s.insert y) s ↔ x ∈ s ∨ x ∈ ys by
    rw [h]
    simp
  intro s ys
  induction ys generalizing s with
  | nil => simp
  | cons y ys ih =>
      have hb : ((y == x) = true) ↔ x = y := by
        rw [beq_iff_eq, eq_comm]
      simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, hb]
      grind

/-! ### Structural pool membership

The eager `Std.HashSet` of `litPool orig` has about 24 literals per domain
value, so it is quadratic on wide-domain instances.  The only operation the
scheduler performs on the cache is `contains`, and the exact answer is
structural: a literal is pooled iff its atom (or its Boolean flip) occurs in
the slot-indexed base atom pool, and base membership has a closed form in
terms of the domain's integer view.  The cache below computes that form
directly from `orig`, without materialising any of the pool lists. -/

/-- The parts of an atom that membership in `slotAtomPool` checks besides the
slot: Boolean pins are always present; `intLe u` is present iff `u` or `u+1`
is in the domain's integer view; `intNe v` iff `v` is. -/
def atomShape (d : Domain) : Atom → Bool
  | .boolEq _ _ => true
  | .intLe _ u => memIntViewB d u || memIntViewB d (u + 1)
  | .intNe _ v => memIntViewB d v

/-- The slot of an atom, as a local projection (`LiteralPool` sits below the
`Encoding` module that defines the shared one). -/
def atomSlot : Atom → Nat
  | .boolEq s _ => s
  | .intLe s _ => s
  | .intNe s _ => s

@[simp] theorem atomSlot_boolFlip (a : Atom) : atomSlot a.boolFlip = atomSlot a := by
  cases a <;> rfl

@[simp] theorem atomShape_boolFlip (d : Domain) (a : Atom) :
    atomShape d a.boolFlip = atomShape d a := by
  cases a <;> rfl

theorem _root_.LeanFzn.Solver.Propagation.Atom.boolFlip_boolFlip (a : Atom) :
    a.boolFlip.boolFlip = a := by
  cases a with
  | boolEq s b => cases b <;> rfl
  | intLe s u => rfl
  | intNe s v => rfl

/-- Membership in the slot-indexed atom pool, structurally: walk the domains
keeping the slot count, so each atom's shape is tested only at its own slot
(the `&&` short-circuits the shape test for the other slots). -/
def atomPoolContainsAux (s : Nat) : List Domain → Atom → Bool
  | [], _ => false
  | d :: ds, a => (atomSlot a == s && atomShape d a) || atomPoolContainsAux (s + 1) ds a

/-- Membership in `atomPoolBase 0 orig`, without materialising the pool. -/
def atomPoolContains (orig : List Domain) (a : Atom) : Bool :=
  atomPoolContainsAux 0 orig a

/-- The pool-membership cache of a fixed input: the original box together
with its structural membership test. -/
structure PoolCache where
  orig : List Domain
  contains : Literal → Bool

/-- Membership in `litPool orig`: the atom or its Boolean flip occurs in the
base atom pool (each in either polarity). -/
def poolContains (orig : List Domain) (x : Literal) : Bool :=
  atomPoolContains orig x.atom || atomPoolContains orig x.atom.boolFlip

/-- The pool membership cache of a fixed input. -/
def litPoolHash (orig : List Domain) : PoolCache :=
  { orig := orig, contains := poolContains orig }

/-! ### Exactness of the structural cache -/

/-- Membership in `threshPool` in terms of the domain's integer view: either
the threshold itself or its successor is a domain value. -/
theorem threshPool_mem_iff {d : Domain} {u : Int} :
    u ∈ threshPool d ↔ u ∈ vocabDomInts d ∨ u + 1 ∈ vocabDomInts d := by
  unfold threshPool
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨v, hv, hv'⟩)
    · exact Or.inl h
    · have hv'' : v = u + 1 := by omega
      exact Or.inr (hv'' ▸ hv)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨u + 1, h, by omega⟩

/-- The slot-indexed atom pool is exactly the structural slot/shape test. -/
theorem slotAtomPool_mem_iff (s : Nat) (d : Domain) (a : Atom) :
    a ∈ slotAtomPool s d ↔ atomSlot a = s ∧ atomShape d a = true := by
  cases a with
  | boolEq s' b =>
      cases b <;> simp [slotAtomPool, atomSlot, atomShape]
  | intLe s' u =>
      constructor
      · intro h
        rw [slotAtomPool, List.mem_append, List.mem_append] at h
        rcases h with (h | h) | h
        · simp at h
        · rcases List.mem_map.mp h with ⟨u', hu', he⟩
          obtain ⟨hs', hu⟩ := Atom.intLe.inj he
          refine ⟨?_, ?_⟩
          · simpa [atomSlot] using hs'.symm
          · rw [← hu, atomShape, Bool.or_eq_true]
            exact (threshPool_mem_iff.mp hu').elim
              (fun hv => Or.inl (by
                simpa [vocabDomInts] using (memIntViewB_iff_intView d u').mpr hv))
              (fun hv => Or.inr (by
                simpa [vocabDomInts] using (memIntViewB_iff_intView d (u' + 1)).mpr hv))
        · simp at h
      · rintro ⟨hs', hshape⟩
        have hs'' : s' = s := by simpa [atomSlot] using hs'
        rw [hs'', slotAtomPool, List.mem_append, List.mem_append]
        refine Or.inl (Or.inr ?_)
        apply List.mem_map_of_mem (f := Atom.intLe s)
        rw [atomShape, Bool.or_eq_true] at hshape
        have hv : u ∈ vocabDomInts d ∨ u + 1 ∈ vocabDomInts d :=
          hshape.elim
            (fun h => Or.inl (by
              simpa [vocabDomInts] using (memIntViewB_iff_intView d u).mp h))
            (fun h => Or.inr (by
              simpa [vocabDomInts] using (memIntViewB_iff_intView d (u + 1)).mp h))
        simpa [vocabDomInts] using threshPool_mem_iff.mpr hv
  | intNe s' v =>
      constructor
      · intro h
        rw [slotAtomPool, List.mem_append, List.mem_append] at h
        rcases h with (h | h) | h
        · simp at h
        · rcases List.mem_map.mp h with ⟨u', hu', he⟩
          cases he
        · rcases List.mem_map.mp h with ⟨v', hv', he⟩
          obtain ⟨hs', hv⟩ := Atom.intNe.inj he
          refine ⟨?_, ?_⟩
          · simpa [atomSlot] using hs'.symm
          · rw [← hv]
            show memIntViewB d v' = true
            simpa [vocabDomInts] using (memIntViewB_iff_intView d v').mpr hv'
      · rintro ⟨hs', hshape⟩
        have hs'' : s' = s := by simpa [atomSlot] using hs'
        rw [hs'', slotAtomPool, List.mem_append, List.mem_append]
        refine Or.inr ?_
        apply List.mem_map_of_mem (f := Atom.intNe s)
        show v ∈ vocabDomInts d
        simpa [vocabDomInts] using (memIntViewB_iff_intView d v).mp hshape

/-- `slotAtomPool` is closed under the Boolean flip. -/
theorem slotAtomPool_boolFlip_mem {s : Nat} {d : Domain} {a : Atom}
    (h : a ∈ slotAtomPool s d) : a.boolFlip ∈ slotAtomPool s d := by
  rw [slotAtomPool_mem_iff] at h ⊢
  exact ⟨by simpa using h.1, by simpa using h.2⟩

/-- `atomPoolBase` is closed under the Boolean flip. -/
theorem atomPoolBase_boolFlip_mem {s : Nat} {ds : List Domain} {a : Atom}
    (h : a ∈ atomPoolBase s ds) : a.boolFlip ∈ atomPoolBase s ds := by
  induction ds generalizing s with
  | nil => simp [atomPoolBase] at h
  | cons d ds ih =>
      rw [atomPoolBase] at h ⊢
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (slotAtomPool_boolFlip_mem h)
      · exact List.mem_append_right _ (ih (s := s + 1) h)

theorem atomPoolContainsAux_eq (s : Nat) (ds : List Domain) (a : Atom) :
    atomPoolContainsAux s ds a = decide (a ∈ atomPoolBase s ds) := by
  induction ds generalizing s with
  | nil => simp [atomPoolContainsAux, atomPoolBase]
  | cons d ds ih =>
      have hhead : (atomSlot a == s && atomShape d a)
          = decide (a ∈ slotAtomPool s d) := by
        rw [Bool.eq_iff_iff, decide_eq_true_eq, slotAtomPool_mem_iff,
          Bool.and_eq_true, beq_iff_eq]
      simp only [atomPoolContainsAux, atomPoolBase, List.mem_append, Bool.decide_or,
        ih (s + 1), hhead]

/-- A flip-image membership is the flip of a base membership. -/
theorem exists_mem_boolFlip_eq {l : List Atom} {a : Atom} :
    (∃ b, b ∈ l ∧ b.boolFlip = a) ↔ a.boolFlip ∈ l := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [Atom.boolFlip_boolFlip] using hb
  · intro h
    exact ⟨a.boolFlip, h, by simp [Atom.boolFlip_boolFlip]⟩

/-- `atomPool` membership is exactly base-pool membership (the explicit flip
image adds nothing because the base pool is already flip-closed). -/
theorem atomPool_mem_iff (orig : List Domain) (a : Atom) :
    a ∈ atomPool orig ↔ a ∈ atomPoolBase 0 orig := by
  rw [atomPool, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨b, hb, hflip⟩)
    · exact h
    · have hb' : a.boolFlip ∈ atomPoolBase 0 orig := by
        have hb'' : b = a.boolFlip := by
          simpa [Atom.boolFlip_boolFlip] using congrArg Atom.boolFlip hflip
        rwa [hb''] at hb
      simpa [Atom.boolFlip_boolFlip] using atomPoolBase_boolFlip_mem hb'
  · exact Or.inl

/-- The four polarity blocks flatten to: the atom or its flip is a base atom. -/
theorem mem_litPool_blocks (orig : List Domain) (a : Atom) (p : Bool) :
    (⟨a, p⟩ : Literal) ∈ litPool orig ↔
      a ∈ atomPool orig ∨ a.boolFlip ∈ atomPool orig := by
  cases p <;>
    simp [litPool, List.mem_append, List.mem_map, posLit, negLit, flipPosLit,
      flipNegLit, exists_mem_boolFlip_eq]

/-- Exact membership in `litPool` in terms of the base atom pool. -/
theorem litPool_mem_iff (orig : List Domain) (x : Literal) :
    x ∈ litPool orig ↔
      x.atom ∈ atomPoolBase 0 orig ∨ x.atom.boolFlip ∈ atomPoolBase 0 orig := by
  obtain ⟨a, p⟩ := x
  rw [mem_litPool_blocks, atomPool_mem_iff, atomPool_mem_iff]

/-- The structural cache is exactly the reference pool membership. -/
theorem poolContains_eq (orig : List Domain) (x : Literal) :
    poolContains orig x = decide (x ∈ litPool orig) := by
  obtain ⟨a, p⟩ := x
  rw [poolContains, atomPoolContains, atomPoolContains,
    atomPoolContainsAux_eq, atomPoolContainsAux_eq, ← Bool.decide_or,
    decide_eq_decide]
  exact (litPool_mem_iff orig ⟨a, p⟩).symm

theorem litPoolHash_contains (orig : List Domain) (x : Literal) :
    (litPoolHash orig).contains x = decide (x ∈ litPool orig) :=
  poolContains_eq orig x


/-! ## The order-insensitive mask key

The novelty guard's reference test compares the SET of pool literals of a
candidate with those of each learned clause. `clauseKeyWith` is a cheap
necessary invariant of that set: a Bloom-style mask recording which hash
buckets occur. Equal sets have equal keys (`clauseKeyWith_eq_of_mem_iff`),
so a hash set of database keys can reject a non-repeat without scanning the
database; hits fall back to the exact list test. -/

/-- The hash-bucket mask of a literal list: bucket `i` is set iff some
literal hashes into it.  Order- and duplicate-insensitive.  The literal
hashes are computed once per call. -/
def litMask (width : Nat) (l : List Literal) : List Bool :=
  let hs := l.map fun x => (hash x).toNat
  (List.range width).map fun i => hs.any fun h => h % width == i

theorem litMask_eq_of_mem_iff {width : Nat} {l m : List Literal}
    (h : ∀ x, x ∈ l ↔ x ∈ m) : litMask width l = litMask width m := by
  have hany : ∀ p : Nat → Bool,
      (l.map fun x => (hash x).toNat).any p
        = (m.map fun x => (hash x).toNat).any p := by
    intro p
    by_cases hl : (l.map fun x => (hash x).toNat).any p = true
    · have hm : (m.map fun x => (hash x).toNat).any p = true := by
        rw [List.any_eq_true] at hl ⊢
        obtain ⟨y, hy, hp⟩ := hl
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact ⟨(hash x).toNat, List.mem_map.mpr ⟨x, (h x).mp hx, rfl⟩, hp⟩
      rw [hl, hm]
    · have hl' : (l.map fun x => (hash x).toNat).any p = false :=
        Bool.eq_false_iff.mpr hl
      have hm : (m.map fun x => (hash x).toNat).any p = false := by
        rw [Bool.eq_false_iff]
        intro hm'
        rw [List.any_eq_true] at hm'
        obtain ⟨y, hy, hp⟩ := hm'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have hlt : (l.map fun x => (hash x).toNat).any p = true := by
          rw [List.any_eq_true]
          exact ⟨(hash x).toNat, List.mem_map.mpr ⟨x, (h x).mpr hx, rfl⟩, hp⟩
        exact hl hlt
      rw [hl', hm]
  unfold litMask
  dsimp only
  apply List.map_congr_left
  intro i _
  exact hany _

/-- The order-insensitive key of an already-normalized clause against a
pool-membership cache. -/
def clauseKeyWith (pool : PoolCache) (c : Clause) : List Bool :=
  litMask 64 (c.filter fun x => pool.contains x)

theorem clauseKeyWith_eq_of_mem_iff {pool : PoolCache} {c d : Clause}
    (h : ∀ x, x ∈ c.filter (fun x => pool.contains x) ↔
      x ∈ d.filter (fun x => pool.contains x)) :
    clauseKeyWith pool c = clauseKeyWith pool d :=
  litMask_eq_of_mem_iff h

/-- Insert the keys of a list of normalized clauses into an index. -/
def insertClauseKeys (pool : PoolCache) (s : Std.HashSet (List Bool))
    (cs : List Clause) : Std.HashSet (List Bool) :=
  cs.foldl (fun s c => s.insert (clauseKeyWith pool c)) s

theorem insertClauseKeys_contains_of_contains {pool : PoolCache}
    {s : Std.HashSet (List Bool)} {cs : List Clause} {k : List Bool}
    (h : s.contains k = true) : (insertClauseKeys pool s cs).contains k = true := by
  unfold insertClauseKeys
  induction cs generalizing s with
  | nil => simpa using h
  | cons c cs ih =>
      simp only [List.foldl_cons]
      exact ih (s := s.insert (clauseKeyWith pool c)) (by
        rw [Std.HashSet.contains_iff_mem] at h ⊢
        exact Std.HashSet.mem_insert.mpr (Or.inr h))

theorem insertClauseKeys_contains_clause {pool : PoolCache}
    {s : Std.HashSet (List Bool)} {cs : List Clause} {c : Clause} (hc : c ∈ cs) :
    (insertClauseKeys pool s cs).contains (clauseKeyWith pool c) = true := by
  unfold insertClauseKeys
  induction cs generalizing s with
  | nil => cases hc
  | cons a t ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact insertClauseKeys_contains_of_contains (cs := t)
          (by rw [Std.HashSet.contains_iff_mem]
              exact Std.HashSet.mem_insert.mpr (Or.inl (beq_iff_eq.mpr rfl)))
      · exact ih hc

end LeanFzn.Solver.UIP
/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerVocabulary.lean

Purpose (PLAN.md task P1, prereq R1):
  Canonical clause identity and a finite literal/clause pool for a FIXED
  input, with proved closure under literal normalization and negation and
  explicit size bounds. This file is the feasibility gate for P2/P3.

  * `Clause.canonicalClause` — normalize every literal (order-level dedup
    is NOT folded in; see the note there). PROVED: idempotence and the
    normalization-reflection laws.
  * `litPool` — finite pool of literals derivable from the input domains:
    Boolean pins for bool-valued slots in both polarities plus an explicit
    Boolean-flip block (so `Literal.norm` of a negative pin stays inside),
    order atoms `intLe s k` at `k ∈ threshPool d`, and value-removal atoms
    `intNe s i` for `i ∈ vocabDomInts d` (the decision vocabulary
    `valueLiteral`/`splitData` emits `negNe s i` for `.int i`).
  * `threshPool d = vocabDomInts d ++ (vocabDomInts d).map (· - 1)` — the finite
    representative set of order thresholds. `orderUpgrade` emits only two
    threshold shapes: `hi` read directly from a positive trail literal,
    and `lo - 1` where `lo` is a foldl-max of `k + 1` over negative trail
    literals `intLe s k`; the `+1` never escapes because it is immediately
    decremented, so emitted thresholds are the trail's own thresholds.
    The genuinely new threshold is `min - 1` ("above everything in the
    domain"), and `pred_mem_threshPool` shows it is included.

  The pool DEFINITIONS (`vocabDomInts`, `threshPool`, `slotAtomPool`,
  `atomPool`, `litPool` and the literal constructors) live in
  `LeanFzn.Solver.UIP.LiteralPool`, below `SchedulerState`, so the scheduler
  initializer can prime `poolHash`; they are moved verbatim and remain in
  this namespace. All pool theorems stay in this file.

  PROVED here: `Literal.norm_idem`, canonical idempotence and reflection,
  pool closure under `norm` and `negate`, all size bounds, the clause-pool
  powerset bound, the pool-membership direction for clause-pool members,
  and the concrete threshold witness that domain values alone are NOT a
  closed representative set. OBLIGATIONS (owner-tagged) are listed at the
  end of the file.

Dependencies:
  - LeanFzn.Solver.Propagation.Operations: `Value.intView`, `Literal.norm`, literals.
  - LeanFzn.Solver.UIP.SchedulerState (transitively `UIP.LiteralPool`).

DAG:
  Operations -> LiteralPool -> SchedulerState -> SchedulerVocabulary
-/

import LeanFzn.Solver.Propagation.Operations
import LeanFzn.Legacy.Solver.UIP.SchedulerState
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Canonical clause form -/

/-- Normalize a clause literal-wise. `List.map` cannot remove duplicates,
    so canonical identity is "same normalized literal sequence"; the
    database bound below is over a pool closed under the sublist
    enumeration, so duplicate shapes are harmless for the counting
    argument. -/
def _root_.LeanFzn.Solver.Propagation.Clause.canonicalClause (c : Clause) : Clause := c.map Literal.norm

/-- Normalization of a literal is idempotent. -/
theorem _root_.LeanFzn.Solver.Propagation.Literal.norm_idem (l : Literal) : l.norm.norm = l.norm := by
  cases l with
  | mk atom positive =>
      cases atom <;> simp [Literal.norm]
      case boolEq s b =>
          cases positive <;> simp

/-- Canonical form is idempotent. -/
theorem _root_.LeanFzn.Solver.Propagation.Clause.canonicalClause_idem (c : Clause) :
    c.canonicalClause.canonicalClause = c.canonicalClause := by
  simp [Clause.canonicalClause, List.map_map, Function.comp_def,
    Literal.norm_idem]

/-- Equality reflection: a clause that is already normalized is its own
    canonical form. -/
theorem _root_.LeanFzn.Solver.Propagation.Clause.canonicalClause_eq_self {c : Clause}
    (h : c.map Literal.norm = c) : c.canonicalClause = c := h

/-- Normalization does not change the canonical form: canonicity is a
    congruence for the canonical identity. -/
theorem _root_.LeanFzn.Solver.Propagation.Clause.canonicalClause_map_norm (c : Clause) :
    Clause.canonicalClause (c.map Literal.norm) = c.canonicalClause := by
  simp [Clause.canonicalClause, List.map_map, Function.comp_def,
    Literal.norm_idem]

/-! ## The finite threshold representative set -/

/-- Every domain value is a representative. -/
theorem self_mem_threshPool {d : Domain} {i : Int} (h : i ∈ vocabDomInts d) :
    i ∈ threshPool d :=
  List.mem_append_left _ h

/-- Every predecessor of a domain value is a representative. -/
theorem pred_mem_threshPool {d : Domain} {i : Int} (h : i ∈ vocabDomInts d) :
    i - 1 ∈ threshPool d :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, h, rfl⟩)

/-- CONCRETE WITNESS (feasibility evidence): for the single-value domain
    `[5]`, the threshold `4` is required by an upgrade-shaped literal
    (`lo - 1` with `lo = 5`) but is NOT a domain value, so finiteness of
    the domains alone does not bound the threshold vocabulary — the
    representative set must carry the predecessor forms. -/
theorem thresh_witness_domain_not_closed :
    (4 : Int) ∉ vocabDomInts (Dom.ofList [Value.int 5]) ∧
      (4 : Int) ∈ threshPool (Dom.ofList [Value.int 5]) := by
  constructor
  · decide
  · exact pred_mem_threshPool
      (List.mem_filterMap.mpr ⟨Value.int 5, by simp, rfl⟩)

/-! ## The finite literal pool -/

theorem _root_.LeanFzn.Solver.Propagation.Atom.boolFlip_invol (a : Atom) : a.boolFlip.boolFlip = a := by
  cases a with
  | boolEq s b => cases b <;> simp [Atom.boolFlip]
  | intLe s k => rfl
  | intNe s k => rfl

/-- The atom pool is closed under the Boolean flip. -/
theorem atomPool_boolFlip_mem {orig : List Domain} {a : Atom}
    (h : a ∈ atomPool orig) : a.boolFlip ∈ atomPool orig := by
  rw [atomPool] at h ⊢
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ (List.mem_map_of_mem (f := Atom.boolFlip) h)
  · rcases List.mem_map.mp h with ⟨a', ha', he⟩
    rw [← he, Atom.boolFlip_invol]
    exact List.mem_append_left _ ha'

/-! ### Pool constructor blocks -/

theorem posLit_mem {orig : List Domain} {a : Atom}
    (ha : a ∈ atomPool orig) : posLit a ∈ litPool orig := by
  rw [litPool]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (f := posLit) ha)))

theorem negLit_mem {orig : List Domain} {a : Atom}
    (ha : a ∈ atomPool orig) : negLit a ∈ litPool orig := by
  rw [litPool]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := negLit) ha)))

theorem flipPosLit_mem {orig : List Domain} {a : Atom}
    (ha : a ∈ atomPool orig) : flipPosLit a ∈ litPool orig := by
  rw [litPool]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := flipPosLit) ha))

theorem flipNegLit_mem {orig : List Domain} {a : Atom}
    (ha : a ∈ atomPool orig) : flipNegLit a ∈ litPool orig := by
  rw [litPool]
  exact List.mem_append_right _ (List.mem_map_of_mem (f := flipNegLit) ha)

/-- `norm` of a pool literal is a pool literal. -/
theorem litPool_norm_closed {orig : List Domain} {l : Literal}
    (h : l ∈ litPool orig) : l.norm ∈ litPool orig := by
  rw [litPool] at h
  rcases List.mem_append.mp h with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · -- positive block: already normal
        rcases List.mem_map.mp h1 with ⟨a, ha, he⟩
        rw [← he]
        cases a <;> simpa [posLit, Literal.norm] using posLit_mem ha
      · -- negative block
        rcases List.mem_map.mp h2 with ⟨a, ha, he⟩
        rw [← he]
        cases a
        · -- Boolean pin: normalizes into the flip-positive block
          simpa [negLit, flipPosLit, Atom.boolFlip, Literal.norm]
            using flipPosLit_mem ha
        · simpa [negLit, Literal.norm] using negLit_mem ha
        · simpa [negLit, Literal.norm] using negLit_mem ha
    · -- flip-positive block
      rcases List.mem_map.mp h3 with ⟨a, ha, he⟩
      rw [← he]
      cases a
      · simpa [flipPosLit, Atom.boolFlip, Literal.norm] using flipPosLit_mem ha
      · simpa [flipPosLit, posLit, Atom.boolFlip, Literal.norm]
          using posLit_mem ha
      · simpa [flipPosLit, posLit, Atom.boolFlip, Literal.norm]
          using posLit_mem ha
  · -- flip-negative block
    rcases List.mem_map.mp h4 with ⟨a, ha, he⟩
    rw [← he]
    cases a
    · -- double flip returns to the original pin
      simpa [flipNegLit, posLit, Atom.boolFlip, Literal.norm, Bool.not_not]
        using posLit_mem ha
    · simpa [flipNegLit, negLit, Atom.boolFlip, Literal.norm]
        using negLit_mem ha
    · simpa [flipNegLit, negLit, Atom.boolFlip, Literal.norm]
        using negLit_mem ha

/-- `negate` of a pool literal is a pool literal. -/
theorem litPool_negate_closed {orig : List Domain} {l : Literal}
    (h : l ∈ litPool orig) : l.negate ∈ litPool orig := by
  rw [litPool] at h
  rcases List.mem_append.mp h with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · rcases List.mem_map.mp h1 with ⟨a, ha, he⟩
        rw [← he]
        simpa [posLit, negLit, Literal.negate, Bool.not_true]
          using negLit_mem ha
      · rcases List.mem_map.mp h2 with ⟨a, ha, he⟩
        rw [← he]
        simpa [posLit, negLit, Literal.negate, Bool.not_false]
          using posLit_mem ha
    · rcases List.mem_map.mp h3 with ⟨a, ha, he⟩
      rw [← he]
      simpa [flipPosLit, flipNegLit, Literal.negate, Bool.not_true]
        using flipNegLit_mem ha
  · rcases List.mem_map.mp h4 with ⟨a, ha, he⟩
    rw [← he]
    simpa [flipPosLit, flipNegLit, Literal.negate, Bool.not_false]
      using flipPosLit_mem ha

/-! ## Size bounds -/

theorem domInts_length_le (d : Domain) : (vocabDomInts d).length ≤ d.length := by
  unfold vocabDomInts
  rw [Dom.length_eq_enum]
  exact List.length_filterMap_le _ _

theorem slotAtomPool_length_le (s : Nat) (d : Domain) :
    (slotAtomPool s d).length ≤ 3 * (vocabDomInts d).length + 2 := by
  have h1 : (threshPool d).length ≤ 2 * (vocabDomInts d).length := by
    simp only [threshPool, List.length_append, List.length_map]
    omega
  simp only [slotAtomPool, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

theorem atomPoolBase_length_le (s : Nat) (ds : List Domain) :
    (atomPoolBase s ds).length ≤ 3 * (ds.map (fun d => d.length)).sum + 2 * ds.length := by
  induction ds generalizing s with
  | nil => simp [atomPoolBase]
  | cons d ds ih =>
      have h := slotAtomPool_length_le s d
      have hle := domInts_length_le d
      have ih' := ih (s + 1)
      simp only [atomPoolBase, List.length_append, List.map_cons,
        List.sum_cons, List.length_cons]
      omega

theorem atomPool_length_le (orig : List Domain) :
    (atomPool orig).length ≤ 2 * (3 * (orig.map (fun d => d.length)).sum + 2 * orig.length) := by
  have h := atomPoolBase_length_le 0 orig
  simp only [atomPool, List.length_append, List.length_map]
  omega

/-- Literal pool size bound: four blocks over the atom pool. -/
theorem litPool_length_le (orig : List Domain) :
    (litPool orig).length ≤ 4 * (2 * (3 * (orig.map (fun d => d.length)).sum + 2 * orig.length)) := by
  simp only [litPool, List.length_append, List.length_map]
  have h := atomPool_length_le orig
  omega

/-- Readable form: at most twenty-four literals per stored value plus
    sixteen per slot. -/
theorem litPool_length_le' (orig : List Domain) :
    (litPool orig).length ≤ 24 * (orig.map (fun d => d.length)).sum + 16 * orig.length := by
  have h := litPool_length_le orig
  omega

/-! ## Clause pool and database bound -/

/-- Powerset enumeration of a literal list (local: this core version has
    no `List.sublists`). -/
def sublistsOf : List Literal → List Clause
  | [] => [[]]
  | a :: L => sublistsOf L ++ (sublistsOf L).map (a :: ·)

/-- The clause pool: all clauses over the literal pool. Its length is
    exactly `2 ^ |litPool|`. -/
def clausePool (orig : List Domain) : List Clause := sublistsOf (litPool orig)

theorem sublistsOf_length (L : List Literal) :
    (sublistsOf L).length = 2 ^ L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [sublistsOf, List.length_append, List.length_map, ih,
        List.length_cons]
      rw [Nat.pow_succ]
      omega

/-- The clause pool has exactly `2 ^ |litPool|` elements. -/
theorem clausePool_length (orig : List Domain) :
    (clausePool orig).length = 2 ^ (litPool orig).length :=
  sublistsOf_length _

/-- Sublist enumeration is sound for the subset reading. -/
theorem sublistsOf_subset_mem {L : List Literal} {c : Clause}
    (h : c ∈ sublistsOf L) : ∀ l ∈ c, l ∈ L := by
  induction L generalizing c with
  | nil =>
      simp only [sublistsOf, List.mem_singleton] at h
      subst h
      intro l hl
      cases hl
  | cons a L ih =>
      simp only [sublistsOf, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨c', hc', he⟩
      · intro l hl
        exact List.mem_cons_of_mem a (ih h l hl)
      · cases he
        intro l hl
        cases hl with
        | head => exact List.mem_cons_self ..
        | tail _ hl' => exact List.mem_cons_of_mem a (ih hc' l hl')

/-- REVERSE MEMBERSHIP DIRECTION (this is what P1-a actually needs): a
    subsequence of the literal pool is enumerated by `sublistsOf`.
    `sublistsOf` enumerates ORDER-PRESERVING sublists, so the hypothesis
    must be `List.Sublist`, NOT mere literal membership (see
    `sublistsOf_reordering_witness` below: literal membership alone is
    kernel-refuted as a sufficient condition). -/
theorem sublistsOf_mem_of_sublist {L c : List Literal} (h : List.Sublist c L) :
    c ∈ sublistsOf L :=
  List.Sublist.rec (motive := fun c L _ => c ∈ sublistsOf L)
    (by simp [sublistsOf])
    (fun a _ ih => by
      simp only [sublistsOf, List.mem_append]
      exact Or.inl ih)
    (fun a _ ih => by
      simp only [sublistsOf, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩))
    h

/-- **POOL CLOSURE, CORRECT MINIMAL SHAPE**: if the canonical form of `c`
    is a subsequence of the literal pool, then it is a clause-pool member
    — exactly the shape `hpool : Clause.canonicalClause an.learned ∈
    clausePool orig` of `Proofs/SchedulerJumpProgress` (P4). -/
theorem canonicalClause_mem_clausePool_of_sublist {orig : List Domain}
    {c : Clause} (h : List.Sublist (Clause.canonicalClause c) (litPool orig)) :
    Clause.canonicalClause c ∈ clausePool orig :=
  sublistsOf_mem_of_sublist h

/-- **ORDER-SENSITIVITY WITNESS (kernel-checked)**: literal-level
    membership `∀ l ∈ c, l ∈ L` does NOT imply `c ∈ sublistsOf L` — the
    reordered clause below has all literals in the pool but is not
    enumerated. Hence P1-a's literal-level hypothesis cannot be met by
    `canonicalClause` alone, in this `sublistsOf` pool or under
    `eraseDups` (dedup does not reorder); the analyzer side (owner P2)
    must supply `canonicalClause an.learned <+ litPool orig` from the
    `ConflictAnalysis.ofUIP` construction order, or the pool/counting
    must be re-keyed by multiset. -/
theorem sublistsOf_reordering_witness :
    (∀ l ∈ ([⟨.intLe 0 3, true⟩, ⟨.intLe 1 3, true⟩] : Clause),
        l ∈ ([⟨.intLe 1 3, true⟩, ⟨.intLe 0 3, true⟩] : Clause))
      ∧ ¬ (([⟨.intLe 0 3, true⟩, ⟨.intLe 1 3, true⟩] : Clause)
            ∈ sublistsOf ([⟨.intLe 1 3, true⟩, ⟨.intLe 0 3, true⟩] : Clause)) := by
  decide

/-- DATABASE BOUND, membership direction: every literal of a clause-pool
    member is a pool literal, so any clause database contained in
    `clausePool orig` uses only the fixed finite vocabulary. -/
theorem clausePool_lits_mem {orig : List Domain} {c : Clause}
    (h : c ∈ clausePool orig) : ∀ l ∈ c, l ∈ litPool orig :=
  sublistsOf_subset_mem h

/-- Canonicalization lands in the pool pointwise: if every literal of `c`
    is pooled, every literal of `c.canonicalClause` is pooled. Combined
    with `clausePool_lits_mem`, a database of pooled clauses stays inside
    the vocabulary; membership of the canonical form in `clausePool`
    proper is obligation P1-a below. -/
theorem canonicalClause_lits_mem {orig : List Domain} {c : Clause}
    (h : ∀ l ∈ c, l ∈ litPool orig) :
    ∀ l ∈ c.canonicalClause, l ∈ litPool orig := by
  intro l hl
  rcases List.mem_map.mp hl with ⟨l', hl', rfl⟩
  exact litPool_norm_closed (h l' hl')

/-! ## Trail vocabulary invariant (P1-a analysis-literal input, owner P2)

The analysis literals recorded by `ConflictAnalysis.ofUIP` must be pooled.
The state-side half is the invariant that every trail literal's normal
form is a pool literal; the analysis-side half is the transfer below. -/

/-- NORMALIZATION NEGATION ALGEBRA (local spelling; same law as
    `norm_negate_norm_local`, `RestorationCertificate`): negation commutes
    with normalization in the direction the pool closure needs. -/
theorem _root_.LeanFzn.Solver.Propagation.Literal.negate_norm_eq (l : Literal) :
    l.negate.norm = l.norm.negate.norm := by
  cases l with
  | mk atom positive =>
      cases atom <;> cases positive <;> simp [Literal.negate, Literal.norm]

/-- If a literal's normal form is pooled, so is the normal form of its
    negation (the `uip.negate` head of an `ofUIP` learned clause). -/
theorem litPool_negate_norm_mem {orig : List Domain} {l : Literal}
    (h : l.norm ∈ litPool orig) : l.negate.norm ∈ litPool orig := by
  rw [Literal.negate_norm_eq]
  exact litPool_norm_closed (litPool_negate_closed h)

/-- THE TRAIL VOCABULARY, stated exactly: every trail entry's normalized
    literal lies in the fixed literal pool of the input. This is the
    invariant P1-a's analysis side consumes; it is NOT yet derived from
    `SchedulerReachable` (the per-arm preservation facts are the residual
    of this file, owner S3/S5 — see the obligations block). -/
def TrailVocabulary (orig : List Domain) (trail : List TrailEntry) : Prop :=
  ∀ e ∈ trail, e.literal.norm ∈ litPool orig

theorem trailVocabulary_nil (orig : List Domain) : TrailVocabulary orig [] := by
  intro e he
  cases he

/-- Extend the vocabulary by one pooled entry (the shape of a trail
    `snoc` in `narrowState`/`BranchState.decide`). -/
theorem trailVocabulary_append_entry {orig : List Domain}
    {trail : List TrailEntry} {e : TrailEntry}
    (h : TrailVocabulary orig trail) (he : e.literal.norm ∈ litPool orig) :
    TrailVocabulary orig (trail ++ [e]) := by
  intro e' he'
  rcases List.mem_append.mp he' with h1 | h1
  · exact h e' h1
  · rcases List.mem_singleton.mp h1
    exact he

/-- Canonical shape of an `ofUIP` learned clause (definitional): the
    normalized negated UIP followed by the normalized below literals, in
    construction order. -/
theorem canonicalClause_ofUIP_learned (below : List (Literal × Nat))
    (uip : Literal) :
    Clause.canonicalClause (ConflictAnalysis.ofUIP below uip).learned
      = uip.negate.norm :: below.map (fun p => p.1.norm) := by
  simp [Clause.canonicalClause, ConflictAnalysis.ofUIP, List.map_map,
    Function.comp_def]

/-- **ANALYSIS-LITERAL TRANSFER, PROVED**: if every below-literal normal
    form and the UIP normal form are pooled, every literal of the
    canonical learned clause is pooled. This is the literal-membership
    half of P1-a, unconditional at the literal level. -/
theorem ofUIP_canonical_lits_mem {orig : List Domain}
    {below : List (Literal × Nat)} {uip : Literal}
    (hbelow : ∀ p ∈ below, p.1.norm ∈ litPool orig)
    (huip : uip.norm ∈ litPool orig) :
    ∀ l ∈ Clause.canonicalClause (ConflictAnalysis.ofUIP below uip).learned,
      l ∈ litPool orig := by
  rw [canonicalClause_ofUIP_learned]
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact litPool_negate_norm_mem huip
  · rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
    exact hbelow p hp

/-! ## P1-b: trail-bound threshold closure (owner P4, CLOSED conditionally)

`orderUpgrade` emits thresholds read off `trailLoOf`/`trailHiOf`. Both are
foldl's of `minI`/`maxI` over the trail's own `intLe` thresholds; a
min/max of two elements of a representative set is one of them, so the
emitted threshold stays in any per-slot representative set G containing
the trail's thresholds — in particular `threshPool d`. The `k + 1` form
of `trailLoOf` is handled through the invariant "accumulator is `c + 1`
with `c ∈ G`" and `maxI a (b+1) - 1 = maxI (a-1) b`. -/

/-- `minI` of two members of a representative set is a member. -/
theorem minI_mem {G : List Int} {a b : Int} (ha : a ∈ G) (hb : b ∈ G) :
    minI a b ∈ G := by
  by_cases h : a ≤ b
  · rw [minI, if_pos h]; exact ha
  · rw [minI, if_neg h]; exact hb

/-- `maxI` of two members of a representative set is a member. -/
theorem maxI_mem {G : List Int} {a b : Int} (ha : a ∈ G) (hb : b ∈ G) :
    maxI a b ∈ G := by
  by_cases h : a ≤ b
  · rw [maxI, if_pos h]; exact hb
  · rw [maxI, if_neg h]; exact ha

/-- The `k + 1` bookkeeping of `trailLoOf`: subtracting one from a
    max-fold over successors is the max-fold over the predecessors. -/
theorem maxI_succ_sub_one (a b : Int) :
    maxI a (b + 1) - 1 = maxI (a - 1) b := by
  unfold maxI
  by_cases h : a ≤ b + 1
  · rw [if_pos h, if_pos (by omega : a - 1 ≤ b)]
    omega
  · rw [if_neg h, if_neg (by omega : ¬ a - 1 ≤ b)]

/-- The `min`-fold step of `trailHiOf` as a named function. -/
def hiStep (s : Nat) (acc : Option Int) (e : TrailEntry) : Option Int :=
  match e.literal.atom with
  | .intLe s' k =>
      if s' == s && e.literal.positive then
        match acc with
        | none => some k
        | some c => some (minI c k)
      else acc
  | _ => acc

/-- The `max`-fold step of `trailLoOf` as a named function. -/
def loStep (s : Nat) (acc : Option Int) (e : TrailEntry) : Option Int :=
  match e.literal.atom with
  | .intLe s' k =>
      if s' == s && !e.literal.positive then
        match acc with
        | none => some (k + 1)
        | some c => some (maxI c (k + 1))
      else acc
  | _ => acc

def foldlHi (trail : List TrailEntry) (s : Nat) (acc : Option Int) : Option Int :=
  trail.foldl (hiStep s) acc

def foldlLo (trail : List TrailEntry) (s : Nat) (acc : Option Int) : Option Int :=
  trail.foldl (loStep s) acc

theorem trailHiOf_eq_foldlHi (trail : List TrailEntry) (s : Nat) :
    trailHiOf trail s = foldlHi trail s none := rfl

theorem trailLoOf_eq_foldlLo (trail : List TrailEntry) (s : Nat) :
    trailLoOf trail s = foldlLo trail s none := rfl

/-- One `hiStep` preserves membership of the accumulator's value. -/
theorem hiStep_mem {s : Nat} {G : List Int} {e : TrailEntry}
    {acc : Option Int} {acc' : Int}
    (hacc : ∀ c, acc = some c → c ∈ G)
    (hmem : ∀ k, e.literal.atom = .intLe s k → e.literal.positive = true →
      k ∈ G)
    (h : hiStep s acc e = some acc') : acc' ∈ G := by
  unfold hiStep at h
  cases hA : e.literal.atom with
  | intLe s' k =>
      cases hb : (s' == s) <;> cases hp : e.literal.positive
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
      · have hs' : s' = s := by simpa using hb
        subst hs'
        simp [hA, hp] at h
        cases acc with
        | none =>
            rw [Option.some.injEq] at h
            rw [← h]
            exact hmem k hA hp
        | some c =>
            rw [Option.some.injEq] at h
            rw [← h]
            exact minI_mem (hacc c rfl) (hmem k hA hp)
  | boolEq s' b =>
      have h' : acc = some acc' := by simpa [hA] using h
      exact hacc acc' h'
  | intNe s' k =>
      have h' : acc = some acc' := by simpa [hA] using h
      exact hacc acc' h'

/-- One `loStep` preserves the invariant "the accumulator is `c + 1` for
    a member `c` of the representative set". -/
theorem loStep_mem {s : Nat} {G : List Int} {e : TrailEntry}
    {acc : Option Int} {acc' : Int}
    (hacc : ∀ c, acc = some c → c - 1 ∈ G)
    (hmem : ∀ k, e.literal.atom = .intLe s k → e.literal.positive = false →
      k ∈ G)
    (h : loStep s acc e = some acc') : acc' - 1 ∈ G := by
  unfold loStep at h
  cases hA : e.literal.atom with
  | intLe s' k =>
      cases hb : (s' == s) <;> cases hp : e.literal.positive
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
      · have hs' : s' = s := by simpa using hb
        subst hs'
        simp [hA, hp] at h
        cases acc with
        | none =>
            rw [Option.some.injEq] at h
            rw [← h]
            have hk := hmem k hA hp
            have : k + 1 - 1 = k := by omega
            rwa [this]
        | some c =>
            rw [Option.some.injEq] at h
            rw [← h]
            rw [maxI_succ_sub_one]
            exact maxI_mem (hacc c rfl) (hmem k hA hp)
      · have h' : acc = some acc' := by simpa [hA, hb, hp] using h
        exact hacc acc' h'
  | boolEq s' b =>
      have h' : acc = some acc' := by simpa [hA] using h
      exact hacc acc' h'
  | intNe s' k =>
      have h' : acc = some acc' := by simpa [hA] using h
      exact hacc acc' h'

/-- A max-fold over trail thresholds with successors: the result's
    predecessor is a representative whenever every (negative) trail
    threshold at the slot is. This is the `lo - 1` output shape. -/
theorem foldlLo_mem {s : Nat} {G : List Int} :
    ∀ (trail : List TrailEntry) (acc : Option Int),
      (∀ c, acc = some c → c - 1 ∈ G) →
      (∀ e ∈ trail, ∀ k, e.literal.atom = .intLe s k →
        e.literal.positive = false → k ∈ G) →
      ∀ c, foldlLo trail s acc = some c → c - 1 ∈ G := by
  intro trail
  induction trail with
  | nil =>
      intro acc hacc _ c hc
      exact hacc c (by simpa [foldlLo] using hc)
  | cons e es ih =>
      intro acc hacc hmem c hc
      have hmem' : ∀ e' ∈ es, ∀ k, e'.literal.atom = .intLe s k →
          e'.literal.positive = false → k ∈ G :=
        fun e' he' k hk hp => hmem e' (List.mem_cons_of_mem _ he') k hk hp
      have hstep : ∀ c, loStep s acc e = some c → c - 1 ∈ G :=
        fun c hc' => loStep_mem hacc (fun k hk hp => hmem e
          (List.mem_cons_self ..) k hk hp) hc'
      exact ih (loStep s acc e) hstep hmem' c
        (by simpa [foldlLo, List.foldl_cons] using hc)

/-- A min-fold over trail thresholds: the result is a representative
    whenever every (positive) trail threshold at the slot is. -/
theorem foldlHi_mem {s : Nat} {G : List Int} :
    ∀ (trail : List TrailEntry) (acc : Option Int),
      (∀ c, acc = some c → c ∈ G) →
      (∀ e ∈ trail, ∀ k, e.literal.atom = .intLe s k →
        e.literal.positive = true → k ∈ G) →
      ∀ c, foldlHi trail s acc = some c → c ∈ G := by
  intro trail
  induction trail with
  | nil =>
      intro acc hacc _ c hc
      exact hacc c (by simpa [foldlHi] using hc)
  | cons e es ih =>
      intro acc hacc hmem c hc
      have hmem' : ∀ e' ∈ es, ∀ k, e'.literal.atom = .intLe s k →
          e'.literal.positive = true → k ∈ G :=
        fun e' he' k hk hp => hmem e' (List.mem_cons_of_mem _ he') k hk hp
      have hstep : ∀ c, hiStep s acc e = some c → c ∈ G :=
        fun c hc' => hiStep_mem hacc (fun k hk hp => hmem e
          (List.mem_cons_self ..) k hk hp) hc'
      exact ih (hiStep s acc e) hstep hmem' c
        (by simpa [foldlHi, List.foldl_cons] using hc)

/-- **P1-b, upper-bound side**: if every positive `intLe s` threshold on
    the trail lies in `G`, so does any `trailHiOf` output. -/
theorem trailHiOf_mem {trail : List TrailEntry} {s : Nat} {G : List Int}
    (hmem : ∀ e ∈ trail, ∀ k, e.literal.atom = .intLe s k →
      e.literal.positive = true → k ∈ G) :
    ∀ c, trailHiOf trail s = some c → c ∈ G := fun c hc =>
  foldlHi_mem trail none (fun c hc' => by cases hc') hmem c
    (by rwa [trailHiOf_eq_foldlHi] at hc)

/-- **P1-b, lower-bound side**: if every negative `intLe s` threshold on
    the trail lies in `G`, any `trailLoOf` output is `c + 1` with
    `c - 1 ∈ G` — exactly the `lo - 1` threshold `orderUpgrade` emits. -/
theorem trailLoOf_sub_one_mem {trail : List TrailEntry} {s : Nat}
    {G : List Int}
    (hmem : ∀ e ∈ trail, ∀ k, e.literal.atom = .intLe s k →
      e.literal.positive = false → k ∈ G) :
    ∀ c, trailLoOf trail s = some c → c - 1 ∈ G := fun c hc =>
  foldlLo_mem trail none (fun c hc' => by cases hc') hmem c
    (by rwa [trailLoOf_eq_foldlLo] at hc)

/-- **P1-b, `orderUpgrade` closure, positive `intLe`**: the output's
    threshold is the literal's own (pooled) or `lo - 1` from the trail. -/
theorem orderUpgrade_intLe_pos_mem {trail : List TrailEntry} {s : Nat}
    {G : List Int} {k : Int}
    (hlo : ∀ e ∈ trail, ∀ j, e.literal.atom = .intLe s j →
      e.literal.positive = false → j ∈ G)
    (hk : k ∈ G) :
    ∀ n, (orderUpgrade trail ⟨.intLe s k, true⟩).atom = .intLe s n →
      n ∈ G := by
  cases h : trailLoOf trail s with
  | none =>
      have hval : (orderUpgrade trail ⟨.intLe s k, true⟩).atom =
          .intLe s k := by
        simp [orderUpgrade, h]
      intro n hn
      rw [hval] at hn
      cases hn
      exact hk
  | some lo =>
      by_cases hc : lo > k
      · have hval : (orderUpgrade trail ⟨.intLe s k, true⟩).atom =
            .intLe s (lo - 1) := by
          simp [orderUpgrade, h, hc, posLe]
        intro n hn
        rw [hval] at hn
        cases hn
        exact trailLoOf_sub_one_mem hlo lo h
      · have hval : (orderUpgrade trail ⟨.intLe s k, true⟩).atom =
            .intLe s k := by
          simp [orderUpgrade, h, hc]
        intro n hn
        rw [hval] at hn
        cases hn
        exact hk

/-- **P1-b, `orderUpgrade` closure, negative `intLe`**: the output's
    threshold is the literal's own (pooled) or `hi` from the trail. -/
theorem orderUpgrade_intLe_neg_mem {trail : List TrailEntry} {s : Nat}
    {G : List Int} {k : Int}
    (hhi : ∀ e ∈ trail, ∀ j, e.literal.atom = .intLe s j →
      e.literal.positive = true → j ∈ G)
    (hk : k ∈ G) :
    ∀ n, (orderUpgrade trail ⟨.intLe s k, false⟩).atom = .intLe s n →
      n ∈ G := by
  cases h : trailHiOf trail s with
  | none =>
      have hval : (orderUpgrade trail ⟨.intLe s k, false⟩).atom =
          .intLe s k := by
        simp [orderUpgrade, h]
      intro n hn
      rw [hval] at hn
      cases hn
      exact hk
  | some hi =>
      by_cases hc : hi ≤ k
      · have hval : (orderUpgrade trail ⟨.intLe s k, false⟩).atom =
            .intLe s hi := by
          simp [orderUpgrade, h, hc, negLe]
        intro n hn
        rw [hval] at hn
        cases hn
        exact trailHiOf_mem hhi hi h
      · have hval : (orderUpgrade trail ⟨.intLe s k, false⟩).atom =
            .intLe s k := by
          simp [orderUpgrade, h, hc]
        intro n hn
        rw [hval] at hn
        cases hn
        exact hk

/-- **P1-b, `orderUpgrade` closure, positive Boolean pin**: the Boolean
    bridge emits `hi` / `lo - 1` trail thresholds; both are pooled under
    the per-slot hypotheses. -/
theorem orderUpgrade_bool_pos_mem {trail : List TrailEntry} {s : Nat}
    {G : List Int} {b : Bool}
    (hhi : ∀ e ∈ trail, ∀ j, e.literal.atom = .intLe s j →
      e.literal.positive = true → j ∈ G)
    (hlo : ∀ e ∈ trail, ∀ j, e.literal.atom = .intLe s j →
      e.literal.positive = false → j ∈ G) :
    ∀ n, (orderUpgrade trail ⟨.boolEq s b, true⟩).atom = .intLe s n →
      n ∈ G := by
  cases b
  · cases h : trailLoOf trail s with
    | none =>
        have hval : (orderUpgrade trail ⟨.boolEq s false, true⟩).atom =
            .boolEq s false := by
          simp [orderUpgrade, h]
        intro n hn
        rw [hval] at hn
        cases hn
    | some lo =>
        by_cases hc : 1 ≤ lo
        · have hval : (orderUpgrade trail ⟨.boolEq s false, true⟩).atom =
              .intLe s (lo - 1) := by
            simp [orderUpgrade, h, hc, posLe]
          intro n hn
          rw [hval] at hn
          cases hn
          exact trailLoOf_sub_one_mem hlo lo h
        · have hval : (orderUpgrade trail ⟨.boolEq s false, true⟩).atom =
              .boolEq s false := by
            simp [orderUpgrade, h, hc]
          intro n hn
          rw [hval] at hn
          cases hn
  · cases h : trailHiOf trail s with
    | none =>
        have hval : (orderUpgrade trail ⟨.boolEq s true, true⟩).atom =
            .boolEq s true := by
          simp [orderUpgrade, h]
        intro n hn
        rw [hval] at hn
        cases hn
    | some hi =>
        by_cases hc : hi ≤ 0
        · have hval : (orderUpgrade trail ⟨.boolEq s true, true⟩).atom =
              .intLe s hi := by
            simp [orderUpgrade, h, hc, negLe]
          intro n hn
          rw [hval] at hn
          cases hn
          exact trailHiOf_mem hhi hi h
        · have hval : (orderUpgrade trail ⟨.boolEq s true, true⟩).atom =
              .boolEq s true := by
            simp [orderUpgrade, h, hc]
          intro n hn
          rw [hval] at hn
          cases hn

/-! ## Obligations (this file is the P1 feasibility gate)

* P1-a (owner P2): canonical-form membership in the clause pool.
  CLOSED for subsequences THIS WAVE: `sublistsOf_mem_of_sublist` +
  `canonicalClause_mem_clausePool_of_sublist`, whose minimal shape is
  `Clause.canonicalClause c <+ litPool orig`. The literal-level form
  (`∀ l ∈ c, l.norm ∈ litPool orig`) is NOT sufficient —
  `sublistsOf_reordering_witness` is a kernel counterexample (the pool
  enumerates order-preserving sublists; dedup does not help).
  LITERAL-MEMBERSHIP HALF NOW PROVED: `canonicalClause_ofUIP_learned`
  (exact canonical shape), `ofUIP_canonical_lits_mem` (below + UIP pooled
  implies every canonical learned literal pooled), `TrailVocabulary` +
  `trailVocabulary_append_entry` (the state-side invariant, stated
  exactly). EXACT IRREDUCIBLE RESIDUAL: the order alignment
  `Clause.canonicalClause an.learned <+ litPool orig` cannot follow from
  literal membership (kernel witness above); it must come from the pool
  count being re-keyed order-insensitively (owner P4, frozen
  `Proofs/SchedulerJumpProgress` `hpool`), or the canonical form being
  sorted into pool order. The counting route does not depend on dedup:
  `clausePool_length` and `clausePool_lits_mem` are proved, and
  duplicates only over-count.
* P1-b (owner P4): upgrade threshold closure — for a trail whose
  `intLe` thresholds all lie in `threshPool d`,
  `(orderUpgrade trail l).atom` is again a `threshPool d` threshold.
  PROVED CONDITIONALLY THIS WAVE (per-slot representative set `G`,
  instantiate `G := threshPool d`): `trailHiOf_mem`,
  `trailLoOf_sub_one_mem`, `orderUpgrade_intLe_pos_mem`,
  `orderUpgrade_intLe_neg_mem`, `orderUpgrade_bool_pos_mem` — the
  `k + 1`/`lo - 1` arithmetic closes via `maxI_succ_sub_one` and the
  foldl invariants (`hiStep_mem`/`loStep_mem`). Residual: linking the
  per-slot hypothesis to the pool (`trail literal pooled ⟹ threshold ∈
  threshPool (orig[s])`) is P1-c vocabulary inversion, still open
  (owner P2).
* P1-c (owner P2/P4): reason-literal class — propagator reasons built
  from slot values (`posNe s i`, `i ∈ vocabDomInts`) and trail bounds are
  pooled; reasons mentioning slots outside `orig`, or `intLe` thresholds
  produced by propagator arithmetic other than trail bounds, are NOT yet
  covered by this vocabulary. P2 must either derive them from
  `DomConflictEvidence` reason validity or name the missing family.

-/

/-- Kind rank of an atom in the literal order key (boolEq < intLe < intNe). -/
def _root_.LeanFzn.Solver.Propagation.Atom.kindRank : Atom → Nat
  | .boolEq _ _ => 0
  | .intLe _ _ => 1
  | .intNe _ _ => 2

/-- Injective encoding of `Int` into `Nat` (constructor match). -/
def Int.encNat : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem Int.encNat_inj {a b : Int} (h : Int.encNat a = Int.encNat b) : a = b := by
  cases a with
  | ofNat n =>
      cases b with
      | ofNat m => exact congrArg Int.ofNat (by simp [Int.encNat] at h; omega)
      | negSucc m => exfalso; simp [Int.encNat] at h; omega
  | negSucc n =>
      cases b with
      | ofNat m => exfalso; simp [Int.encNat] at h; omega
      | negSucc m => exact congrArg Int.negSucc (by simp [Int.encNat] at h; omega)

theorem Bool.toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Payload code of a literal (kind-rank disambiguates the constructors). -/
def _root_.LeanFzn.Solver.Propagation.Literal.payloadCode : Literal → Nat
  | ⟨.boolEq _ b, _⟩ => b.toNat
  | ⟨.intLe _ k, _⟩ => Int.encNat k
  | ⟨.intNe _ k, _⟩ => Int.encNat k

/-- Computable total-order key: (slot, kind), (payload, polarity). -/
def _root_.LeanFzn.Solver.Propagation.Literal.key (l : Literal) : (Nat × Nat) × (Nat × Nat) :=
  ((l.atom.slot, l.atom.kindRank), (l.payloadCode, l.positive.toNat))

theorem _root_.LeanFzn.Solver.Propagation.Literal.key_inj {a b : Literal} (h : a.key = b.key) : a = b := by
  cases a with
  | mk aA aP =>
  cases b with
  | mk bA bP =>
  simp only [Literal.key, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  cases aA with
  | boolEq sa va =>
      cases bA with
      | boolEq sb vb =>
          have hv : va = vb := Bool.toNat_inj h3
          have hp : aP = bP := Bool.toNat_inj h4
          subst h1; subst hv; subst hp; rfl
      | intLe sb kb => exfalso; simp [Atom.kindRank] at h2
      | intNe sb kb => exfalso; simp [Atom.kindRank] at h2
  | intLe sa ka =>
      cases bA with
      | boolEq sb vb => exfalso; simp [Atom.kindRank] at h2
      | intLe sb kb =>
          have hk : ka = kb := Int.encNat_inj h3
          have hp : aP = bP := Bool.toNat_inj h4
          subst h1; subst hk; subst hp; rfl
      | intNe sb kb => exfalso; simp [Atom.kindRank] at h2
  | intNe sa ka =>
      cases bA with
      | boolEq sb vb => exfalso; simp [Atom.kindRank] at h2
      | intLe sb kb => exfalso; simp [Atom.kindRank] at h2
      | intNe sb kb =>
          have hk : ka = kb := Int.encNat_inj h3
          have hp : aP = bP := Bool.toNat_inj h4
          subst h1; subst hk; subst hp; rfl

/-- Strict lexicographic order on Nat pairs. -/
def Lex2Lt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Nat × Nat) : Decidable (Lex2Lt a b) := by unfold Lex2Lt; infer_instance

theorem Lex2Lt_asymm {a b : Nat × Nat} (h1 : Lex2Lt a b) (h2 : Lex2Lt b a) : False := by
  rcases h1 with h | ⟨h, h'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩ <;> omega

/-- Strict order on literal keys (two lex layers of `Lex2Lt`). -/
def KeyLt (a b : Literal) : Prop :=
  Lex2Lt a.key.1 b.key.1 ∨ (a.key.1 = b.key.1 ∧ Lex2Lt a.key.2 b.key.2)

instance (a b : Literal) : Decidable (KeyLt a b) := by unfold KeyLt; infer_instance

theorem KeyLt_asymm {a b : Literal} (h1 : KeyLt a b) (h2 : KeyLt b a) : False := by
  rcases h1 with h | ⟨h, h'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Lex2Lt_asymm h h2
  · rw [h2] at h
    rcases h with h | ⟨h, _⟩ <;> omega
  · rw [h] at h2
    rcases h2 with h2 | ⟨h2, _⟩ <;> omega
  · exact Lex2Lt_asymm h' h2'

/-- The literal order (Prop form; `Decidable` via the instances above). -/
def _root_.LeanFzn.Solver.Propagation.Literal.leB (a b : Literal) : Prop := KeyLt a b ∨ a.key = b.key

instance (a b : Literal) : Decidable (a.leB b) := by unfold Literal.leB; infer_instance

theorem _root_.LeanFzn.Solver.Propagation.Literal.leB_refl (l : Literal) : l.leB l := Or.inr rfl

theorem _root_.LeanFzn.Solver.Propagation.Literal.leB_antisymm {a b : Literal} (h1 : a.leB b) (h2 : b.leB a) : a = b := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (KeyLt_asymm h1 h2).elim
  · exact Literal.key_inj h2.symm
  · exact Literal.key_inj h1
  · exact Literal.key_inj h1

/-- Boolean sort comparator for `List.mergeSort`. -/
def litSortLe (a b : Literal) : Bool := decide (a.leB b)

/-- Sort-based canonical form of a clause: normalized literals, sorted. -/
def canonicalClauseSorted (c : Clause) : Clause :=
  (c.map Literal.norm).mergeSort litSortLe

theorem canonicalClauseSorted_mem {c : Clause} {l : Literal} :
    l ∈ canonicalClauseSorted c ↔ l ∈ c.map Literal.norm :=
  List.mem_mergeSort

theorem canonicalClauseSorted_perm (c : Clause) :
    (canonicalClauseSorted c).Perm (c.map Literal.norm) :=
  List.mergeSort_perm _ _

/-- The sorted literal pool. -/
def sortedLitPool (orig : List Domain) : List Literal :=
  (litPool orig).mergeSort litSortLe

theorem sortedLitPool_mem {orig : List Domain} {l : Literal} :
    l ∈ sortedLitPool orig ↔ l ∈ litPool orig :=
  List.mem_mergeSort

/-- **THE ORDER-INSENSITIVE CANONICAL CLAUSE**: the sublist of the
    sorted pool containing exactly the pool literals that occur
    (normalized) in `c`. Depends only on the SET of `c.map Literal.norm`. -/
def canonicalSorted (orig : List Domain) (c : Clause) : Clause :=
  (sortedLitPool orig).filter (fun x => decide (x ∈ c.map Literal.norm))

/-- The order-insensitive clause pool. -/
def sortedClausePool (orig : List Domain) : List Clause :=
  sublistsOf (sortedLitPool orig)

theorem canonicalSorted_sublist (orig : List Domain) (c : Clause) :
    (canonicalSorted orig c).Sublist (sortedLitPool orig) :=
  List.filter_sublist

theorem sublistsOf_sublist {L : List Literal} {c : Clause}
    (h : c ∈ sublistsOf L) : c.Sublist L := by
  induction L generalizing c with
  | nil =>
      simp only [sublistsOf, List.mem_singleton] at h
      subst h
      exact List.Sublist.refl _
  | cons a L ih =>
      simp only [sublistsOf, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨c', hc', he⟩
      · exact (ih h).trans (List.Sublist.cons a (List.Sublist.refl L))
      · cases he
        exact List.Sublist.cons_cons a (ih hc')

theorem sortedClausePool_mem_iff_sublist {orig : List Domain} {c : Clause} :
    c ∈ sortedClausePool orig ↔ c.Sublist (sortedLitPool orig) :=
  ⟨sublistsOf_sublist, sublistsOf_mem_of_sublist⟩

theorem canonicalSorted_mem_sortedClausePool (orig : List Domain) (c : Clause) :
    canonicalSorted orig c ∈ sortedClausePool orig :=
  sublistsOf_mem_of_sublist (canonicalSorted_sublist orig c)

theorem canonicalSorted_congr {orig : List Domain} {c d : Clause}
    (h : ∀ l : Literal, l ∈ c.map Literal.norm ↔ l ∈ d.map Literal.norm) :
    canonicalSorted orig c = canonicalSorted orig d := by
  apply List.filter_congr
  intro x _
  exact decide_eq_decide.mpr (h x)

theorem norm_mem_canonicalSorted {orig : List Domain} {c : Clause} {l : Literal}
    (hc : l ∈ c) (hp : l.norm ∈ litPool orig) :
    l.norm ∈ canonicalSorted orig c :=
  List.mem_filter.mpr
    ⟨sortedLitPool_mem.mpr hp, by
      simp only [decide_eq_true_eq]
      exact List.mem_map_of_mem (f := Literal.norm) hc⟩

/-- The P4-consumable backward direction: every literal-normalized
    clause is in the order-insensitive pool (no sublist hypothesis). -/
theorem sortedClausePool_mem_of_forall_norm_mem {orig : List Domain} {c : Clause}
    (h : ∀ l ∈ c, l.norm ∈ litPool orig) :
    canonicalSorted orig c ∈ sortedClausePool orig :=
  canonicalSorted_mem_sortedClausePool orig c

/-- Kernel-checked refutation of the literal-membership-to-CANONICAL-
    membership equivalence's converse direction: for `orig = []` the
    canonical (pool-filtered) form of a one-literal clause is `[]`,
    which IS enumerated, while the literal's normalization is NOT in the
    empty pool. -/
theorem canonicalSorted_forward_false_witness :
    canonicalSorted [] [⟨.intLe 0 3, true⟩] ∈ sortedClausePool []
      ∧ ¬ (∀ l ∈ ([⟨.intLe 0 3, true⟩] : Clause), l.norm ∈ litPool []) := by
  constructor
  · simp [sortedClausePool, canonicalSorted, sortedLitPool, litPool, atomPool,
      atomPoolBase, sublistsOf]
  · intro h
    have hmem := h ⟨.intLe 0 3, true⟩ (by simp)
    simp [litPool, atomPool, atomPoolBase] at hmem

/-! ## The finite pool extension (C1): `litPoolWith`

The retained kernel witness (`Proofs/EmissionVocabulary.lean` §4:
`emitted_threshold_not_pooled`) shows the registered kit can emit a
threshold OUTSIDE `threshPool`, so the C1 pooled-emission producer cannot
live at `litPool` alone. This section provides the APPEND-ONLY finite
extension: `litPoolWith extra orig` is `litPool`'s four-block
construction over the atom pool extended by `extra` (kept
`Atom.boolFlip`-closed by construction), so every pool algebra fact
(membership constructors, normalization/negation closure, size bound)
has an exact analog, `litPool` embeds by `litPool_mem_litPoolWith`, and
`litPool` itself is NOT redefined (no downstream statement changes). -/

/-- The extra atoms with their Boolean-flip closure (the `extra` half of
`atomPoolWith`). -/
def atomExtras (extra : List Atom) : List Atom :=
  extra ++ extra.map Atom.boolFlip

/-- The atom pool extended by `extra` (flip-closed): the append-only
analog of `atomPool`. -/
def atomPoolWith (extra : List Atom) (orig : List Domain) : List Atom :=
  atomPool orig ++ atomExtras extra

/-- `atomExtras` is closed under the Boolean flip. -/
theorem atomExtras_boolFlip_mem {extra : List Atom} {a : Atom}
    (h : a ∈ atomExtras extra) : a.boolFlip ∈ atomExtras extra := by
  rw [atomExtras] at h ⊢
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ (List.mem_map_of_mem (f := Atom.boolFlip) h)
  · rcases List.mem_map.mp h with ⟨a', ha', he⟩
    rw [← he, Atom.boolFlip_invol]
    exact List.mem_append_left _ ha'

/-- `atomPoolWith` is closed under the Boolean flip. -/
theorem atomPoolWith_boolFlip_mem {extra : List Atom} {orig : List Domain}
    {a : Atom} (h : a ∈ atomPoolWith extra orig) :
    a.boolFlip ∈ atomPoolWith extra orig := by
  rw [atomPoolWith] at h ⊢
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (atomPool_boolFlip_mem h)
  · exact List.mem_append_right _ (atomExtras_boolFlip_mem h)

/-- Every original atom is an extended atom. -/
theorem atomPool_mem_atomPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (h : a ∈ atomPool orig) : a ∈ atomPoolWith extra orig :=
  List.mem_append_left _ h

/-- Every extra atom is an extended atom. -/
theorem atomExtras_mem_atomPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (h : a ∈ atomExtras extra) : a ∈ atomPoolWith extra orig :=
  List.mem_append_right _ h

/-- The extended literal pool: `litPool`'s four blocks over the extended
atom pool. -/
def litPoolWith (extra : List Atom) (orig : List Domain) : List Literal :=
  (atomPoolWith extra orig).map posLit
    ++ (atomPoolWith extra orig).map negLit
    ++ (atomPoolWith extra orig).map flipPosLit
    ++ (atomPoolWith extra orig).map flipNegLit

theorem posLit_mem_litPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (ha : a ∈ atomPoolWith extra orig) :
    posLit a ∈ litPoolWith extra orig := by
  rw [litPoolWith]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (f := posLit) ha)))

theorem negLit_mem_litPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (ha : a ∈ atomPoolWith extra orig) :
    negLit a ∈ litPoolWith extra orig := by
  rw [litPoolWith]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := negLit) ha)))

theorem flipPosLit_mem_litPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (ha : a ∈ atomPoolWith extra orig) :
    flipPosLit a ∈ litPoolWith extra orig := by
  rw [litPoolWith]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := flipPosLit) ha))

theorem flipNegLit_mem_litPoolWith {extra : List Atom} {orig : List Domain}
    {a : Atom} (ha : a ∈ atomPoolWith extra orig) :
    flipNegLit a ∈ litPoolWith extra orig := by
  rw [litPoolWith]
  exact List.mem_append_right _ (List.mem_map_of_mem (f := flipNegLit) ha)

/-- The base pool embeds into the extended pool. -/
theorem litPool_mem_litPoolWith {extra : List Atom} {orig : List Domain}
    {l : Literal} (h : l ∈ litPool orig) : l ∈ litPoolWith extra orig := by
  rw [litPool] at h
  rcases List.mem_append.mp h with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · rcases List.mem_map.mp h1 with ⟨a, ha, he⟩
        rw [← he]
        exact posLit_mem_litPoolWith (atomPool_mem_atomPoolWith ha)
      · rcases List.mem_map.mp h2 with ⟨a, ha, he⟩
        rw [← he]
        exact negLit_mem_litPoolWith (atomPool_mem_atomPoolWith ha)
    · rcases List.mem_map.mp h3 with ⟨a, ha, he⟩
      rw [← he]
      exact flipPosLit_mem_litPoolWith (atomPool_mem_atomPoolWith ha)
  · rcases List.mem_map.mp h4 with ⟨a, ha, he⟩
    rw [← he]
    exact flipNegLit_mem_litPoolWith (atomPool_mem_atomPoolWith ha)

/-- `norm` of an extended-pool literal is an extended-pool literal. -/
theorem litPoolWith_norm_closed {extra : List Atom} {orig : List Domain}
    {l : Literal} (h : l ∈ litPoolWith extra orig) :
    l.norm ∈ litPoolWith extra orig := by
  rw [litPoolWith] at h
  rcases List.mem_append.mp h with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · rcases List.mem_map.mp h1 with ⟨a, ha, he⟩
        rw [← he]
        cases a <;> simpa [posLit, Literal.norm] using posLit_mem_litPoolWith ha
      · rcases List.mem_map.mp h2 with ⟨a, ha, he⟩
        rw [← he]
        cases a
        · simpa [negLit, flipPosLit, Atom.boolFlip, Literal.norm]
            using flipPosLit_mem_litPoolWith ha
        · simpa [negLit, Literal.norm] using negLit_mem_litPoolWith ha
        · simpa [negLit, Literal.norm] using negLit_mem_litPoolWith ha
    · rcases List.mem_map.mp h3 with ⟨a, ha, he⟩
      rw [← he]
      cases a
      · simpa [flipPosLit, Atom.boolFlip, Literal.norm]
          using flipPosLit_mem_litPoolWith ha
      · simpa [flipPosLit, posLit, Atom.boolFlip, Literal.norm]
          using posLit_mem_litPoolWith ha
      · simpa [flipPosLit, posLit, Atom.boolFlip, Literal.norm]
          using posLit_mem_litPoolWith ha
  · rcases List.mem_map.mp h4 with ⟨a, ha, he⟩
    rw [← he]
    cases a
    · simpa [flipNegLit, posLit, Atom.boolFlip, Literal.norm, Bool.not_not]
        using posLit_mem_litPoolWith ha
    · simpa [flipNegLit, negLit, Atom.boolFlip, Literal.norm]
        using negLit_mem_litPoolWith ha
    · simpa [flipNegLit, negLit, Atom.boolFlip, Literal.norm]
        using negLit_mem_litPoolWith ha

/-- `negate` of an extended-pool literal is an extended-pool literal. -/
theorem litPoolWith_negate_closed {extra : List Atom} {orig : List Domain}
    {l : Literal} (h : l ∈ litPoolWith extra orig) :
    l.negate ∈ litPoolWith extra orig := by
  rw [litPoolWith] at h
  rcases List.mem_append.mp h with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · rcases List.mem_map.mp h1 with ⟨a, ha, he⟩
        rw [← he]
        simpa [posLit, negLit, Literal.negate, Bool.not_true]
          using negLit_mem_litPoolWith ha
      · rcases List.mem_map.mp h2 with ⟨a, ha, he⟩
        rw [← he]
        simpa [posLit, negLit, Literal.negate, Bool.not_false]
          using posLit_mem_litPoolWith ha
    · rcases List.mem_map.mp h3 with ⟨a, ha, he⟩
      rw [← he]
      simpa [flipPosLit, flipNegLit, Literal.negate, Bool.not_true]
        using flipNegLit_mem_litPoolWith ha
  · rcases List.mem_map.mp h4 with ⟨a, ha, he⟩
    rw [← he]
    simpa [flipPosLit, flipNegLit, Literal.negate, Bool.not_false]
      using flipPosLit_mem_litPoolWith ha

theorem atomExtras_length (extra : List Atom) :
    (atomExtras extra).length = 2 * extra.length := by
  rw [atomExtras, List.length_append, List.length_map]
  omega

theorem atomPoolWith_length_le (extra : List Atom) (orig : List Domain) :
    (atomPoolWith extra orig).length ≤ (atomPool orig).length + 2 * extra.length := by
  rw [atomPoolWith, List.length_append, atomExtras_length]
  omega

/-- Extended literal pool size bound: four blocks over the extended atom
pool (the finiteness fact the extended rank/closure key consumes). -/
theorem litPoolWith_length_le (extra : List Atom) (orig : List Domain) :
    (litPoolWith extra orig).length
      ≤ 4 * ((atomPool orig).length + 2 * extra.length) := by
  simp only [litPoolWith, List.length_append, List.length_map]
  have h := atomPoolWith_length_le extra orig
  omega

/-- Readable finiteness form of the extended pool: the base bound plus
eight literals per extra atom. -/
theorem litPoolWith_length_le' (extra : List Atom) (orig : List Domain) :
    (litPoolWith extra orig).length
      ≤ 4 * (atomPool orig).length + 8 * extra.length := by
  have h := litPoolWith_length_le extra orig
  omega

end LeanFzn.Solver.UIP

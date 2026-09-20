import solver.Solve

/-!
# All-solutions enumeration (PLAN.md 6.7, part 1: enumeration)

PLAN 6.7 asks for all-solutions enumeration with two guarantees:
every reported solution is distinct and satisfying, and a completed
enumeration returns all satisfying assignments.  This module delivers
exactly that, mirroring the architecture of `solver/Search.lean` and
`solver/Solve.lean`:

* `enumerateAll` — the enumerator, structurally identical to the
  reference `search` (first slot, first value, retry the rest of the
  first slot's domain; an empty-domain slot contributes nothing) but
  *accumulating* every complete assignment that passes the leaf
  predicate, in the deterministic search order.  Termination uses the
  same measure (`slotsMeasure`): each recursive call strictly shrinks
  the slots, even though the accumulator grows.

* `enumerateAll_mem_iff_root` — **the membership theorem**, giving
  both halves of the guarantee in one iff: a result is reported
  exactly when it is a complete assignment of the slots that passes
  the leaf.  Forward: every reported solution is a satisfying
  complete assignment.  Backward: every satisfying complete
  assignment is reported (a completed enumeration returns them all).

* `enumerateAll_nodup` — **distinctness**: the reported solutions are
  pairwise distinct provided every slot *domain* is duplicate-free
  (`List.Nodup`).  The hypothesis is necessary in general — a
  duplicated domain value would make one complete assignment
  reachable down two different branches — and is discharged for the
  FlatZinc wrapper by construction (below).

* `enumModel` — the FlatZinc-shaped wrapper, mirroring
  `solveModel`'s gate structure (`firstUnsupportedFast`,
  `wellFormedFastB`, `slotsChecked`) but collecting *all* accepted
  solution texts via `enumerateAll` with the same leaf
  (`solveLeaf` from `solver/Solve.lean`, unchanged).  Two design
  points:

  - the slot domains are passed through `dedup` (keep first
    occurrences), so the enumeration's distinctness theorem applies
    by construction; `dedup` preserves membership
    (`dedup_mem_iff`), hence `allAssigns` over the deduped slots
    has the same members as over the originals
    (`allAssigns_dedup_mem`), so the wrapper theorems still
    quantify over exactly the declared assignments.  Duplicated
    domains only arise from explicitly enumerated sets
    (`var {1, 1}: x;`), which the checker's semantics accepts as a
    one-element domain;

  - the emitted texts are passed through `dedup` as well, so the
    *reported* solutions are pairwise distinct unconditionally
    (`enumModel_nodup`), without a string-level round-trip theorem
    about the emitter (the in-progress proof branch is isolated in
    `solver/Emit/Roundtrip.lean`). Under duplicate-free domains the two dedups are
    no-ops for distinctness purposes; they exist to make the
    distinctness guarantee hold in full generality.

  The wrapper theorems mirror `solveModel`'s: `enumModel_sat_sound`
  (every reported text is checker-accepted),
  `enumModel_complete` (every accepted slot assignment's emitted
  text is reported), and `enumModel_unsat` (an `unsat` verdict
  excludes every slot assignment).  Together with
  `enumModel_nodup` these are the enumeration half of PLAN 6.7.

The optimization half of PLAN 6.7 (branch and bound, improving
bounds) is a later phase and not part of this module.  Round 3 will
wire this enumeration into the FlatZinc-facing CLI layer.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Check LeanFzn.Globals

/-! ## A decidable equality on `Value`

The generic machinery below (`dedup`, `enumerateAll_nodup`) needs
`BEq`/`LawfulBEq` on the value type.  The checker's own structural
equality `Value.eqB` (`LeanFzn.FznStdLib.lean`) is exactly right and
carries the correctness theorems `value_eqB_refl`/`value_eqB_iff`
(the development's established pattern: reuse the proved Boolean
twin instead of deriving a fresh equality). -/

/-- The checker's structural value equality, as the `BEq` instance. -/
instance : BEq Value := ⟨Value.eqB⟩

/-- `Value.eqB` is reflexive and sound, so it is a lawful equality. -/
instance : LawfulBEq Value := {
  eq_of_beq := fun {_ _} h => value_eqB_iff.mp h
  rfl := fun {_} => value_eqB_refl _
}

/-! ## The enumerator -/

/-- **The all-solutions enumerator.**  Structurally the reference
`search` of `solver/Search.lean` (first slot, first value, retry the
rest of the first slot's domain; an empty-domain slot contributes
nothing), but instead of stopping at the first assignment that passes
`leaf`, it *accumulates* every passing complete assignment, in the
deterministic search order.  `slots` is the list of remaining domains
and `acc` the already-fixed prefix; each result is a complete
assignment `acc ++ a` with `a` picking one value per remaining slot. -/
def enumerateAll {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → List (List α)
  | [], acc => if leaf acc then [acc] else []
  | [] :: _, _ => []
  | (v :: vs) :: rest, acc =>
      enumerateAll leaf rest (acc ++ [v])
        ++ enumerateAll leaf (vs :: rest) acc
termination_by slots _ => slotsMeasure slots
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega

/-! ## The streaming fast twin (IDEAS 4.5)

`enumerateAll` pays two quadratic costs: `acc ++ [v]` per node (as
in `search`), and the `++` join of the two children's result lists
at every branching level — O(k²) list cells in the number `k` of
solutions.  The twin below threads *both* accumulators:

* the reversed assignment accumulator `racc` (consing, as
  `searchGo`), so the leaf test runs on `racc.reverse` — exactly the
  slot-order list the reference tests; and

* a *result accumulator* `acc'` that collects the passing
  assignments newest-first (consing, O(1) per solution): the two
  children are folded in the reference's left-to-right order
  (retry branch inner, first-value branch outer), so the final
  `reverse` restores the deterministic search order.

The bridge theorem `enumGo_enum` below proves the twin *is* the
reference enumerator pointwise (the equality behind the
`implemented_by` attribute on `enumerateAll`), so the membership
theorem `enumerateAll_mem_iff` and the distinctness theorem
`enumerateAll_nodup` transfer to the running code verbatim. -/

/-- The streaming enumeration loop: `racc` the reversed assignment
    accumulator, `acc'` the reversed result accumulator (passing
    assignments collected newest-first). -/
private def enumGo {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → List (List α) → List (List α)
  | [], racc, acc' => if leaf racc.reverse then racc.reverse :: acc' else acc'
  | [] :: _, _, acc' => acc'
  | (v :: vs) :: rest, racc, acc' =>
      enumGo leaf (vs :: rest) racc (enumGo leaf rest (v :: racc) acc')
termination_by slots _ _ => slotsMeasure slots
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega

/-- Same-shape fast twin of `enumerateAll` (the `implemented_by`
    target): runs the streaming loop from the slot-order
    accumulator and reverses the collected results once. -/
private def enumFast {α : Type} (leaf : List α → Bool)
    (slots : List (List α)) (acc : List α) : List (List α) :=
  (enumGo leaf slots acc.reverse []).reverse

/-- **The bridge theorem (IDEAS 4.5's proof obligation)**: the
    streaming loop returns, after the final reversal, exactly the
    reference enumeration of the reversed accumulator.  The
    invariant is `(enumGo … acc').reverse = results ++ acc'.reverse`;
    the children fold in the reference's order, so the two
    `reverse`s restore left-to-right order. -/
theorem enumGo_enum {α : Type} (leaf : List α → Bool) :
    ∀ (slots : List (List α)) (racc : List α) (acc' : List (List α)),
      enumGo leaf slots racc acc'
        = (enumerateAll leaf slots racc.reverse).reverse ++ acc' := by
  intro slots racc acc'
  induction slots, racc, acc' using enumGo.induct (leaf := leaf) with
  | case1 racc acc' hleaf =>
      show enumGo leaf [] racc acc' = _
      rw [enumGo]
      have h : leaf racc.reverse = true := by simpa using hleaf
      rw [if_pos h, enumerateAll, if_pos h]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
  | case2 racc acc' hleaf =>
      show enumGo leaf [] racc acc' = _
      rw [enumGo]
      have h : ¬leaf racc.reverse = true := by simpa using hleaf
      rw [if_neg h, enumerateAll, if_neg h]
      simp
  | case3 tail x acc' =>
      show enumGo leaf ([] :: tail) x acc' = _
      rw [enumGo, enumerateAll]
      simp
  | case4 v vs rest racc acc' ih1 ih2 =>
      show enumGo leaf ((v :: vs) :: rest) racc acc' = _
      rw [enumGo, ih2, ih1, enumerateAll, List.reverse_cons,
        List.reverse_append, List.append_assoc]

/-- The fast twin is the reference `enumerateAll` pointwise (the
    equality behind the `implemented_by` attribute below). -/
theorem enumFast_eq {α : Type} (leaf : List α → Bool)
    (slots : List (List α)) (acc : List α) :
    enumFast leaf slots acc = enumerateAll leaf slots acc := by
  unfold enumFast
  rw [enumGo_enum]
  simp

-- IDEAS 4.5: the compiled `enumerateAll` runs the streaming twin
-- (equal by `enumFast_eq`)
attribute [implemented_by enumFast] enumerateAll

/-! ## The membership theorem (satisfaction and completeness) -/

/-- The general membership characterization of `enumerateAll`, for an
arbitrary accumulator: a result is reported exactly when it is the
accumulator extended by a complete assignment of the remaining slots
that passes the leaf predicate.  Instantiating the accumulator at
`[]` gives `enumerateAll_mem_iff_root`. -/
theorem enumerateAll_mem_iff {α : Type} (leaf : List α → Bool) :
    ∀ (slots : List (List α)) (acc : List α) (r : List α),
      (r ∈ enumerateAll leaf slots acc) ↔
        ∃ a, a ∈ allAssigns slots ∧ r = acc ++ a ∧ leaf (acc ++ a) = true := by
  intro slots acc
  induction slots, acc using enumerateAll.induct (leaf := leaf) with
  | case1 acc hleaf =>
      intro r
      simp only [enumerateAll, if_pos hleaf]
      constructor
      · intro h
        have hrr : r = acc := List.mem_singleton.mp h
        subst hrr
        refine ⟨[], by simp [allAssigns], ?_, ?_⟩
        · rw [List.append_nil]
        · rw [List.append_nil]; exact hleaf
      · intro h
        obtain ⟨a, ha, heq, _⟩ := h
        have ha0 : a = [] := by simpa [allAssigns] using ha
        subst ha0
        simp only [List.append_nil] at heq
        subst heq
        simp
  | case2 acc hleaf =>
      intro r
      simp only [enumerateAll, if_neg hleaf]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h
        obtain ⟨a, ha, heq, hleaf'⟩ := h
        have ha0 : a = [] := by simpa [allAssigns] using ha
        subst ha0
        simp only [List.append_nil] at heq hleaf'
        subst heq
        exact absurd hleaf' hleaf
  | case3 tail x =>
      intro r
      simp only [enumerateAll]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h
        obtain ⟨a, ha, _, _⟩ := h
        exact absurd ha (by simp [allAssigns])
  | case4 v vs rest acc ih1 ih2 =>
      intro r
      simp only [enumerateAll]
      rw [List.mem_append]
      constructor
      · intro h
        rcases h with h | h
        · obtain ⟨a, ha, rfl, hleaf⟩ := (ih1 r).mp h
          refine ⟨v :: a, (mem_allAssigns_singleton v vs rest (v :: a)).mpr
            ⟨v, List.mem_cons_self, a, ha, rfl⟩, ?_, ?_⟩
          · simp only [List.append_assoc, List.cons_append, List.nil_append]
          · simp only [List.append_assoc, List.cons_append, List.nil_append] at hleaf
            exact hleaf
        · obtain ⟨a, ha, rfl, hleaf⟩ := (ih2 r).mp h
          exact ⟨a, allAssigns_subset_cons v vs rest a ha, rfl, hleaf⟩
      · intro h
        obtain ⟨a, ha, rfl, hleaf⟩ := h
        rw [mem_allAssigns_singleton] at ha
        obtain ⟨w, hw, a', ha', rfl⟩ := ha
        by_cases hwv : w = v
        · subst hwv
          left
          have ih1' := ih1 (acc ++ w :: a')
          simp only [List.append_assoc, List.cons_append, List.nil_append] at ih1'
          exact ih1'.mpr ⟨a', ha', rfl, hleaf⟩
        · right
          have hwvs : w ∈ vs := by
            rcases List.mem_cons.mp hw with heq | hin
            · exact absurd heq hwv
            · exact hin
          have hgen : ∀ (xs : List α) (b : α),
              b ∈ xs → ∀ (r2 : List (List α)) (t : List α),
                t ∈ allAssigns r2 → b :: t ∈ allAssigns (xs :: r2) := by
            intro xs b hmem r2 t ht
            induction xs with
            | nil => exact absurd hmem (by simp)
            | cons u us ih3 =>
                by_cases hmemu : u = b
                · subst hmemu
                  rw [allAssigns, List.mem_flatMap]
                  exact ⟨t, ht, by
                    have := List.mem_map_of_mem (a := u)
                      (f := fun w => w :: t) (l := u :: us) List.mem_cons_self
                    exact this⟩
                · have hbus : b ∈ us := by
                    rcases List.mem_cons.mp hmem with heq | hin
                    · exact absurd heq.symm hmemu
                    · exact hin
                  have hrec : b :: t ∈ allAssigns (us :: r2) := ih3 hbus
                  exact allAssigns_subset_cons u us r2 _ hrec
          have hmem2 : w :: a' ∈ allAssigns (vs :: rest) := hgen vs w hwvs rest a' ha'
          exact (ih2 (acc ++ (w :: a'))).mpr ⟨w :: a', hmem2, rfl, hleaf⟩

/-- **The membership theorem at the root** (PLAN 6.7's satisfaction
and completeness guarantees in one iff): a result is reported by the
completed enumeration exactly when it is a complete assignment of the
slots that passes the leaf predicate.  Forward: every reported
solution is a satisfying complete assignment.  Backward: every
satisfying complete assignment is reported by the completed
enumeration. -/
theorem enumerateAll_mem_iff_root {α : Type} (leaf : List α → Bool)
    (slots : List (List α)) (r : List α) :
    r ∈ enumerateAll leaf slots [] ↔ r ∈ allAssigns slots ∧ leaf r = true := by
  have h := enumerateAll_mem_iff leaf slots [] r
  simp only [List.nil_append] at h
  constructor
  · intro hmem
    obtain ⟨a, ha, heq, hleaf⟩ := h.mp hmem
    subst heq
    exact ⟨ha, hleaf⟩
  · intro ⟨ha, hleaf⟩
    exact h.mpr ⟨r, ha, rfl, hleaf⟩

/-! ## Distinctness of the enumeration -/

/-- **Distinctness of the reported solutions** (PLAN 6.7): under the
explicit hypothesis that every slot domain is duplicate-free
(`List.Nodup`), the enumeration reports no solution twice.  The
hypothesis is necessary — a duplicated value in a domain would make
one complete assignment reachable down two different branches (the
first sub-enumeration fixes the head value `v`, the second some value
of the tail, and without Nodup they can coincide).  The FlatZinc
wrapper discharges it by construction, passing the domains through
`dedup`. -/
theorem enumerateAll_nodup {α : Type} [BEq α] [LawfulBEq α] (leaf : List α → Bool) :
    ∀ (slots : List (List α)) (acc : List α),
      (∀ d ∈ slots, d.Nodup) → (enumerateAll leaf slots acc).Nodup := by
  intro slots acc
  induction slots, acc using enumerateAll.induct (leaf := leaf) with
  | case1 acc hleaf =>
      intro _
      simp only [enumerateAll, if_pos hleaf]
      rw [List.nodup_cons]
      exact ⟨by simp, List.nodup_nil⟩
  | case2 acc hleaf =>
      intro _
      simp only [enumerateAll, if_neg hleaf]
      exact List.nodup_nil
  | case3 tail x =>
      intro _
      simp only [enumerateAll]
      exact List.nodup_nil
  | case4 v vs rest acc ih1 ih2 =>
      intro hdoms
      have hnd : (v :: vs).Nodup := hdoms (v :: vs) List.mem_cons_self
      have hvnotin : v ∉ vs := (List.nodup_cons.mp hnd).1
      have hrest : ∀ d ∈ rest, d.Nodup :=
        fun d hd => hdoms d (List.mem_cons_of_mem _ hd)
      have hvsrest : ∀ d ∈ vs :: rest, d.Nodup := by
        intro d hd
        rcases List.mem_cons.mp hd with heq | hin
        · rw [heq]
          exact (List.nodup_cons.mp hnd).2
        · exact hdoms d (List.mem_cons_of_mem _ hin)
      simp only [enumerateAll]
      rw [List.nodup_append]
      refine ⟨ih1 hrest, ih2 hvsrest, ?_⟩
      intro x hx y hy
      obtain ⟨a, ha, hxa, _⟩ := (enumerateAll_mem_iff leaf rest (acc ++ [v]) x).mp hx
      obtain ⟨a', ha', hya, _⟩ := (enumerateAll_mem_iff leaf (vs :: rest) acc y).mp hy
      cases vs with
      | nil => exact absurd ha' (by simp [allAssigns])
      | cons u us =>
          rw [mem_allAssigns_singleton] at ha'
          obtain ⟨w, hw, a'', ha'', rfl⟩ := ha'
          intro hxy
          rw [hxa, hya] at hxy
          rw [List.append_assoc] at hxy
          have h1 : [v] ++ a = w :: a'' := List.append_cancel_left hxy
          have hcons : v :: a = w :: a'' := by simpa using h1
          injection hcons with hvw _
          exact hvnotin (hvw ▸ hw)

/-! ## Duplicate elimination (keeping first occurrences) -/

/-- Remove duplicate elements of a list, keeping each element's first
occurrence.  Used by `enumModel` to guarantee the distinctness of the
reported solutions by construction: domain value lists may contain
duplicates (explicitly enumerated sets such as `var {1, 1}: x;` are
accepted by the checker's semantics), and the emitter's texts are
only distinct modulo injectivity of `emitAssignment`, which this
    development deliberately does not assume (see the proof branch in
    `solver/Emit/Roundtrip.lean`). -/
def dedup {α : Type} [BEq α] : List α → List α
  | [] => []
  | a :: as =>
      let d := dedup as
      if d.contains a then d else a :: d
termination_by l => l.length
decreasing_by decreasing_tactic

/-- `dedup` produces a duplicate-free list. -/
theorem dedup_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), (dedup l).Nodup := by
  intro l
  induction l with
  | nil => rw [dedup]; exact List.nodup_nil
  | cons a as ih =>
      show (dedup (a :: as)).Nodup
      rw [dedup]
      split
      · exact ih
      · next h =>
          rw [List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hmem
          exact h (List.contains_iff_mem.mpr hmem)

/-- `dedup` is membership-preserving in both directions, so the
reported solutions are exactly the enumerated ones. -/
theorem dedup_mem_iff {α : Type} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (l : List α), x ∈ dedup l ↔ x ∈ l := by
  intro l
  induction l with
  | nil =>
      show x ∈ dedup ([] : List α) ↔ x ∈ ([] : List α)
      rw [dedup]
  | cons a as ih =>
      show x ∈ dedup (a :: as) ↔ x ∈ a :: as
      rw [dedup]
      split
      · next hc =>
          have ha : a ∈ dedup as := List.contains_iff_mem.mp hc
          constructor
          · intro h
            exact List.mem_cons_of_mem a (ih.mp h)
          · intro h
            rcases List.mem_cons.mp h with heq | hin
            · exact heq ▸ ha
            · exact ih.mpr hin
      · next hc =>
          constructor
          · intro h
            rcases List.mem_cons.mp h with heq | hin
            · exact heq ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem a (ih.mp hin)
          · intro h
            rcases List.mem_cons.mp h with heq | hin
            · exact heq ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem a (ih.mpr hin)


/-! ## The hash-counted text deduplication (IDEAS 4.5)

`enumModel` dedups the emitted solution *texts* with `dedup`,
whose `contains` scan makes it O(k²) string equality on the number
`k` of reported solutions.  The fast twin below pre-counts every
text once with a `Std.HashMap` (one hash pass), then streams the
list once more, keeping a text exactly when its remaining count is
`1` — which, since the reference `dedup` keeps an element exactly
when it does not occur in the tail, is element-for-element the same
decision.  `dedupTexts_eq` proves the twin is the reference `dedup`
on lists of texts (the equality behind `enumModel`'s use of it),
so the distinctness guarantee `enumModel_nodup` is unchanged. -/

/-- Membership implies a positive count. -/
private theorem texts_one_le_count (a : String) :
    ∀ {l : List String}, a ∈ l → 1 ≤ List.count a l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b bs ih =>
      intro h
      rcases List.mem_cons.mp h with heq | hin
      · rw [heq, List.count_cons_self]; omega
      · have hc : 1 ≤ List.count a bs := ih hin
        by_cases hbx : (b == a) = true
        · rw [List.count_cons, if_pos hbx]; omega
        · rw [List.count_cons, if_neg hbx]; omega

/-- A positive count implies membership. -/
private theorem texts_mem_of_one_le_count (a : String) :
    ∀ {l : List String}, 1 ≤ List.count a l → a ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp only [List.count_nil] at h; omega
  | cons b bs ih =>
      intro h
      by_cases hbx : (b == a) = true
      · apply List.mem_cons.mpr; left; exact (eq_of_beq hbx).symm
      · rw [List.count_cons, if_neg hbx] at h
        apply List.mem_cons.mpr; right; exact ih h

/-- Counting the head leaves the counted element's tally alone. -/
private theorem texts_count_cons_ne {a b : String} (h : b ≠ a)
    (l : List String) : List.count a (b :: l) = List.count a l := by
  rw [List.count_cons]
  have hba : (b == a) = false := by
    by_cases hb : (b == a) = true
    · exact absurd (eq_of_beq hb) h
    · simpa using hb
  rw [hba]; simp

/-- The one-pass counting fold: folding the list into a hash map of
    occurrence counts adds each element's count to the map. -/
private theorem texts_foldl_counts_add :
    ∀ (l' : List String) (m : Std.HashMap String Nat) (y : String),
      (l'.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m).getD y 0
        = List.count y l' + m.getD y 0 := by
  intro l'
  induction l' with
  | nil => intro m y; simp
  | cons x xs ih =>
      intro m y
      rw [List.foldl_cons, ih (m.insert x (m.getD x 0 + 1)) y,
        Std.HashMap.getD_insert]
      by_cases hxy : (x == y) = true
      · rw [if_pos hxy]
        have hxeq : x = y := eq_of_beq hxy
        rw [← hxeq, List.count_cons_self]
        omega
      · rw [if_neg hxy]
        have hcountne : List.count y (x :: xs) = List.count y xs := by
          refine texts_count_cons_ne (a := y) (b := x) (l := xs) ?_
          intro hzx
          exact hxy (by rw [hzx]; simp)
        rw [hcountne]

/-- The streaming dedup loop over the pre-counted texts: keep a
    text when its remaining count is `1` (its last occurrence in the
    stream), decrementing the count either way. -/
private def dedupTextsGo : Std.HashMap String Nat → List String → List String
  | _, [] => []
  | cnts, a :: as =>
      let n := cnts.getD a 0
      if n ≤ 1 then a :: dedupTextsGo (cnts.insert a (n - 1)) as
      else dedupTextsGo (cnts.insert a (n - 1)) as
termination_by _ l => l.length
decreasing_by decreasing_tactic

/-- The counting invariant: when the map agrees with `List.count`
    on the whole remaining list, the loop reproduces the reference
    `dedup` (the keep decision `count a (a :: as) ≤ 1` is exactly
    the reference's `a ∉ as`). -/
private theorem dedupTextsGo_eq :
    ∀ (l : List String) (m : Std.HashMap String Nat),
      (∀ y, m.getD y 0 = List.count y l) → dedupTextsGo m l = dedup l := by
  intro l
  induction l with
  | nil =>
      intro m _
      show dedupTextsGo m [] = _
      rw [dedupTextsGo, dedup]
  | cons x xs ih =>
      intro m hm
      show dedupTextsGo m (x :: xs) = _
      rw [dedupTextsGo]
      have hcx : m.getD x 0 = List.count x xs + 1 := by
        have := hm x
        rwa [List.count_cons_self] at this
      have hxx : (m.insert x (m.getD x 0 - 1)).getD x 0
          = List.count x xs := by
        rw [Std.HashMap.getD_insert_self]
        have := hm x
        rw [List.count_cons_self] at this
        omega
      have hminv : ∀ y, (m.insert x (m.getD x 0 - 1)).getD y 0
          = List.count y xs := by
        intro y
        by_cases hyxeq : x = y
        · rw [← hyxeq]; exact hxx
        · have hyx : (x == y) = false := by
            by_cases hb : (x == y) = true
            · exact absurd (eq_of_beq hb) hyxeq
            · simpa using hb
          rw [Std.HashMap.getD_insert, if_neg (show ¬(x == y) = true by
            intro hcontra; rw [hyx] at hcontra
            exact absurd hcontra (by simp))]
          rw [hm y, texts_count_cons_ne (a := y) (b := x) (l := xs)
            (fun h => hyxeq h.symm.symm)]
      by_cases hle : m.getD x 0 ≤ 1
      · have h0 : List.count x xs = 0 := by omega
        have hxnx : x ∉ xs := fun hmem => by
          have := texts_one_le_count x hmem; omega
        have hxd : ¬ x ∈ dedup xs := fun hc => hxnx ((dedup_mem_iff xs).mp hc)
        have hdd : dedup (x :: xs) = x :: dedup xs := by
          rw [dedup]
          have hc : ¬ (dedup xs).contains x = true := by
            rw [List.contains_iff_mem]
            intro hcontra; exact hxd hcontra
          rw [if_neg hc]
        rw [if_pos hle, hdd, ih _ hminv]
      · have hge : List.count x xs ≥ 1 := by omega
        have hxmem : x ∈ xs := texts_mem_of_one_le_count x hge
        have hxd : x ∈ dedup xs := (dedup_mem_iff xs).mpr hxmem
        have hdd : dedup (x :: xs) = dedup xs := by
          rw [dedup]
          have hc : (dedup xs).contains x = true := by
            rw [List.contains_iff_mem]; exact hxd
          rw [if_pos hc]
        rw [if_neg hle, hdd, ih _ hminv]

/-- The hash-counted twin of `dedup` on solution texts (IDEAS 4.5):
    one counting pass over the list (hash inserts), then one
    streaming pass keeping last occurrences — O(k) hashed
    comparisons instead of `dedup`'s O(k²) string scans. -/
def dedupTexts (l : List String) : List String :=
  dedupTextsGo (l.foldl (fun m x => m.insert x (m.getD x 0 + 1)) {}) l

/-- **The fast text dedup is the reference `dedup`** (IDEAS 4.5's
    proof obligation): the counting loop decides `keep` exactly when
    the reference recursion does, element for element. -/
theorem dedupTexts_eq (l : List String) : dedupTexts l = dedup l := by
  unfold dedupTexts
  refine dedupTextsGo_eq l _ ?_
  intro y
  rw [texts_foldl_counts_add]
  simp


/-! ## `allAssigns` over deduped domains -/

/-- Membership in `allAssigns`, pointwise: an assignment of the slots
is a list of the slot count whose position `i` comes from slot `i`.
(The same characterization `solver/Heuristic.lean` derives privately;
restated here since it is the bridge for domain deduplication.) -/
theorem mem_allAssigns_iff_ptw {α : Type} [Inhabited α] :
    ∀ (slots : List (List α)) (a : List α),
      a ∈ allAssigns slots ↔
        a.length = slots.length ∧
        ∀ i, i < a.length → a.getD i default ∈ slots.getD i [] := by
  intro slots
  induction slots with
  | nil =>
      intro a
      constructor
      · intro ha
        have ha' : a = [] := List.mem_singleton.mp (by simpa [allAssigns] using ha)
        subst ha'
        exact ⟨rfl, fun _ hi => absurd hi (by simp)⟩
      · intro ⟨hlen, _⟩
        cases a with
        | nil => simp [allAssigns]
        | cons w a' =>
            exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
  | cons d ds ih =>
      intro a
      cases d with
      | nil =>
          have hnone : allAssigns (([] : List α) :: ds) = [] := rfl
          rw [hnone]
          constructor
          · intro hmem
            exact absurd hmem (by simp)
          · intro ⟨hlen, hmem⟩
            have hlen' : a.length = ds.length + 1 := by
              simpa only [List.length_cons] using hlen
            have h0 := hmem 0 (by omega)
            rw [List.getD_cons_zero] at h0
            exact absurd h0 (by simp)
      | cons v vs =>
          constructor
          · intro ha
            rw [mem_allAssigns_singleton] at ha
            obtain ⟨w, hw, a', ha', rfl⟩ := ha
            have ih' := (ih a').mp ha'
            refine ⟨?_, ?_⟩
            · simp only [List.length_cons, ih'.1]
            · intro i hi
              cases i with
              | zero =>
                  rw [List.getD_cons_zero, List.getD_cons_zero]
                  exact hw
              | succ j =>
                  have hj : j < a'.length := by
                    simp only [List.length_cons] at hi; omega
                  rw [List.getD_cons_succ, List.getD_cons_succ]
                  exact ih'.2 j hj
          · rintro ⟨hlen, hmem⟩
            have hlen' : a.length = ds.length + 1 := by
              simpa only [List.length_cons] using hlen
            cases a with
            | nil =>
                simp only [List.length_nil] at hlen'
                exact absurd hlen' (by omega)
            | cons w a' =>
                simp only [List.length_cons] at hlen'
                have hw : w ∈ v :: vs := by
                  have h0 := hmem 0 (by simp only [List.length_cons]; omega)
                  rw [List.getD_cons_zero, List.getD_cons_zero] at h0
                  exact h0
                refine (mem_allAssigns_singleton v vs ds (w :: a')).mpr
                  ⟨w, hw, a', (ih a').mpr ⟨by omega, ?_⟩, rfl⟩
                intro i hi
                have hisucc : i + 1 < (w :: a').length := by
                  simp only [List.length_cons]; omega
                have hv := hmem (i + 1) hisucc
                rw [List.getD_cons_succ, List.getD_cons_succ] at hv
                exact hv

/-- Looking up an in-bounds index never falls back to the default. -/
private theorem getD_of_lt' {α : Type} {l : List α} {i : Nat} (d : α)
    (h : i < l.length) : l.getD i d = l[i]'h := by
  have h1 : l[i]? = some (l[i]'h) := List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩
  show (l[i]?.getD d) = l[i]'h
  rw [h1, Option.getD_some]

/-- Looking up an out-of-bounds index falls back to the default. -/
private theorem getD_of_le' {α : Type} {l : List α} {i : Nat} (d : α)
    (h : l.length ≤ i) : l.getD i d = d := by
  have h1 : l[i]? = none := List.getElem?_eq_none_iff.mpr h
  show (l[i]?.getD d) = d
  rw [h1, Option.getD_none]

/-- Looking up an index of a mapped list applies the function to the
looked-up element (the inner fallback is irrelevant in bounds). -/
private theorem getD_map' {α β : Type} (f : α → β) (l : List α) {q : Nat} (d : β) (d' : α)
    (h : q < l.length) : (l.map f).getD q d = f (l.getD q d') := by
  have h1 : q < (l.map f).length := by rw [List.length_map]; exact h
  rw [getD_of_lt' d h1, getD_of_lt' d' h, List.getElem_map]

/-- Deduplicating every slot domain does not change the space of
complete assignments: `allAssigns` over the deduped slots has exactly
the members of `allAssigns` over the originals (pointwise
membership is preserved by `dedup_mem_iff`).  This is what lets
`enumModel` dedup the domains for distinctness while its theorems
keep quantifying over the original domains. -/
theorem allAssigns_dedup_mem {α : Type} [Inhabited α] [BEq α] [LawfulBEq α]
    (slots : List (List α)) (a : List α) :
    a ∈ allAssigns (slots.map dedup) ↔ a ∈ allAssigns slots := by
  have hlen : (slots.map dedup).length = slots.length := by rw [List.length_map]
  have hmap : ∀ i, (slots.map dedup).getD i [] = dedup (slots.getD i []) := by
    intro i
    by_cases hin : i < slots.length
    · exact getD_map' dedup slots (d := []) (d' := []) hin
    · have hle : slots.length ≤ i := by omega
      have hle2 : (slots.map dedup).length ≤ i := by rw [hlen]; exact hle
      have e1 : (slots.map dedup).getD i [] = [] := getD_of_le' [] hle2
      have e2 : slots.getD i [] = [] := getD_of_le' [] hle
      rw [e1, e2, dedup]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (mem_allAssigns_iff_ptw _ a).mp h
    refine (mem_allAssigns_iff_ptw slots a).mpr ⟨?_, ?_⟩
    · rw [h1, hlen]
    · intro i hi
      have hv := h2 i hi
      rw [hmap i] at hv
      exact (dedup_mem_iff _).mp hv
  · intro h
    obtain ⟨h1, h2⟩ := (mem_allAssigns_iff_ptw slots a).mp h
    refine (mem_allAssigns_iff_ptw _ a).mpr ⟨?_, ?_⟩
    · rw [h1, hlen]
    · intro i hi
      rw [hmap i]
      exact (dedup_mem_iff _).mpr (h2 i hi)

/-! ## The FlatZinc-shaped wrapper -/

/-- The result of `enumModel`: the list of all reported solution
texts, a refutation, or a refusal to run.  Mirrors `SolveResult`
with the SAT payload widened to the full list of solution texts
(an empty enumeration is reported as `.unsat`). -/
inductive EnumResult where
  /-- All solutions were enumerated; every carried text is accepted
      by the verified checker (`enumModel_sat_sound`), every accepted
      slot assignment is represented (`enumModel_complete`), and the
      texts are pairwise distinct (`enumModel_nodup`). -/
  | sat (texts : List String)
  /-- Exhaustive enumeration found no accepted assignment. -/
  | unsat
  /-- The model is outside the searched fragment (out-of-fragment
      or capped domains, unsupported predicate, ill-formed). -/
  | unsupported (reason : String)
  deriving Repr, Inhabited

/-- **The all-solutions FlatZinc enumerator.**  Mirrors `solveModel`
gate for gate (`firstUnsupportedFast`, `wellFormedFastB`,
`slotsChecked`), but runs `enumerateAll` with the same leaf predicate
(the prepared twin of `solveLeaf`: emit the candidate solution text
and check it with the verified checker, over a `PreparedModel` built
once per enumeration — `solveLeaf` pointwise by `solveLeafP_eq`) and
reports every accepted emitted text, in the deterministic search
order.  An empty enumeration is reported as `.unsat`.

Two deduplications make the distinctness guarantees hold by
construction (see the module discussion): the slot domains are passed
through `dedup` before searching (duplicated domains can only arise
from explicitly enumerated sets, and `allAssigns` is unchanged as a
set by `allAssigns_dedup_mem`), and the emitted texts are passed
through `dedup` before reporting. -/
def enumModel (m : Model) : EnumResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            let p := prepareModel m
            let names := slots.map Prod.fst
            let doms := (slots.map Prod.snd).map dedup
            let texts := dedupTexts ((enumerateAll (solveLeafP p names) doms []).map
              (emitAssignment names))
            if texts.isEmpty then .unsat else .sat texts
      else
        .unsupported "model is not well-formed"

/-! ## Wrapper theorems -/

/-- `modelSlots m = none` means the slots gate failed: `slotsChecked`
is an error. -/
private theorem slotsChecked_error_of_modelSlots_none {m : Model}
    (h : modelSlots m = none) : ∃ e, slotsChecked m = .error e := by
  rw [show modelSlots m = (slotsChecked m).toOption from rfl] at h
  suffices goal2 : ∀ sc : Except String (List (String × List Value)),
      slotsChecked m = sc → (∃ e, sc = .error e) by
    exact goal2 (slotsChecked m) rfl
  intro sc hsc
  cases sc with
  | error e => exact ⟨e, rfl⟩
  | ok s =>
      rw [hsc] at h
      exact absurd h (by simp [Except.toOption])

/-- `modelSlots m = some slots` implies `slotsChecked m = .ok slots`
(the Option projection inverts). -/
private theorem slotsChecked_ok_of_modelSlots_some {m : Model}
    {slots : List (String × List Value)}
    (h : modelSlots m = some slots) : slotsChecked m = .ok slots := by
  rw [show modelSlots m = (slotsChecked m).toOption from rfl] at h
  suffices goal2 : ∀ sc : Except String (List (String × List Value)),
      slotsChecked m = sc → sc = .ok slots by
    exact goal2 (slotsChecked m) rfl
  intro sc hsc
  cases sc with
  | error e =>
      rw [hsc] at h
      exact absurd h (by simp [Except.toOption])
  | ok s =>
      rw [hsc] at h
      have hs : s = slots := by simpa [Except.toOption] using h
      rw [hs]

/-- The gate structure of `enumModel` unfolded: on a well-formed,
supported model, a `.sat` verdict means the slots extracted cleanly
and the reported list is the deduplicated emission of the
enumeration. -/
private theorem enumModel_gates {m : Model} {texts : List String}
    (h : enumModel m = .sat texts) :
    ∃ slots, slotsChecked m = .ok slots ∧
      texts = dedup ((enumerateAll (solveLeaf m (slots.map Prod.fst))
        (((slots.map Prod.snd).map dedup)) []).map
        (emitAssignment (slots.map Prod.fst))) := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      have hbad : enumModel m = .unsupported s!"unsupported predicate: {n}" := by
        rw [enumModel, huns]
      rw [hbad] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          have hbad : enumModel m = .unsupported "model is not well-formed" := by
            rw [enumModel, huns, hwf]
            rfl
          rw [hbad] at h
          exact absurd h (by simp)
      | true =>
          cases hms : modelSlots m with
          | none =>
              exfalso
              obtain ⟨e, he⟩ := slotsChecked_error_of_modelSlots_none hms
              have hbad : enumModel m = .unsupported e := by
                rw [enumModel, huns, hwf, he]
                rfl
              rw [hbad] at h
              exact absurd h (by simp)
          | some slots =>
              have hslots := slotsChecked_ok_of_modelSlots_some hms
              rw [enumModel, huns, hwf, hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst), dedupTexts_eq] at h
              by_cases hempty :
                (dedup ((enumerateAll (solveLeaf m (slots.map Prod.fst))
                  (((slots.map Prod.snd).map dedup)) []).map
                  (emitAssignment (slots.map Prod.fst)))).isEmpty = true
              · rw [if_pos hempty] at h
                exact absurd h (by simp)
              · rw [if_neg hempty] at h
                exact ⟨slots, hslots, (EnumResult.sat.inj h).symm⟩

/-- Same gate structure for the `unsat` verdict. -/
private theorem enumModel_gates_unsat {m : Model} (h : enumModel m = .unsat) :
    ∃ slots, slotsChecked m = .ok slots ∧
      dedup ((enumerateAll (solveLeaf m (slots.map Prod.fst))
        (((slots.map Prod.snd).map dedup)) []).map
        (emitAssignment (slots.map Prod.fst))) = [] := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      have hbad : enumModel m = .unsupported s!"unsupported predicate: {n}" := by
        rw [enumModel, huns]
      rw [hbad] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          have hbad : enumModel m = .unsupported "model is not well-formed" := by
            rw [enumModel, huns, hwf]
            rfl
          rw [hbad] at h
          exact absurd h (by simp)
      | true =>
          cases hms : modelSlots m with
          | none =>
              exfalso
              obtain ⟨e, he⟩ := slotsChecked_error_of_modelSlots_none hms
              have hbad : enumModel m = .unsupported e := by
                rw [enumModel, huns, hwf, he]
                rfl
              rw [hbad] at h
              exact absurd h (by simp)
          | some slots =>
              have hslots := slotsChecked_ok_of_modelSlots_some hms
              rw [enumModel, huns, hwf, hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst), dedupTexts_eq] at h
              refine ⟨slots, hslots, ?_⟩
              by_cases hempty :
                (dedup ((enumerateAll (solveLeaf m (slots.map Prod.fst))
                  (((slots.map Prod.snd).map dedup)) []).map
                  (emitAssignment (slots.map Prod.fst)))).isEmpty = true
              · cases hl : dedup ((enumerateAll (solveLeaf m (slots.map Prod.fst))
                     (((slots.map Prod.snd).map dedup)) []).map
                     (emitAssignment (slots.map Prod.fst))) with
                | nil => rfl
                | cons a as =>
                    exfalso
                    rw [hl] at hempty
                    simp [List.isEmpty] at hempty
              · rw [if_neg hempty] at h
                exact absurd h (by simp)

/-- **SAT soundness**: every text in a returned solution list is
accepted by the verified front door.  (By
`checkModelSolution_correct`, the model is well formed and the parsed
entries' completed store satisfies `Satisfies fullSig fullInterp`.) -/
theorem enumModel_sat_sound {m : Model} {texts : List String}
    (h : enumModel m = .sat texts) :
    ∀ t ∈ texts, checkModelSolution m t = .accepted := by
  intro t ht
  rw [← checkModelSolutionFast_eq]
  obtain ⟨slots, hslots, htexts⟩ := enumModel_gates h
  rw [htexts] at ht
  have ht2 : t ∈ ((enumerateAll (solveLeaf m (slots.map Prod.fst))
    (((slots.map Prod.snd).map dedup)) []).map
    (emitAssignment (slots.map Prod.fst))) := (dedup_mem_iff _).mp ht
  rw [List.mem_map] at ht2
  obtain ⟨asg, hasg, heq⟩ := ht2
  -- asg passed the leaf, which checked the emitted text
  have hleaf := (enumerateAll_mem_iff_root (solveLeaf m (slots.map Prod.fst))
    (((slots.map Prod.snd).map dedup)) asg).mp hasg
  obtain ⟨_, hleaf'⟩ := hleaf
  simp only [solveLeaf, beq_iff_eq] at hleaf'
  rw [heq] at hleaf'
  exact hleaf'

/-- **Completeness**: every complete assignment of the model's slot
domains whose emitted text the checker accepts is reported in the
solution list. -/
theorem enumModel_complete {m : Model} {texts : List String}
    (h : enumModel m = .sat texts) {asg : List Value}
    (hmem : asg ∈ allAssigns (slotDomains m))
    (hacc : checkModelSolution m (emitAssignment (slotNames m) asg) = .accepted) :
    emitAssignment (slotNames m) asg ∈ texts := by
  obtain ⟨slots, hslots, htexts⟩ := enumModel_gates h
  have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
  obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
  rw [hnames]
  rw [htexts]
  -- the assignment lives in allAssigns over the deduped domains too
  have hmem' : asg ∈ allAssigns (dedup <$> (slots.map Prod.snd)) :=
    (allAssigns_dedup_mem (slots.map Prod.snd) asg).mpr (by
      rw [← hdoms]; exact hmem)
  -- its emitted text is accepted, so it passed the leaf
  have hleaf : solveLeaf m (slots.map Prod.fst) asg = true := by
    rw [hnames] at hacc
    rw [← checkModelSolutionFast_eq] at hacc
    simp only [solveLeaf, beq_iff_eq]
    exact hacc
  have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
      (((slots.map Prod.snd).map dedup)) [] :=
    (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
  exact (dedup_mem_iff _).mpr (List.mem_map_of_mem
    (f := emitAssignment (slots.map Prod.fst)) hin)

/-- **UNSAT soundness**: if `enumModel` returns `unsat`, then no
complete assignment of the model's slot domains yields an accepted
solution. -/
theorem enumModel_unsat {m : Model} (h : enumModel m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  obtain ⟨slots, hslots, htexts⟩ := enumModel_gates_unsat h
  have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
  obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
  -- asg passes the leaf on the deduped domains
  have hmem' : asg ∈ allAssigns (dedup <$> (slots.map Prod.snd)) :=
    (allAssigns_dedup_mem (slots.map Prod.snd) asg).mpr (by
      rw [← hdoms]; exact hmem)
  have hleaf : solveLeaf m (slots.map Prod.fst) asg = true := by
    rw [hnames] at hacc
    rw [← checkModelSolutionFast_eq] at hacc
    simp only [solveLeaf, beq_iff_eq]
    exact hacc
  have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
      (((slots.map Prod.snd).map dedup)) [] :=
    (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
  -- so the emitted text is in the reported list — but the list is empty
  have htext : emitAssignment (slots.map Prod.fst) asg ∈
      (enumerateAll (solveLeaf m (slots.map Prod.fst))
        (((slots.map Prod.snd).map dedup)) []).map
        (emitAssignment (slots.map Prod.fst)) :=
    List.mem_map_of_mem hin
  have : emitAssignment (slots.map Prod.fst) asg ∈ ([] : List String) := by
    rw [← htexts]
    exact (dedup_mem_iff _).mpr htext
  exact absurd this (by simp)

/-- **Distinctness of the reported texts** (PLAN 6.7): the solution
texts reported by `enumModel` are pairwise distinct — by construction
(the reported list is `dedup`-ed), so the guarantee holds
unconditionally, with no hypothesis on the model's domains or names. -/
theorem enumModel_nodup {m : Model} {texts : List String}
    (h : enumModel m = .sat texts) : texts.Nodup := by
  obtain ⟨slots, hslots, htexts⟩ := enumModel_gates h
  rw [htexts]
  exact dedup_nodup _

end LeanFzn.Solver

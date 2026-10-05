/-
File: solver/Direct/Proofs/CompileAux1.lean

Purpose:
  The auxiliary-slot expansion layer of the compiler-correspondence
  proofs, part 1: aux-name freshness, nameIndex append lemmas, the
  expansion pre-pass's spec and membership inversions, the emitted
  aux slots' derived properties, and the per-piece compile
  inversions. Split from Compile.lean (P1c) to bound elaboration
  memory; the statements are unchanged.

Dependencies:
  - solver.Direct.Proofs.CompileCore (the core correspondence
    layer: lookup, store bridge, typing chains, linkers).

DAG:
  solver.Direct.Compile -> CompileCore -> CompileAux1 -> CompileAux2
    -> Compile (re-export shell) -> Exact / Fam.AllDiff
-/

import solver.Direct.Proofs.CompileCore

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core
/-! ## The auxiliary-slot expansion's infrastructure -/

/-! ### Aux-name freshness -/

/-- Pushing a character onto a concatenation concatenates it after
    the second half (the byte-array associativity). -/
theorem strpush_app (s t : String) (c : Char) :
    (s ++ t).push c = s ++ t.push c := by
  refine String.toByteArray_inj.mp ?_
  have hb : ((s ++ t).push c).toByteArray
      = s.toByteArray ++ (t.toByteArray ++ [c].utf8Encode) := by
    show ((s ++ t).toByteArray ++ [c].utf8Encode) = _
    rw [show (s ++ t).toByteArray = s.toByteArray ++ t.toByteArray from rfl]
    simp only [ByteArray.append_assoc]
  rw [hb]
  rfl

/-- The successor aux name: pushing `$` onto the n-th aux name gives
    the (n+1)-th (the dollar-run grows by one). -/
theorem auxName_succ (taken : List String) (n : Nat) :
    (auxName taken n).push '$' = auxName taken (n + 1) := by
  unfold auxName
  rw [show maxStrLength taken + 1 + (n + 1)
      = (maxStrLength taken + 1 + n) + 1 from by omega]
  rw [dollarRun]
  rw [strpush_app]

/-- The successor aux identifier's name is the successor aux name. -/
theorem nextAuxIdent_name (taken : List String) (n : Nat) :
    (nextAuxIdent (Ident.mk (auxName taken n))).name
      = auxName taken (n + 1) := by
  unfold nextAuxIdent
  rw [auxName_succ]

/-- Every taken string's length is dominated by `maxStrLength`. -/
theorem maxStrLength_ge : ∀ (taken : List String) (t : String),
    t ∈ taken → t.length ≤ maxStrLength taken := by
  intro taken
  induction taken with
  | nil => intro t hmem; cases hmem
  | cons a rest ih =>
      intro t hmem
      rw [maxStrLength]
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih t htl) (Nat.le_max_right _ _)

/-- The dollar-run's length is its parameter. -/
theorem dollarRun_length (n : Nat) : (dollarRun n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [dollarRun, String.length_push, ih]

/-- An aux name is strictly longer than every taken name. -/
theorem auxName_length (taken : List String) (n : Nat) :
    (auxName taken n).length = 5 + (maxStrLength taken + 1 + n) := by
  show ("_aux_" ++ dollarRun (maxStrLength taken + 1 + n)).length = _
  rw [String.length_append, dollarRun_length]
  rfl

/-- An aux name is not among the taken names (it is strictly longer
    than every one of them). -/
theorem auxName_not_mem {taken : List String} {n : Nat} :
    auxName taken n ∉ taken := by
  intro hmem
  have hge : (auxName taken n).length ≤ maxStrLength taken :=
    maxStrLength_ge taken _ hmem
  rw [auxName_length] at hge
  omega

/-- Distinct counters give distinct aux names (their lengths
    differ). -/
theorem auxName_inj {taken : List String} {n n' : Nat}
    (h : auxName taken n = auxName taken n') : n = n' := by
  have h1 : (auxName taken n).length = (auxName taken n').length :=
    congrArg String.length h
  rw [auxName_length, auxName_length] at h1
  omega

/-! ### nameIndex append lemmas -/

/-- A name found in the first half is found at the same position in
    the concatenation. -/
theorem nameIndex_append_left {l1 l2 : List String} {s : String}
    {i : Nat} (h : nameIndex l1 s = some i) :
    nameIndex (l1 ++ l2) s = some i := by
  induction l1 generalizing i with
  | nil => simp [nameIndex] at h
  | cons a rest ih =>
      simp only [nameIndex, List.cons_append] at h ⊢
      by_cases hab : a == s
      · rw [if_pos hab] at h ⊢; exact h
      · rw [if_neg hab] at h ⊢
        cases h2 : nameIndex rest s with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some j =>
            rw [h2] at h
            have him := ih h2
            rw [him]
            exact h

/-- A member of a name list is found by `nameIndex`. -/
theorem nameIndex_of_mem {l1 : List String} {s : String}
    (hmem : s ∈ l1) : ∃ i, nameIndex l1 s = some i := by
  induction l1 with
  | nil => cases hmem
  | cons a rest ih =>
      by_cases hab : a == s
      · refine ⟨0, ?_⟩
        simp only [nameIndex]
        rw [if_pos hab]
      · rcases List.mem_cons.mp hmem with rfl | htl
        · exact absurd (beq_iff_eq.mpr rfl) hab
        · obtain ⟨i, hi⟩ := ih htl
          refine ⟨i + 1, ?_⟩
          simp only [nameIndex]
          rw [if_neg hab, hi]
          rfl

/-- A name found in the concatenation is found in one of the
    halves. -/
theorem nameIndex_append_inv {l1 l2 : List String} {s : String}
    {i : Nat} (h : nameIndex (l1 ++ l2) s = some i) :
    nameIndex l1 s = some i ∨
      (∃ j, nameIndex l2 s = some j ∧ i = l1.length + j) := by
  induction l1 generalizing i with
  | nil =>
      simp only [List.nil_append] at h
      exact Or.inr ⟨i, by simpa using h, by simp⟩
  | cons a rest ih =>
      simp only [nameIndex, List.cons_append] at h ⊢
      by_cases hab : a == s
      · rw [if_pos hab] at h ⊢
        exact Or.inl h
      · rw [if_neg hab] at h ⊢
        cases h2 : nameIndex (rest ++ l2) s with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some j =>
            rw [h2] at h
            have hij : j + 1 = i := Option.some.inj h
            rcases ih h2 with h3 | ⟨j2, h3, hjeq⟩
            · exact Or.inl (by rw [h3, Option.map_some]; simp [hij])
            · refine Or.inr ⟨j2, h3, ?_⟩
              simp only [List.length_cons]
              omega

/-- A member of the first half resolves at the same position in the
    concatenation. -/
theorem nameIndex_append_of_mem {l1 l2 : List String} {s : String}
    (hmem : s ∈ l1) : nameIndex (l1 ++ l2) s = nameIndex l1 s := by
  obtain ⟨i, hi⟩ := nameIndex_of_mem hmem
  rw [nameIndex_append_left hi]
  exact hi.symm

/-! ### The expansion pre-pass's spec -/
/-- The emitted aux slots: every slot's name is its own-position aux
    name (the invariant carried from the accumulator: the
    accumulator's own slots must already satisfy it), and every
    EMITTED slot's domain is a singleton (likewise carried). At the
    top level (`auxs = []`) both premises hold vacuously, so the
    emitted list satisfies them outright. -/
theorem expandPlan_aux_spec {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      (∀ i p, auxs[i]? = some p → p.1 = auxName taken i) →
      (∀ p ∈ auxs, ∃ v, p.2 = [v]) →
      (∀ i p, auxs'[i]? = some p → p.1 = auxName taken i) ∧
        (∀ p ∈ auxs', ∃ v, p.2 = [v]) := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h hinvaux hsingle
      have haux : auxs = auxs' := (Prod.mk.injEq _ _ _ _ ▸ h).1
      have hcs : [] = cs' := (Prod.mk.injEq _ _ _ _ ▸ h).2
      subst haux
      subst hcs
      exact ⟨hinvaux, hsingle⟩
  | cons c rest ih =>
      intro auxs auxs' cs' h hinvaux hsingle
      rw [expandPlan] at h
      -- the head's shape classification drives the branch structure
      split at h
      · -- passthrough: no aux slot consumed
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            -- h : (auxs2, c :: cs2) = (auxs', cs')
            obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ c :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            rw [← h1]
            exact ih auxs auxs2 cs2 hrec hinvaux hsingle
      · -- a pinning shape: split on the two pins
        rename_i sh hshape
        split at h
        · -- TWO aux slots (the two-literal times shapes)
          rename_i v v2 hpin hpin2
          simp only [] at h
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              -- the extended accumulator satisfies the name invariant
              have hnew : ∀ i p,
                  (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])])[i]? = some p →
                  p.1 = auxName taken i := by
                intro i p hip
                by_cases hilt : i < auxs.length
                · rw [List.getElem?_append_left hilt] at hip
                  exact hinvaux i p hip
                · have hlen : (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]).length
                      = auxs.length + 2 := by
                    rw [List.length_append, List.length_cons, List.length_singleton]
                  have hilt2 : i < (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]).length := by
                    rw [hlen]
                    have := (List.getElem?_eq_some_iff.mp hip).1
                    omega
                  -- the position is one of the two appended slots
                  have hlt3 : i < auxs.length + 1 ∨ i = auxs.length + 1 := by
                    omega
                  rcases hlt3 with hlt3 | hlt3
                  · -- i = auxs.length: the first appended slot
                    have hieq : i = auxs.length := by omega
                    subst hieq
                    rw [List.getElem?_append_right (Nat.le_refl _)] at hip
                    rw [show auxs.length - auxs.length = 0 from by omega] at hip
                    simp only [List.getElem?_cons_zero, List.getElem?_singleton] at hip
                    exact (Option.some.inj hip).symm ▸ rfl
                  · -- i = auxs.length + 1: the second appended slot
                    have hieq : i = auxs.length + 1 := by omega
                    subst hieq
                    rw [List.getElem?_append_right (by omega)] at hip
                    rw [show auxs.length + 1 - auxs.length = 1 from by omega] at hip
                    simp only [List.getElem?_cons_succ, List.getElem?_singleton] at hip
                    -- the second slot's name IS the successor aux name
                    simp only [if_pos, if_true] at hip
                    rw [auxName_succ] at hip
                    exact (Option.some.inj hip).symm ▸ rfl
              have hnewsingle : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])],
                  ∃ w, p.2 = [w] := by
                intro p hp
                rcases List.mem_append.mp hp with hp' | hp'
                · exact hsingle p hp'
                · rcases List.mem_cons.mp hp' with hp' | hp'
                  · obtain ⟨rfl⟩ : p = (auxName taken auxs.length, [v]) := hp'
                    exact ⟨v, rfl⟩
                  · obtain ⟨rfl⟩ : p = ((auxName taken auxs.length).push '$', [v2]) :=
                    List.mem_singleton.mp hp'
                    exact ⟨v2, rfl⟩
              rw [← h1]
              exact ih (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                hrec hnew hnewsingle
        · -- ONE aux slot
          rename_i v hpin hpin2
          simp only [] at h
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              -- h : (auxs2, sh.expand aux ++ cs2) = (auxs', cs')
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              -- the extended accumulator satisfies the name invariant
              have hnew : ∀ i p,
                  (auxs ++ [(auxName taken auxs.length, [v])])[i]? = some p →
                  p.1 = auxName taken i := by
                intro i p hip
                by_cases hilt : i < auxs.length
                · rw [List.getElem?_append_left hilt] at hip
                  exact hinvaux i p hip
                · have hlen : (auxs ++ [(auxName taken auxs.length, [v])]).length
                      = auxs.length + 1 := by
                    rw [List.length_append, List.length_singleton]
                  have hilt2 : i < (auxs ++ [(auxName taken auxs.length, [v])]).length := by
                    rw [hlen]
                    have := (List.getElem?_eq_some_iff.mp hip).1
                    omega
                  have hlast : i = auxs.length := by omega
                  subst hlast
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hip
                  rw [show auxs.length - auxs.length = 0 from by omega] at hip
                  simp only [List.getElem?_singleton] at hip
                  exact (Option.some.inj hip).symm ▸ rfl
              have hnewsingle : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v])],
                  ∃ w, p.2 = [w] := by
                intro p hp
                rcases List.mem_append.mp hp with hp' | hp'
                · exact hsingle p hp'
                · rw [List.mem_singleton] at hp'
                  obtain ⟨rfl⟩ := hp'
                  exact ⟨v, rfl⟩
              rw [← h1]
              exact ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2
                hrec hnew hnewsingle
        · -- no aux slot (the pin is none)
          cases hrec : expandPlan taken auxs rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              rw [← h1]
              exact ih auxs auxs2 cs2 hrec hinvaux hsingle



/-! ### The expansion pre-pass's membership inversions -/


/-- The expansion only GROWS the aux-slot accumulator: the final
    first component extends the input accumulator (the length only
    increases, and every in-bounds position of the input is
    preserved). -/
theorem expandPlan_aux_grows {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      auxs.length ≤ auxs'.length ∧
        ∀ (i : Nat), i < auxs.length → auxs'[i]? = auxs[i]? := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h
      have haux : auxs = auxs' := (Prod.mk.injEq _ _ _ _ ▸ h).1
      subst haux
      exact ⟨Nat.le_refl _, by intro i _; rfl⟩
  | cons c rest ih =>
      intro auxs auxs' cs' h
      rw [expandPlan] at h
      split at h
      · -- passthrough
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ c :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            subst h1 h2
            exact ih auxs auxs2 cs2 hrec
      · rename_i sh hshape
        split at h
        · -- TWO aux slots (the two-literal times shapes)
          rename_i v v2 hpin hpin2
          simp only [] at h
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              obtain ⟨hge, hagree⟩ :=
                ih (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2 hrec
              have hlen : (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]).length
                  = auxs.length + 2 := by
                rw [List.length_append, List.length_cons, List.length_singleton]
              refine ⟨Nat.le_trans (by rw [hlen]; omega) hge, ?_⟩
              intro i hilt
              have hilt2 : i < (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]).length := by
                rw [hlen]; omega
              have hread := hagree i hilt2
              rw [List.getElem?_append_left hilt] at hread
              exact hread
        · -- ONE aux slot
          rename_i v hpin hpin2
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              obtain ⟨hge, hagree⟩ :=
                ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2 hrec
              have hlen : (auxs ++ [(auxName taken auxs.length, [v])]).length
                  = auxs.length + 1 := by
                rw [List.length_append, List.length_singleton]
              refine ⟨Nat.le_trans (by rw [hlen]; omega) hge, ?_⟩
              intro i hilt
              have hilt2 : i < (auxs ++ [(auxName taken auxs.length, [v])]).length := by
                rw [hlen]; omega
              have hread := hagree i hilt2
              rw [List.getElem?_append_left hilt] at hread
              exact hread
        · -- no aux slot
          rename_i hpin2
          cases hrec : expandPlan taken auxs rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              exact ih auxs auxs2 cs2 hrec

/-- **The expansion's completeness**: every pinning shape's every
    piece is in the expanded list (the forward half the coverage
    direction needs). The pin clause carries the SECOND pinned slot
    of the two-literal times shapes (`pin2 = none` for all other
    shapes, so the second disjunct is then vacuous). -/
theorem expandPlan_pieces_mem {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      ∀ c ∈ cs, ∀ sh : AuxShape, auxShapeOf c = some sh →
        ∃ i : Nat, ∀ c' ∈ sh.expand (Ident.mk (auxName taken i)), c' ∈ cs' ∧
          (sh.pin = none ∨
            ∃ v, sh.pin = some v ∧ auxs'[i]? = some (auxName taken i, [v])) ∧
          (sh.pin2 = none ∨
            ∃ v2, sh.pin2 = some v2 ∧
              auxs'[i + 1]? = some (auxName taken (i + 1), [v2])) := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h c hc _ hshape
      cases hc
  | cons c rest ih =>
      intro auxs auxs' cs' h c0 hc0mem sh hshape
      rcases List.mem_cons.mp hc0mem with rfl | htl
      · -- c0 is the head: its own expansion's pieces
        rw [expandPlan] at h
        split at h
        · -- the head is not a pinning shape: contradiction with hshape
          rename_i hshapeNone
          rw [hshapeNone] at hshape
          exact absurd hshape (by simp)
        · -- a pinning shape: split on the two pins
          rename_i sh2 hshape2
          rw [hshape2] at hshape
          rw [Option.some.inj hshape] at *
          split at h
          · -- TWO aux slots (the two-literal times shapes)
            rename_i v v2 hpin hpin2
            simp only [] at h
            cases hrec : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                obtain ⟨hge2, hagree2⟩ :=
                  expandPlan_aux_grows rest
                    (auxs ++ [(auxName taken auxs.length, [v]),
                       ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2 hrec
                have hlen : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]).length
                    = auxs.length + 2 := by
                  rw [List.length_append, List.length_cons, List.length_singleton]
                have hpos1 : auxs.length
                    < (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]).length := by
                  rw [hlen]; omega
                have hpos2 : auxs.length + 1
                    < (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]).length := by
                  rw [hlen]; omega
                have haccget1 : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length]?
                    = some (auxName taken auxs.length, [v]) := by
                  have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length]?
                      = [(auxName taken auxs.length, [v]),
                        ((auxName taken auxs.length).push '$', [v2])][auxs.length - auxs.length]? :=
                    List.getElem?_append_right (l₁ := auxs)
                      (l₂ := [(auxName taken auxs.length, [v]),
                        ((auxName taken auxs.length).push '$', [v2])]) (Nat.le_refl _)
                  rw [hstep]
                  rw [show auxs.length - auxs.length = 0 from by omega]
                  simp
                have haccget2 : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                    = some ((auxName taken auxs.length).push '$', [v2]) := by
                  have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                      = [(auxName taken auxs.length, [v]),
                        ((auxName taken auxs.length).push '$', [v2])][auxs.length + 1 - auxs.length]? :=
                    List.getElem?_append_right (l₁ := auxs)
                      (l₂ := [(auxName taken auxs.length, [v]),
                        ((auxName taken auxs.length).push '$', [v2])]) (by omega)
                  rw [hstep]
                  rw [show auxs.length + 1 - auxs.length = 1 from by omega]
                  simp
                have hslotget1 : auxs2[auxs.length]?
                    = some (auxName taken auxs.length, [v]) := by
                  have hpres := hagree2 auxs.length hpos1
                  rw [haccget1] at hpres
                  exact hpres
                have hslotget2 : auxs2[auxs.length + 1]?
                    = some ((auxName taken auxs.length).push '$', [v2]) := by
                  have hpres := hagree2 (auxs.length + 1) hpos2
                  rw [haccget2] at hpres
                  exact hpres
                refine ⟨auxs.length, fun c' hc'mem =>
                  ⟨List.mem_append.mpr (Or.inl hc'mem),
                    Or.inr ⟨v, hpin, hslotget1⟩, ?_⟩⟩
                -- the second pin: the successor slot's name IS the
                -- successor aux name
                rw [auxName_succ] at hslotget2
                exact Or.inr ⟨v2, hpin2, hslotget2⟩
          · -- ONE aux slot
            rename_i v hpin hpin2
            cases hrec : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                obtain ⟨hge2, hagree2⟩ :=
                  expandPlan_aux_grows rest
                    (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2 hrec
                have hlen : (auxs ++ [(auxName taken auxs.length, [v])]).length
                    = auxs.length + 1 := by
                  rw [List.length_append, List.length_singleton]
                have hpos : auxs.length
                    < (auxs ++ [(auxName taken auxs.length, [v])]).length := by
                  rw [hlen]; omega
                have haccget : (auxs ++ [(auxName taken auxs.length, [v])])[auxs.length]?
                    = some (auxName taken auxs.length, [v]) := by
                  have hstep : (auxs ++ [(auxName taken auxs.length, [v])])[auxs.length]?
                      = [(auxName taken auxs.length, [v])][auxs.length - auxs.length]? :=
                    List.getElem?_append_right (l₁ := auxs)
                      (l₂ := [(auxName taken auxs.length, [v])]) (Nat.le_refl _)
                  rw [hstep]
                  rw [show auxs.length - auxs.length = 0 from by omega]
                  simp
                have hslotget : auxs2[auxs.length]?
                    = some (auxName taken auxs.length, [v]) := by
                  have hpres := hagree2 auxs.length hpos
                  rw [haccget] at hpres
                  exact hpres
                refine ⟨auxs.length, fun c' hc'mem =>
                  ⟨List.mem_append.mpr (Or.inl hc'mem),
                    Or.inr ⟨v, hpin, hslotget⟩, ?_⟩⟩
                -- pin2 = none (the one-slot shapes): vacuous
                rename_i hpin2
                exact Or.inl hpin2
          · -- no aux slot
            rename_i hpin hpin2
            cases hrec : expandPlan taken auxs rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                refine ⟨auxs.length, fun c' hc'mem =>
                  ⟨List.mem_append.mpr (Or.inl hc'mem), ?_, ?_⟩⟩
                · -- sh.pin = none in this arm
                  cases hpn : sh.pin with
                  | none => exact Or.inl rfl
                  | some v =>
                      exfalso
                      cases hpn2 : sh.pin2 with
                      | none => exact hpin2 v hpn hpn2
                      | some v2 => exact hpin v v2 hpn hpn2
                · -- sh.pin2 = some only for the two-literal times
                  -- shapes, whose pin is also some — excluded above
                  cases hpn2 : sh.pin2 with
                  | none => exact Or.inl rfl
                  | some v2 =>
                      exfalso
                      cases hpn : sh.pin with
                      | none =>
                          -- pin2 = some forces pin = some (the
                          -- three two-literal shapes all pin both)
                          cases sh <;>
                            simp [AuxShape.pin, AuxShape.pin2] at hpn hpn2
                      | some v => exact hpin v v2 hpn hpn2
      · -- c0 is in the tail: the tail's own recursion
        rw [expandPlan] at h
        split at h
        · rename_i hshapeNone
          cases hrec : expandPlan taken auxs rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ c :: cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              obtain ⟨i, hall⟩ := ih auxs auxs2 cs2 hrec c0 htl sh hshape
              refine ⟨i, fun c' hc'mem => ⟨List.mem_cons_of_mem _ (hall c' hc'mem).1,
                (hall c' hc'mem).2.1, (hall c' hc'mem).2.2⟩⟩
        · rename_i sh2 hshape2
          split at h
          · -- TWO aux slots
            rename_i v v2 hpin hpin2
            simp only [] at h
            cases hrec : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh2.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                obtain ⟨i, hall⟩ :=
                  ih (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2 hrec
                    c0 htl sh hshape
                refine ⟨i, fun c' hc'mem => ⟨List.mem_append.mpr (Or.inr (hall c' hc'mem).1),
                  (hall c' hc'mem).2.1, (hall c' hc'mem).2.2⟩⟩
          · -- ONE aux slot
            rename_i v hpin hpin2
            cases hrec : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh2.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                obtain ⟨i, hall⟩ :=
                  ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2 hrec c0 htl sh hshape
                refine ⟨i, fun c' hc'mem => ⟨List.mem_append.mpr (Or.inr (hall c' hc'mem).1),
                  (hall c' hc'mem).2.1, (hall c' hc'mem).2.2⟩⟩
          · rename_i hpin
            cases hrec : expandPlan taken auxs rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh2.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                obtain ⟨i, hall⟩ := ih auxs auxs2 cs2 hrec c0 htl sh hshape
                refine ⟨i, fun c' hc'mem => ⟨List.mem_append.mpr (Or.inr (hall c' hc'mem).1),
                  (hall c' hc'mem).2.1, (hall c' hc'mem).2.2⟩⟩


/-! ### The emitted aux slots' derived properties -/

/-- The pin values of the shapes are ints or bools. -/
theorem auxShape_pin_valued (sh : AuxShape) (v : Value)
    (h : sh.pin = some v) :
    (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) := by
  cases sh with
  | timesRK x y k =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | timesKR x y k =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | timesKR' x y k =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | timesRKK x k k2 =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | timesKRR x k k2 =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | timesKKR x k k2 =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | neRK x k =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | neKR x k =>
      rw [AuxShape.pin] at h
      have hvv : Value.int k = v := (Option.some.inj h)
      exact Or.inl ⟨k, hvv.symm⟩
  | andFalse x y =>
      rw [AuxShape.pin] at h
      have hvv : Value.bool false = v := (Option.some.inj h)
      exact Or.inr ⟨false, hvv.symm⟩
  | orTrue x y =>
      rw [AuxShape.pin] at h
      have hvv : Value.bool true = v := (Option.some.inj h)
      exact Or.inr ⟨true, hvv.symm⟩
  | andTrue x y => rw [AuxShape.pin] at h; cases h
  | orFalse x y => rw [AuxShape.pin] at h; cases h

/-- The second pin values are ints. -/
theorem auxShape_pin2_valued (sh : AuxShape) (v : Value)
    (h : sh.pin2 = some v) :
    (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) := by
  cases sh with
  | timesRK x y k => simp [AuxShape.pin2] at h
  | timesKR x y k => simp [AuxShape.pin2] at h
  | timesKR' x y k => simp [AuxShape.pin2] at h
  | timesRKK x k k2 =>
      rw [AuxShape.pin2] at h
      have hvv : Value.int k2 = v := (Option.some.inj h)
      exact Or.inl ⟨k2, hvv.symm⟩
  | timesKRR x k k2 =>
      rw [AuxShape.pin2] at h
      have hvv : Value.int k2 = v := (Option.some.inj h)
      exact Or.inl ⟨k2, hvv.symm⟩
  | timesKKR x k k2 =>
      rw [AuxShape.pin2] at h
      have hvv : Value.int k2 = v := (Option.some.inj h)
      exact Or.inl ⟨k2, hvv.symm⟩
  | neRK x k => simp [AuxShape.pin2] at h
  | neKR x k => simp [AuxShape.pin2] at h
  | andFalse x y => simp [AuxShape.pin2] at h
  | orTrue x y => simp [AuxShape.pin2] at h
  | andTrue x y => simp [AuxShape.pin2] at h
  | orFalse x y => simp [AuxShape.pin2] at h

/-- The emitted aux slots' singleton values are ints or bools. -/
theorem expandPlan_aux_pinval {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      (∀ p ∈ auxs, ∀ v, p.2 = [v] →
        (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b)) →
      ∀ p ∈ auxs', ∀ v, p.2 = [v] →
        (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h hall p hp hv
      have haux : auxs = auxs' := (Prod.mk.injEq _ _ _ _ ▸ h).1
      exact hall p (haux ▸ hp) hv
  | cons c rest ih =>
      intro auxs auxs' cs' h hall p hp hv
      rw [expandPlan] at h
      split at h
      · -- passthrough
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ c :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            exact ih auxs auxs2 cs2 hrec hall p (h1 ▸ hp) hv
      · -- a pinning shape
        rename_i sh hshape
        split at h
        · -- TWO aux slots (the pins are int/bool by the shapes)
          rename_i v v2 hpin hpin2
          have hvpin : (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) :=
            auxShape_pin_valued sh v hpin
          have hvpin2 : (∃ k, v2 = Value.int k) ∨ (∃ b, v2 = Value.bool b) :=
            auxShape_pin2_valued sh v2 hpin2
          have hnew : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])],
              ∀ v3, p.2 = [v3] →
              (∃ k, v3 = Value.int k) ∨ (∃ b, v3 = Value.bool b) := by
            intro p hp2 v3 hv3
            rcases List.mem_append.mp hp2 with htl | hlast
            · exact hall p htl v3 hv3
            · rcases List.mem_cons.mp hlast with hlast | hlast
              · obtain ⟨rfl⟩ : p = (auxName taken auxs.length, [v]) := hlast
                have hvs : [v] = [v3] := hv3
                have hvv : v = v3 := by
                  injection hvs
                exact hvv ▸ hvpin
              · obtain ⟨rfl⟩ : p = ((auxName taken auxs.length).push '$', [v2]) :=
                  List.mem_singleton.mp hlast
                have hvs : [v2] = [v3] := hv3
                have hvv : v2 = v3 := by
                  injection hvs
                exact hvv ▸ hvpin2
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) rest with
          | mk auxs2 cs2 =>
              simp only [hrec] at h
              obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ _ = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              exact ih _ auxs2 cs2 hrec hnew p (h1 ▸ hp) hv
        · -- ONE aux slot (the pin is int/bool by the shape)
          rename_i hpin hneq2
          -- hpin : sh.pin = some v✝ for an inaccessible value;
          -- generalize it and substitute into the goal
          generalize hpin : sh.pin = op at *
          cases op with
          | none => exact absurd hpin (by simp)
          | some v =>
              -- hpin : some v = some v✝; identify v with v✝ so the
              -- goal's occurrences of v✝ become v
              have hvv := Option.some.inj hpin
              subst hvv
              -- the pre-generalization equation survives as hpin✝
              rename_i hpin0
              have hvpin : (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) :=
                auxShape_pin_valued sh v hpin0
              have hnew : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v])],
                  ∀ v2, p.2 = [v2] →
                  (∃ k, v2 = Value.int k) ∨ (∃ b, v2 = Value.bool b) := by
                intro p hp2 v2 hv2
                rcases List.mem_append.mp hp2 with htl | hlast
                · exact hall p htl v2 hv2
                · obtain ⟨rfl⟩ : p = (auxName taken auxs.length, [v]) :=
                    List.mem_singleton.mp hlast
                  have hvs : [v] = [v2] := hv2
                  have hvv : v = v2 := by
                    injection hvs
                  exact hvv ▸ hvpin
              cases hrec : expandPlan taken
                  (auxs ++ [(auxName taken auxs.length, [v])]) rest with
              | mk auxs2 cs2 =>
                  simp only [hrec] at h
                  obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ _ = cs' := by
                    simpa using h
                  exact ih _ auxs2 cs2 hrec hnew p (h1 ▸ hp) hv
        · -- no aux slot
          rename_i hpin
          cases hrec : expandPlan taken auxs rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ _ = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              exact ih auxs auxs2 cs2 hrec hall p (h1 ▸ hp) hv

/-- Every member of the expanded list is either an original constraint
    or a piece of some pinning shape (with the shape's aux slot at the
    piece's position: either a pinned singleton or no slot at all;
    the two-literal times shapes' pieces additionally carry their
    SECOND pinned slot at the successor position). -/
theorem expandPlan_origin {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      ∀ c' ∈ cs', c' ∈ cs ∨
        ∃ c ∈ cs, ∃ sh : AuxShape, auxShapeOf c = some sh ∧
          ∃ i, auxs.length ≤ i ∧
            c' ∈ sh.expand (Ident.mk (auxName taken i)) ∧
            (sh.pin = none ∨ ∃ v, sh.pin = some v ∧
              auxs'[i]? = some (auxName taken i, [v])) ∧
            (sh.pin2 = none ∨ ∃ v2, sh.pin2 = some v2 ∧
              auxs'[i + 1]? = some (auxName taken (i + 1), [v2])) := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h c' hc'
      have hcs : [] = cs' := (Prod.mk.injEq _ _ _ _ ▸ h).2
      subst hcs
      exact absurd hc' (by simp)
  | cons c rest ih =>
      intro auxs auxs' cs' h c' hc'
      rw [expandPlan] at h
      split at h
      · -- the head passes through
        rename_i hshapeNone
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ c :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            subst h1 h2
            rcases List.mem_cons.mp hc' with rfl | htl
            · exact Or.inl List.mem_cons_self
            · rcases ih auxs auxs2 cs2 hrec c' htl with horig |
                ⟨c2, hc2mem, sh, hshape2, i, hge, hmem, hslot⟩
              · exact Or.inl (List.mem_cons_of_mem _ horig)
              · obtain ⟨hp1, hp2⟩ := hslot
                exact Or.inr ⟨c2, List.mem_cons_of_mem _ hc2mem, sh, hshape2,
                  i, hge, hmem, hp1, hp2⟩
      · -- the head is a pinning shape
        rename_i sh hshape2
        split at h
        · -- TWO aux slots (the two-literal times shapes)
          rename_i v v2 hpin hpin2
          simp only [] at h
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              -- the two appended slots' positioned reads (of auxs')
              have hlen : (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]).length
                  = auxs.length + 2 := by
                rw [List.length_append, List.length_cons, List.length_singleton]
              obtain ⟨hge2, hagree2⟩ :=
                expandPlan_aux_grows rest
                  (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2 hrec
              have haccget1 : (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])])[auxs.length]?
                  = some (auxName taken auxs.length, [v]) := by
                have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length]?
                    = [(auxName taken auxs.length, [v]),
                       ((auxName taken auxs.length).push '$', [v2])][auxs.length - auxs.length]? :=
                  List.getElem?_append_right (l₁ := auxs)
                    (l₂ := [(auxName taken auxs.length, [v]),
                       ((auxName taken auxs.length).push '$', [v2])]) (Nat.le_refl _)
                rw [hstep]
                rw [show auxs.length - auxs.length = 0 from by omega]
                simp
              have haccget2 : (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                  = some ((auxName taken auxs.length).push '$', [v2]) := by
                have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                    = [(auxName taken auxs.length, [v]),
                       ((auxName taken auxs.length).push '$', [v2])][auxs.length + 1 - auxs.length]? :=
                  List.getElem?_append_right (l₁ := auxs)
                    (l₂ := [(auxName taken auxs.length, [v]),
                       ((auxName taken auxs.length).push '$', [v2])]) (by omega)
                rw [hstep]
                rw [show auxs.length + 1 - auxs.length = 1 from by omega]
                simp
              have hslot1 : auxs2[auxs.length]?
                  = some (auxName taken auxs.length, [v]) := by
                have hpres := hagree2 auxs.length (by rw [hlen]; omega)
                rw [haccget1] at hpres
                exact hpres
              have hslot2 : auxs2[auxs.length + 1]?
                  = some ((auxName taken auxs.length).push '$', [v2]) := by
                have hpres := hagree2 (auxs.length + 1) (by rw [hlen]; omega)
                rw [haccget2] at hpres
                exact hpres
              rcases List.mem_append.mp hc' with hpiece | htl
              · -- a piece of the head's shape: both slots positioned
                refine Or.inr ⟨c, List.mem_cons_self, sh, hshape2, auxs.length,
                  Nat.le_refl _, hpiece, ⟨Or.inr ⟨v, hpin, hslot1⟩, ?_⟩⟩
                -- the second slot's name IS the successor aux name
                show sh.pin2 = none ∨ ∃ v2, sh.pin2 = some v2 ∧
                    auxs2[auxs.length + 1]? =
                      some ((auxName taken auxs.length).push '$', [v2])
                exact Or.inr ⟨v2, hpin2, hslot2⟩
              · -- from the tail: positions are at or beyond the two
                -- newly consumed slots
                rcases ih (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                    hrec c' htl with horig |
                    ⟨c2, hc2mem, sh2, hshape3, i, hge, hmem, hslot⟩
                · exact Or.inl (List.mem_cons_of_mem _ horig)
                · obtain ⟨hp1, hp2⟩ := hslot
                  refine Or.inr ⟨c2, List.mem_cons_of_mem _ hc2mem, sh2, hshape3,
                    i, ?_, hmem, hp1, hp2⟩
                  rw [hlen] at hge
                  omega
        · -- ONE aux slot
          rename_i v hpin hpin2
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              rcases List.mem_append.mp hc' with hpiece | htl
              · -- a piece of the head's shape: the slot is positioned
                refine Or.inr ⟨c, List.mem_cons_self, sh, hshape2, auxs.length,
                  Nat.le_refl _, hpiece, ⟨Or.inr ⟨v, hpin, ?_⟩, ?_⟩⟩
                · -- the final list's slot at auxs.length (grows)
                  obtain ⟨hge2, hagree2⟩ :=
                    expandPlan_aux_grows rest
                      (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2 hrec
                  have haccget : (auxs ++ [(auxName taken auxs.length, [v])])[auxs.length]?
                      = some (auxName taken auxs.length, [v]) := by
                    have hstep : (auxs ++ [(auxName taken auxs.length, [v])])[auxs.length]?
                        = [(auxName taken auxs.length, [v])][auxs.length - auxs.length]? :=
                      List.getElem?_append_right (l₁ := auxs)
                        (l₂ := [(auxName taken auxs.length, [v])]) (Nat.le_refl _)
                    rw [hstep]
                    rw [show auxs.length - auxs.length = 0 from by omega]
                    simp
                  rw [← haccget]
                  exact hagree2 auxs.length (by
                    rw [List.length_append, List.length_singleton]
                    omega)
                · -- pin2 = none (the one-slot shapes): the arm's
                  -- own hypothesis states it directly
                  exact Or.inl hpin2
              · -- from the tail: positions are at or beyond the
                -- newly consumed slot
                rcases ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2
                    hrec c' htl with horig |
                    ⟨c2, hc2mem, sh2, hshape3, i, hge, hmem, hslot⟩
                · exact Or.inl (List.mem_cons_of_mem _ horig)
                · obtain ⟨hp1, hp2⟩ := hslot
                  refine Or.inr ⟨c2, List.mem_cons_of_mem _ hc2mem, sh2, hshape3,
                    i, ?_, hmem, hp1, hp2⟩
                  have hlennew : (auxs ++ [(auxName taken auxs.length, [v])]).length
                      = auxs.length + 1 := by
                    rw [List.length_append, List.length_singleton]
                  rw [hlennew] at hge
                  omega
        · -- no aux slot (andTrue/orFalse: the pieces have no pin)
          rename_i hpin hpin2
          cases hrec : expandPlan taken auxs rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                  sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              subst h1 h2
              rcases List.mem_append.mp hc' with hpiece | htl
              · refine Or.inr ⟨c, List.mem_cons_self, sh, hshape2, auxs.length,
                  Nat.le_refl _, hpiece, ?_, ?_⟩
                · -- sh.pin = none in this arm (the some/some and
                  -- some/none patterns above were excluded)
                  cases hpn : sh.pin with
                  | none => exact Or.inl rfl
                  | some v =>
                      exfalso
                      cases hpn2 : sh.pin2 with
                      | none => exact hpin2 v hpn hpn2
                      | some v2 => exact hpin v v2 hpn hpn2
                · -- sh.pin2 = some only for the two-literal times
                  -- shapes, whose pin is also some — excluded above
                  cases hpn2 : sh.pin2 with
                  | none => exact Or.inl rfl
                  | some v2 =>
                      exfalso
                      cases hpn : sh.pin with
                      | none =>
                          cases sh <;>
                            simp [AuxShape.pin, AuxShape.pin2] at hpn hpn2
                      | some v => exact hpin v v2 hpn hpn2
              · rcases ih auxs auxs2 cs2 hrec c' htl with horig |
                  ⟨c2, hc2mem, sh2, hshape3, i, hge, hmem, hslot⟩
                · exact Or.inl (List.mem_cons_of_mem _ horig)
                · obtain ⟨hp1, hp2⟩ := hslot
                  exact Or.inr ⟨c2, List.mem_cons_of_mem _ hc2mem, sh2, hshape3,
                    i, hge, hmem, hp1, hp2⟩

/-- The model's aux slots' singleton pin values are ints or bools
    (the nine pinning shapes' pins). -/
theorem modelAuxSlots_pinval {m : Model}
    {slots0 : List (String × List Value)}
    (hslot : slotsChecked m = .ok slots0) :
    ∀ p ∈ modelAuxSlots m, ∀ v, p.2 = [v] →
      (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) := by
  have hplan : expandPlan (auxTaken m slots0) [] m.constraints
      = (modelAuxSlots m, modelExpand m) := by
    have h1 := modelAuxSlots_eq hslot
    have h2 := modelExpand_eq hslot
    rw [h1, h2]
  exact expandPlan_aux_pinval m.constraints [] (modelAuxSlots m)
    (modelExpand m) hplan (by intro p hp; cases hp)

/-- The aux slots of a model-level expansion: every slot's name is
    its own-position name and its domain is a singleton. -/
theorem modelAuxSlots_spec {m : Model} {slots0 : List (String × List Value)}
    (hslot : slotsChecked m = .ok slots0) :
    (∀ i p, (modelAuxSlots m)[i]? = some p → p.1 = auxName (auxTaken m slots0) i) ∧
      (∀ p ∈ modelAuxSlots m, ∃ v, p.2 = [v]) := by
  have hplan : expandPlan (auxTaken m slots0) [] m.constraints
      = (modelAuxSlots m, modelExpand m) := by
    have h1 := modelAuxSlots_eq hslot
    have h2 := modelExpand_eq hslot
    rw [h1, h2]
  obtain ⟨hnames, hsingle⟩ :=
    expandPlan_aux_spec m.constraints [] (modelAuxSlots m) (modelExpand m) hplan
    (by intro i p hp; cases hp) (by intro p hp; cases hp)
  exact ⟨hnames, hsingle⟩

/-- Positioned aux slots have pairwise-distinct names: the names
    encode the positions in their lengths. -/
theorem auxSlots_nodup {taken : List String} :
    ∀ (auxs : List (String × List Value)),
      (∀ i p, auxs[i]? = some p → p.1 = auxName taken i) →
      (auxs.map Prod.fst).Nodup := by
  intro auxs hspec
  -- a shifted positioning of the tail
  have main : ∀ (l : List (String × List Value)) (off : Nat),
      (∀ i p, l[i]? = some p → p.1 = auxName taken (off + i)) →
      (l.map Prod.fst).Nodup := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons a rest ih =>
        intro off hspec'
        rw [List.map_cons, List.nodup_cons]
        have hshift : ∀ i p, rest[i]? = some p → p.1 = auxName taken (off + 1 + i) := by
          intro i p hp
          have := hspec' (i + 1) p (by rw [List.getElem?_cons_succ]; exact hp)
          simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using this
        refine ⟨?_, ih (off + 1) hshift⟩
        intro hmem
        -- the head's name is at offset off; every tail name is at a
        -- strictly greater offset — distinct by the length encoding
        obtain ⟨p, hpmem, hget⟩ := List.mem_map.mp hmem
        obtain ⟨k, hklt, hkget⟩ := slot_getElem!_of_mem rest p hpmem
        have hhead : a.1 = auxName taken off := hspec' 0 a (by simp)
        have htail : p.1 = auxName taken (off + 1 + k) := by
          have := hspec' (k + 1) p (by
            rw [List.getElem?_cons_succ, show rest[k]? = some rest[k]! from by
              rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
              rfl]
            rw [hkget])
          simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using this
        rw [hget, hhead] at htail
        exact absurd (auxName_inj htail) (by omega)
  exact main auxs 0 (fun i p hp => by simpa using hspec i p hp)


/-- The combined slot-name list of an aux-extended model is
    distinct: the model's slot names are distinct, and the aux names
    are fresh (not among the model's slot OR parameter names) and
    pairwise distinct. -/
theorem extendedSlotNames_nodup {m : Model}
    {slots0 auxs : List (String × List Value)}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hauxs : modelAuxSlots m = auxs) :
    ((slots0 ++ auxs).map Prod.fst).Nodup := by
  -- the two halves' names
  have hmodel : (slots0.map Prod.fst).Nodup := slotNames_nodup hwf hslot
  have hspec : ∀ i p, auxs[i]? = some p → p.1 = auxName (auxTaken m slots0) i := by
    rw [← hauxs]
    exact (modelAuxSlots_spec hslot).1
  have haux : (auxs.map Prod.fst).Nodup := auxSlots_nodup auxs hspec
  -- disjointness: aux names are longer than every taken name
  have hdisj : ∀ x ∈ auxs.map Prod.fst, x ∉ slots0.map Prod.fst := by
    intro x hxmem
    obtain ⟨p, hpmem, hget⟩ := List.mem_map.mp hxmem
    obtain ⟨i, hilt, higet⟩ := slot_getElem!_of_mem auxs p hpmem
    have hsome : auxs[i]? = some p := by
      rw [show auxs[i]? = auxs[i]! from by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hilt]
        rfl, higet]
    have hname : p.1 = auxName (auxTaken m slots0) i := hspec i p hsome
    -- the taken list contains the slot names
    have hsub : slots0.map Prod.fst ⊆ auxTaken m slots0 := by
      intro t ht
      exact List.mem_append.mpr (Or.inl ht)
    have hnotmem : p.1 ∉ auxTaken m slots0 := by
      rw [hname]
      exact auxName_not_mem
    intro hcontra
    rw [hname] at hnotmem
    have hmem2 : p.1 ∈ auxTaken m slots0 := by
      apply hsub
      rw [← hget] at hcontra
      exact hcontra
    rw [hname] at hmem2
    exact hnotmem hmem2
  -- the append's Nodup from the two halves
  have main : ∀ (l1 l2 : List String), l1.Nodup → l2.Nodup →
      (∀ x ∈ l2, x ∉ l1) → (l1 ++ l2).Nodup := by
    intro l1
    induction l1 with
    | nil => intro l2 h1 h2 _; simpa using h2
    | cons a rest ih =>
        intro l2 h1 h2 hdisj'
        rw [List.nodup_cons] at h1
        rw [List.cons_append, List.nodup_cons]
        refine ⟨?_, ih l2 h1.2 h2 (fun x hx hmemx => hdisj' x hx (List.mem_cons_of_mem _ hmemx))⟩
        intro hmem
        rcases List.mem_append.mp hmem with hhead | htl
        · exact absurd hhead h1.1
        · exact hdisj' a htl (List.mem_cons_self)
  rw [List.map_append]
  exact main _ _ hmodel haux hdisj


/-! ### The per-piece compile inversions (the expansion pieces'
    compiled forms) -/

/-- A three-identifier `int_times` constraint whose names all
    resolve compiles to exactly the `timesSlot` over the resolved
    positions. -/
theorem compileConstraint_int_times3 {env : Store} {names : List String}
    {x y z : Ident} {i j k : Nat} {dc : DomConstraint}
    (hxi : nameIndex names x.name = some i)
    (hyi : nameIndex names y.name = some j)
    (hzi : nameIndex names z.name = some k)
    (h : compileConstraint env names
        { name := Ident.mk "int_times"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    dc = .timesSlot i j k := by
  have hex : extractConstraint names
      { name := Ident.mk "int_times"
      , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
      , anns := [] } = some (.timesSlot i j k) := by
    simp only [extractConstraint, hxi, hyi, hzi]
  unfold compileConstraint at h
  rw [hex] at h
  exact (Except.ok.inj h).symm

/-- A two-identifier `int_ne` constraint whose names both resolve
    compiles to exactly the `neSlot` over the resolved positions. -/
theorem compileConstraint_int_ne2 {env : Store} {names : List String}
    {x y : Ident} {i j : Nat} {dc : DomConstraint}
    (hxi : nameIndex names x.name = some i)
    (hyi : nameIndex names y.name = some j)
    (h : compileConstraint env names
        { name := Ident.mk "int_ne"
        , args := [.basic (.ident x), .basic (.ident y)]
        , anns := [] } = .ok dc) :
    dc = .neSlot i j := by
  have hex : extractConstraint names
      { name := Ident.mk "int_ne"
      , args := [.basic (.ident x), .basic (.ident y)]
      , anns := [] } = some (.neSlot i j) := by
    simp only [extractConstraint, hxi, hyi]
  unfold compileConstraint at h
  rw [hex] at h
  exact (Except.ok.inj h).symm

/-- A three-identifier `bool_and` constraint whose names all resolve
    compiles to exactly the `boolAndSlot` over the resolved
    positions. -/
theorem compileConstraint_bool_and3 {env : Store} {names : List String}
    {x y z : Ident} {i j k : Nat} {dc : DomConstraint}
    (hxi : nameIndex names x.name = some i)
    (hyi : nameIndex names y.name = some j)
    (hzi : nameIndex names z.name = some k)
    (h : compileConstraint env names
        { name := Ident.mk "bool_and"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    dc = .boolAndSlot i j k := by
  have hex : extractConstraint names
      { name := Ident.mk "bool_and"
      , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
      , anns := [] } = some (.boolAndSlot i j k) := by
    simp only [extractConstraint, hxi, hyi, hzi]
  unfold compileConstraint at h
  rw [hex] at h
  exact (Except.ok.inj h).symm

/-- A three-identifier `bool_or` constraint whose names all resolve
    compiles to exactly the `boolOrSlot` over the resolved
    positions. -/
theorem compileConstraint_bool_or3 {env : Store} {names : List String}
    {x y z : Ident} {i j k : Nat} {dc : DomConstraint}
    (hxi : nameIndex names x.name = some i)
    (hyi : nameIndex names y.name = some j)
    (hzi : nameIndex names z.name = some k)
    (h : compileConstraint env names
        { name := Ident.mk "bool_or"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    dc = .boolOrSlot i j k := by
  have hex : extractConstraint names
      { name := Ident.mk "bool_or"
      , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
      , anns := [] } = some (.boolOrSlot i j k) := by
    simp only [extractConstraint, hxi, hyi, hzi]
  unfold compileConstraint at h
  rw [hex] at h
  exact (Except.ok.inj h).symm

/-- A slot-identifier/bool-literal `bool_not` constraint compiles
    (through the fallback) to exactly the negated `constEq`. -/
theorem compileConstraint_bool_not_lit {env : Store} {names : List String}
    {x : Ident} {b : Bool} {i : Nat} {dc : DomConstraint}
    (hxi : nameIndex names x.name = some i)
    (h : compileConstraint env names
        { name := Ident.mk "bool_not"
        , args := [.basic (.ident x), .basic (.lit (.bool b))]
        , anns := [] } = .ok dc) :
    dc = .constEq i (.bool (!b)) := by
  unfold compileConstraint at h
  have hex : extractConstraint names
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } = none := by
    simp only [extractConstraint]
  cases hext : extractConstraint names
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } with
  | some dc' =>
      rw [hex] at hext
      exact absurd hext (by simp)
  | none =>
      simp only [hext] at h
      rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at h
      rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at h
      rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at h
      rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at h
      rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at h
      rw [if_pos ⟨trivial, rfl⟩] at h
      have ha0 : argOf
          { name := Ident.mk "bool_not"
          , args := [.basic (.ident x), .basic (.lit (.bool b))]
          , anns := [] } 0 = .ok (.ident x) := rfl
      have ha1 : argOf
          { name := Ident.mk "bool_not"
          , args := [.basic (.ident x), .basic (.lit (.bool b))]
          , anns := [] } 1 = .ok (.lit (.bool b)) := rfl
      rw [ha0, ha1] at h
      -- evaluate the two argument compiles
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = .ok (ArgVal.slotRef i) := by
        rw [compileArgVal, hxi]
      have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
          = .ok (ArgVal.litVal (Value.bool b)) := by
        rw [compileArgVal]
      -- the do-block: bind-reduce then match-reduce
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = .ok (ArgVal.slotRef i) := by
        rw [compileArgVal, hxi]
      have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
          = .ok (ArgVal.litVal (Value.bool b)) := by
        rw [compileArgVal]
      have hred : (do
          let a0 ← (Except.ok (BasicExpr.ident x) : Except String BasicExpr)
          let a1 ← (Except.ok (BasicExpr.lit (BasicLiteral.bool b)) :
            Except String BasicExpr)
          match compileArgVal env names a0, compileArgVal env names a1 with
          | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
              Except.ok (DomConstraint.constEq i (Value.bool !b))
          | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
              Except.ok (DomConstraint.constEq j (Value.bool !b))
          | Except.error e, _ => Except.error e
          | _, Except.error e => Except.error e
          | _, _ =>
              Except.error "unsupported bool_not argument shapes" :
          Except String DomConstraint)
          = Except.ok (DomConstraint.constEq i (Value.bool !b)) := by
        show (match compileArgVal env names (BasicExpr.ident x),
            compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b)) with
          | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
              Except.ok (DomConstraint.constEq i (Value.bool !b))
          | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
              Except.ok (DomConstraint.constEq j (Value.bool !b))
          | Except.error e, _ => Except.error e
          | _, Except.error e => Except.error e
          | _, _ =>
              Except.error "unsupported bool_not argument shapes") = _
        rw [hc0, hc1]
      have h' : (do
          let a0 ← (Except.ok (BasicExpr.ident x) : Except String BasicExpr)
          let a1 ← (Except.ok (BasicExpr.lit (BasicLiteral.bool b)) :
            Except String BasicExpr)
          match compileArgVal env names a0, compileArgVal env names a1 with
          | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
              Except.ok (DomConstraint.constEq i (Value.bool !b))
          | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
              Except.ok (DomConstraint.constEq j (Value.bool !b))
          | Except.error e, _ => Except.error e
          | _, Except.error e => Except.error e
          | _, _ =>
              Except.error "unsupported bool_not argument shapes" :
          Except String DomConstraint) = .ok dc := h
      rw [hred] at h'
      exact (Except.ok.inj h').symm



end LeanFzn.Solver.Direct

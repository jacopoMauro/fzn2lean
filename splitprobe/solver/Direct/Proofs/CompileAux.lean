/-
File: solver/Direct/Proofs/Compile.lean

Purpose:
  The exact semantic-correspondence theorems for the certified
  FlatZinc fragment compiler (`solver/Direct/Compile.lean`).

Dependencies:
  - solver.Direct.Compile: the executable compiler.
DAG:
  solver.Direct.Compile -> solver.Direct.Proofs.Compile
     -> solver.Direct.Correctness
-/

import solver.Core
import solver.Direct.Compile
import solver.Direct.Proofs.CompileCore

namespace LeanFzn.Solver.Direct


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
                  rcases Nat.lt_succ_iff_lt_or_eq.mp
                    (Nat.lt_of_le_of_lt (Nat.le_succ i) hilt2) with hlt3 | hlt3
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
                    rw [List.getElem?_append_right
                      (Nat.le_succ_le.mpr (by
                        have hnn : auxs.length + 1 ≤ auxs.length + 1 := Nat.le_refl _
                        exact hnn))] at hip
                    rw [show auxs.length + 1 - auxs.length = 1 from by omega] at hip
                    simp only [List.getElem?_cons_succ, List.getElem?_singleton] at hip
                    -- the second slot's name IS the successor aux name
                    rw [auxName_succ]
                    exact (Option.some.inj hip).symm ▸ rfl
              have hnewsingle : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])],
                  ∃ w, p.2 = [w] := by
                intro p hp
                rcases List.mem_append.mp hp with hp' | hp'
                · exact hsingle p hp'
                · rcases List.mem_cons.mp hp' with hp' | hp'
                  · rw [List.mem_singleton] at hp'
                    obtain ⟨rfl⟩ := hp'
                    exact ⟨v, rfl⟩
                  · rw [List.mem_singleton] at hp'
                    obtain ⟨rfl⟩ := hp'
                    exact ⟨v2, rfl⟩
              rw [← h1]
              exact ih (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                hrec hnew hnewsingle
        · -- ONE aux slot
          rename_i v hpin
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
          rename_i v hpin
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
                      = [((auxName taken auxs.length).push '$', [v2])][auxs.length - auxs.length]? :=
                    List.getElem?_append_right (l₁ := auxs)
                      (l₂ := [((auxName taken auxs.length).push '$', [v2])]) (Nat.le_refl _)
                  rw [hstep]
                  rw [show auxs.length - auxs.length = 0 from by omega]
                  simp
                have haccget2 : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                    = some ((auxName taken auxs.length).push '$', [v2]) := by
                  have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                      = [((auxName taken auxs.length).push '$', [v2])][auxs.length + 1 - auxs.length]? :=
                    List.getElem?_append_right (l₁ := auxs)
                      (l₂ := [((auxName taken auxs.length).push '$', [v2])]) (by omega)
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
                  ⟨⟨List.mem_append.mpr (Or.inl hc'mem),
                    Or.inr ⟨v, hpin, hslotget1⟩⟩, ?_⟩⟩
                -- the second pin: the successor slot's name IS the
                -- successor aux name
                rw [auxName_succ]
                exact Or.inr ⟨v2, hpin2, hslotget2⟩
          · -- ONE aux slot
            rename_i v hpin
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
                  ⟨⟨List.mem_append.mpr (Or.inl hc'mem),
                    Or.inr ⟨v, hpin, hslotget⟩⟩, ?_⟩⟩
                -- pin2 = none (the one-slot shapes): vacuous
                rw [AuxShape.pin2] at *
                exact Or.inl rfl
          · -- no aux slot
            rename_i hpin
            cases hrec : expandPlan taken auxs rest with
            | mk auxs2 cs2 =>
                rw [hrec] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧
                    sh.expand (Ident.mk (auxName taken auxs.length)) ++ cs2 = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                refine ⟨auxs.length, fun c' hc'mem =>
                  ⟨⟨List.mem_append.mpr (Or.inl hc'mem), Or.inl hpin⟩, ?_⟩⟩
                rw [AuxShape.pin2] at *
                exact Or.inl rfl
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
              refine ⟨i, fun c' hc'mem => ⟨⟨?_, (hall c' hc'mem).2.1⟩,
                (hall c' hc'mem).2.2⟩⟩
              exact List.mem_cons_of_mem _ (hall c' hc'mem).1
        · rename_i sh2 hshape2
          split at h
          · -- TWO aux slots
            rename_i v v2 hpin hpin2
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
                refine ⟨i, fun c' hc'mem => ⟨⟨?_, (hall c' hc'mem).2.1⟩,
                  (hall c' hc'mem).2.2⟩⟩
                exact List.mem_append.mpr (Or.inr (hall c' hc'mem).1)
          · -- ONE aux slot
            rename_i v hpin
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
                refine ⟨i, fun c' hc'mem => ⟨⟨?_, (hall c' hc'mem).2.1⟩,
                  (hall c' hc'mem).2.2⟩⟩
                exact List.mem_append.mpr (Or.inr (hall c' hc'mem).1)
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
                refine ⟨i, fun c' hc'mem => ⟨⟨?_, (hall c' hc'mem).2.1⟩,
                  (hall c' hc'mem).2.2⟩⟩
                exact List.mem_append.mpr (Or.inr (hall c' hc'mem).1)


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
  | timesRK x y k => rw [AuxShape.pin2] at h; cases h
  | timesKR x y k => rw [AuxShape.pin2] at h; cases h
  | timesKR' x y k => rw [AuxShape.pin2] at h; cases h
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
  | neRK x k => rw [AuxShape.pin2] at h; cases h
  | neKR x k => rw [AuxShape.pin2] at h; cases h
  | andFalse x y => rw [AuxShape.pin2] at h; cases h
  | orTrue x y => rw [AuxShape.pin2] at h; cases h
  | andTrue x y => rw [AuxShape.pin2] at h; cases h
  | orFalse x y => rw [AuxShape.pin2] at h; cases h

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
              · rw [List.mem_singleton] at hlast
                obtain ⟨rfl⟩ := hlast
                have hvs : [v] = [v3] := hv3
                have hvv : v = v3 := by
                  injection hvs
                exact hvv ▸ hvpin
              · rw [List.mem_singleton] at hlast
                obtain ⟨rfl⟩ := hlast
                have hvs : [v2] = [v3] := hv3
                have hvv : v2 = v3 := by
                  injection hvs
                exact hvv ▸ hvpin2
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ _ = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
              exact ih _ auxs2 cs2 hrec hnew p (h1 ▸ hp) hv
        · -- ONE aux slot (the pin is int/bool by the shape)
          rename_i v hpin
          have hvpin : (∃ k, v = Value.int k) ∨ (∃ b, v = Value.bool b) :=
            auxShape_pin_valued sh v hpin
          have hnew : ∀ p ∈ auxs ++ [(auxName taken auxs.length, [v])],
              ∀ v2, p.2 = [v2] →
              (∃ k, v2 = Value.int k) ∨ (∃ b, v2 = Value.bool b) := by
            intro p hp2 v2 hv2
            rcases List.mem_append.mp hp2 with htl | hlast
            · exact hall p htl v2 hv2
            · rw [List.mem_singleton] at hlast
              obtain ⟨rfl⟩ := hlast
              have hvs : [v] = [v2] := hv2
              have hvv : v = v2 := by
                injection hvs
              exact hvv ▸ hvpin
          cases hrec : expandPlan taken
              (auxs ++ [(auxName taken auxs.length, [v])]) rest with
          | mk auxs2 cs2 =>
              rw [hrec] at h
              simp only at h
              obtain ⟨h1, _⟩ : auxs2 = auxs' ∧ _ = cs' :=
                Prod.mk.injEq _ _ _ _ ▸ h
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
                    = [((auxName taken auxs.length).push '$', [v2])][auxs.length - auxs.length]? :=
                  List.getElem?_append_right (l₁ := auxs)
                    (l₂ := [((auxName taken auxs.length).push '$', [v2])]) (Nat.le_refl _)
                rw [hstep]
                rw [show auxs.length - auxs.length = 0 from by omega]
                simp
              have haccget2 : (auxs ++ [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                  = some ((auxName taken auxs.length).push '$', [v2]) := by
                have hstep : (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])])[auxs.length + 1]?
                    = [((auxName taken auxs.length).push '$', [v2])][auxs.length + 1 - auxs.length]? :=
                  List.getElem?_append_right (l₁ := auxs)
                    (l₂ := [((auxName taken auxs.length).push '$', [v2])]) (by omega)
                rw [hstep]
                rw [show auxs.length + 1 - auxs.length = 1 from by omega]
                simp
              have hslot1 : auxs'[auxs.length]?
                  = some (auxName taken auxs.length, [v]) := by
                have hpres := hagree2 auxs.length (by rw [hlen]; omega)
                rw [haccget1] at hpres
                exact hpres
              have hslot2 : auxs'[auxs.length + 1]?
                  = some ((auxName taken auxs.length).push '$', [v2]) := by
                have hpres := hagree2 (auxs.length + 1) (by rw [hlen]; omega)
                rw [haccget2] at hpres
                exact hpres
              rcases List.mem_append.mp hc' with hpiece | htl
              · -- a piece of the head's shape: both slots positioned
                refine Or.inr ⟨c, List.mem_cons_self, sh, hshape2, auxs.length,
                  Nat.le_refl _, hpiece, ⟨Or.inr ⟨v, hpin, hslot1⟩, ?_⟩⟩
                rw [auxName_succ]
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
          rename_i v hpin
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
                · -- pin2 = none (the one-slot shapes): vacuous
                  rw [AuxShape.pin2]
                  exact Or.inl rfl
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
          rename_i hpin
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
                  Nat.le_refl _, hpiece, ⟨Or.inl hpin, by
                    rw [AuxShape.pin2]; exact Or.inl rfl⟩⟩
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


/-! ### The per-shape semantic bridges (SAT and coverage) -/

/-- The assembled store reads the aux slot at the extended position
    (the generic read bridge, position-indexed). -/
theorem toStore_read_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x : Ident} {i : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hx : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i) :
    (assemble m (slots0 ++ auxs) dcs).toStore a x = some a[i]! := by
  exact toStore_read (m := m) (slots := slots0 ++ auxs) (dcs := dcs)
    hnu hx halt

/-- The expansion keeps every passthrough constraint (not a pinning
    shape) in the expanded list. -/
theorem expandPlan_keep {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      ∀ c ∈ cs, auxShapeOf c = none → c ∈ cs' := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h c hc _
      cases hc
  | cons head rest ih =>
      intro auxs auxs' cs' h c hc hshape
      rw [expandPlan] at h
      split at h
      · -- the head passes through (hshapeNone : auxShapeOf head = none)
        rename_i hshapeNone
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ head :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            subst h1 h2
            rcases List.mem_cons.mp hc with rfl | htl
            · rw [hshape] at hshapeNone
              cases hshapeNone
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih auxs auxs2 cs2 hrec c htl hshape)
      · -- the head is a pinning shape: the member must be in the tail
        -- (the head is not a passthrough)
        rcases List.mem_cons.mp hc with hhead | htl
        · -- c = head, but the head is a pinning shape: contradiction
          exfalso
          rw [hhead] at hshape
          rename_i sh hshape2
          rw [hshape] at hshape2
          exact absurd hshape2 (by simp)
        · -- the tail's passthroughs survive inside the pieces' append
          -- The head is a pinning shape; split on its pins to find the
          -- accumulator the tail's recursion used.
          split at h
          · -- TWO aux slots
            rename_i v v2 hpin hpin2
            cases hrec2 : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                    hrec2 c htl hshape))
          · -- ONE aux slot
            rename_i v hpin
            cases hrec2 : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2
                    hrec2 c htl hshape))
          · -- no aux slot
            rename_i hpin
            cases hrec2 : expandPlan taken auxs rest with
            | mk auxs2 cs2 =>
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih auxs auxs2 cs2 hrec2 c htl hshape))


/-- The extended candidate space's domain at a model position is the
    model slot's own domain (the append's first half). -/
theorem getD_map_snd_append_first {slots0 auxs : List (String × List Value)}
    {i : Nat} (hilt : i < slots0.length) :
    ((slots0 ++ auxs).map Prod.snd).getD i [] = slots0[i].snd := by
  have hmap : (slots0 ++ auxs).map Prod.snd
      = slots0.map Prod.snd ++ auxs.map Prod.snd := List.map_append
  rw [hmap]
  have main : ∀ (l1 l2 : List (List Value)) (i : Nat),
      i < l1.length → (l1 ++ l2).getD i [] = l1.getD i [] := by
    intro l1
    induction l1 with
    | nil => intro _ i hilt; exact absurd hilt (by simp)
    | cons p rest ih =>
        intro l2 i hilt
        cases i with
        | zero => rfl
        | succ i2 =>
            show (p :: (rest ++ l2)).getD (i2 + 1) []
              = (p :: rest).getD (i2 + 1) []
            rw [List.getD_cons_succ, List.getD_cons_succ, ih l2 i2 (by simp at hilt; omega)]
  rw [main (slots0.map Prod.snd) (auxs.map Prod.snd) i
    (by rw [List.length_map]; omega)]
  rw [show (slots0.map Prod.snd).getD i [] = slots0[i].snd from
    getD_map_snd hilt]

/-- The model-slot positions of an extended slot list agree with the
    model slots (the prefix). -/
theorem extendedSlots_prefix {slots0 auxs : List (String × List Value)}
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (i : Nat) (hilt : i < slots0.length) :
    ∃ v, a[i]? = some v ∧ v ∈ slots0[i].snd := by
  have hlen : a.length = (slots0 ++ auxs).length := by
    have h1 := mem_allAssigns_length ((slots0 ++ auxs).map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  have hsome : a[i]? = some a[i]! := getElem_as_some (by
    rw [hlen, List.length_append]
    omega)
  have hfits := mem_allAssigns_fits ((slots0 ++ auxs).map Prod.snd) a hmem i
    a[i]! hsome
  rw [getD_map_snd_append_first hilt] at hfits
  exact ⟨a[i]!, hsome, hfits⟩

/-! ### The extended read chains (the aux-slot linker's premises) -/

/-- The int-reads premise over an EXTENDED candidate space: a
    slot-position read of an assignment in the extended space is an
    integer whenever the constraint's argument checks against the
    int-typed signature (the domain membership comes from the model
    prefix). -/
theorem int_read_of_checkArg_slot_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .int))))
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.int p := by
  -- the slot is in bounds
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots0.map Prod.fst) x.name i hxi
  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
  have hislt : i < slots0.length := by omega
  -- the check supplies the int base type for x
  obtain ⟨isVar, henv⟩ := staticEnv_int_of_checkArg hcheck
  -- the slot's variable, with its staticEnv resolution
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  -- the checked identifier IS the slot's name
  have hnameilt : i < (slots0.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots0.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots0[i]!.1 = x.name := by
    rw [show slots0[i]!.1 = (slots0.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots0[i]!.1 := by
      obtain ⟨sn⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  -- both resolutions describe the same staticEnv value: the type is int
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  -- combine the two staticEnv values: the variable's type is base int
  have htyint : ty.base = BaseType.int := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.int, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.int, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  -- the slot's domain is an intDom
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  obtain ⟨xs, hxs⟩ := varDomain_int_of_base hdom htyint
  -- the assignment's read is in the slot's values — all int (the
  -- EXTENDED candidate space's model-prefix membership)
  have hmemv : a[i]! ∈ slots0[i].snd := by
    obtain ⟨v, hsv, hvdom⟩ :=
      extendedSlots_prefix (slots0 := slots0) (auxs := auxs) hmem i hislt
    have hib : a[i]! = v := bang_of_getElem? hsv
    rw [hib]
    exact hvdom
  -- the slot pair is (n.name, dom.values)
  have hpairplain : slots0[i] = (n.name, dom.values) := by
    have hslotpair : slots0[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots0[i]! = slots0[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  rw [hxs] at hmemv
  obtain ⟨p, hp⟩ := intDom_values_int a[i]! hmemv
  exact ⟨p, hp⟩

/-- The bool-reads twin of `int_read_of_checkArg_slot_ext`. -/
theorem bool_read_of_checkArg_slot_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .bool))))
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.bool p := by
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots0.map Prod.fst) x.name i hxi
  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
  have hislt : i < slots0.length := by omega
  obtain ⟨isVar, henv⟩ := staticEnv_bool_of_checkArg hcheck
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  have hnameilt : i < (slots0.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots0.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots0[i]!.1 = x.name := by
    rw [show slots0[i]!.1 = (slots0.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots0[i]!.1 := by
      obtain ⟨sn⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  have htybool : ty.base = BaseType.bool := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.bool, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.bool, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  have hbooldom : dom = .boolDom := varDomain_bool_of_base hdom htybool
  have hmemv : a[i]! ∈ slots0[i].snd := by
    obtain ⟨v, hsv, hvdom⟩ :=
      extendedSlots_prefix (slots0 := slots0) (auxs := auxs) hmem i hislt
    have hib : a[i]! = v := bang_of_getElem? hsv
    rw [hib]
    exact hvdom
  have hpairplain : slots0[i] = (n.name, dom.values) := by
    have hslotpair : slots0[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots0[i]! = slots0[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  rw [hbooldom] at hmemv
  have hmemv' : a[i]! ∈ VarDomain.boolDom.values := hmemv
  obtain ⟨p, hp⟩ := boolDom_values_bool hmemv'
  exact ⟨p, hp⟩




/-- The timesRK shape's argument inversion: the classified
    constraint's arguments are the two identifiers and the int literal. -/
theorem auxShapeOf_timesRK_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesRK x y k)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))



/-- The timesKR shape's argument inversion. -/
theorem auxShapeOf_timesKR_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR x y k)) :
    c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident y)] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The timesKR' shape's argument inversion. -/
theorem auxShapeOf_timesKR'_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR' x y k)) :
    c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident y)] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The timesRKK shape's argument inversion. -/
theorem auxShapeOf_timesRKK_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesRKK x k k')) :
    c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.lit (.int k'))] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The timesKRR shape's argument inversion. -/
theorem auxShapeOf_timesKRR_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKRR x k k')) :
    c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.lit (.int k'))] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The timesKKR shape's argument inversion. -/
theorem auxShapeOf_timesKKR_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKKR x k k')) :
    c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')), .basic (.ident x)] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))


/-- The neRK shape's argument inversion. -/
theorem auxShapeOf_neRK_inv {c : ConstraintItem} {x : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.neRK x k)) :
    c.name.name = "int_ne" ∧ c.args = [.basic (.ident x), .basic (.lit (.int k))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: the two arms
    split at h
    · -- neRK arm
      next x2 k2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact ⟨heq1, heq2⟩
    · -- neKR arm
      next k2 x2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  -- bool_and / bool_or / other names: 3-arg arms clash with the
  -- 2-arg ne shapes
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The neKR shape's argument inversion. -/
theorem auxShapeOf_neKR_inv {c : ConstraintItem} {x : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.neKR x k)) :
    c.name.name = "int_ne" ∧ c.args = [.basic (.lit (.int k)), .basic (.ident x)] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: the two arms
    split at h
    · -- neRK arm: the clash
      next x2 k2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- neKR arm: the match
      next k2 x2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact ⟨heq1, heq2⟩
    · -- no pattern
      exact absurd h (by simp)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))



/-- The andTrue shape's argument inversion. -/
theorem auxShapeOf_andTrue_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andTrue x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: the two arms
    split at h
    · -- true arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- false arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  next heq1 =>
    -- bool_or: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The andFalse shape's argument inversion. -/
theorem auxShapeOf_andFalse_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andFalse x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: the two arms
    split at h
    · -- true arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- false arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- no pattern
      exact absurd h (by simp)
  next heq1 =>
    -- bool_or: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The orTrue shape's argument inversion. -/
theorem auxShapeOf_orTrue_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orTrue x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_or: the two arms
    split at h
    · -- true arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- false arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The orFalse shape's argument inversion. -/
theorem auxShapeOf_orFalse_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orFalse x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_or: the two arms
    split at h
    · -- true arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- false arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- no pattern
      exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)


/-- The timesRK shape's name inversion: the classification's int_times
    branch fired, so the constraint's name is `int_times`. -/
theorem auxShapeOf_timesRK_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesRK x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.int k))] := auxShapeOf_timesRK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKR shape's name inversion. -/
theorem auxShapeOf_timesKR_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.ident y)] := auxShapeOf_timesKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKR' shape's name inversion. -/
theorem auxShapeOf_timesKR'_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR' x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.ident y)] := auxShapeOf_timesKR'_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesRKK shape's name inversion. -/
theorem auxShapeOf_timesRKK_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesRKK x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.lit (.int k'))] := auxShapeOf_timesRKK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKRR shape's name inversion. -/
theorem auxShapeOf_timesKRR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKRR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.lit (.int k'))] := auxShapeOf_timesKRR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKKR shape's name inversion. -/
theorem auxShapeOf_timesKKR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKKR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')),
    .basic (.ident x)] := auxShapeOf_timesKKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The andTrue shape's name inversion. -/
theorem auxShapeOf_andTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andTrue x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_andTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The andFalse shape's name inversion. -/
theorem auxShapeOf_andFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andFalse x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_andFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The orTrue shape's name inversion. -/
theorem auxShapeOf_orTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orTrue x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_orTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)

/-- The orFalse shape's name inversion. -/
theorem auxShapeOf_orFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orFalse x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_orFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)


/-- The successful compile of a 3-identifier `int_times` piece gives
    the slot resolutions and the timesSlot form (the extraction arm's
    inversion: a failed resolution would have made the compile fail). -/
theorem compileConstraint_int_times3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "int_times"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    ∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .timesSlot i j k := by
  -- the extraction's result IS the compiled dc (the compile's first arm)
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm: the result IS the extraction's value
    rename_i dc' hext
    -- hext : extractConstraint ... = some dc'; hcc : .ok dc' = .ok dc
    have hcdc : dc' = dc := (Except.ok.inj hcc)
    -- the extraction's inversion: the int_times 3-identifier arm is
    -- the only one matching this piece's shape
    rcases extractConstraint_inv hext with
      -- int_eq 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_eq ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_eq literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_ne: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_le 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_le ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_le literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_plus: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- all_different: name mismatch
      ⟨-, -, hname, -, -, -⟩ |
      -- int_lin_eq: name mismatch
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_lin_le: name mismatch
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_times: THE arm
      ⟨x', y', z', i, j, k, hname, hargs, hi, hj, hk, h'⟩ |
      -- int_min: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_max: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_abs: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_lt 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_lt ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_lt literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- bool_not: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- bool_and: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- bool_or: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩
    all_goals
      first
        | (simp only [Ident.mk] at hname; exact absurd hname (by decide))
        | (
          -- the int_times arm: resolve the identifiers from the args
          injection hargs with hx' hrest
          injection hrest with hy' hz'
          injection hx' with hxb
          injection hy' with hyb
          injection hz' with hzb
          injection hxb with hx
          injection hyb with hy
          injection hzb with hzi
          injection hzi with hz
          subst hx
          subst hy
          subst hz
          exact ⟨i, j, k, hi, hj, hk, hcdc.symm.trans h'⟩)
  · -- the fallback arm: int_times is not among the fallback names
    -- (the gates all fail) — the compile errors, contradicting hcc
    exact absurd hcc (by intro hc; cases hc)

/-- An aux slot's name resolves at its extended position (fresh in the
    model prefix, positioned in the aux suffix). -/
theorem nameIndex_aux_slot {slots0 auxs : List (String × List Value)}
    {taken : List String} {i : Nat} {vs : List Value}
    (hsub : ∀ s ∈ slots0.map Prod.fst, s ∈ taken)
    (hspec : ∀ j p, auxs[j]? = some p → p.1 = auxName taken j)
    (hslot : auxs[i]? = some (auxName taken i, vs)) :
    nameIndex ((slots0 ++ auxs).map Prod.fst) (auxName taken i)
      = some (slots0.length + i) := by
  -- the name is a member of the extended list
  have hilt : i < auxs.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hpair : auxs[i] = (auxName taken i, vs) := by
    have h1 : auxs[i]? = some auxs[i] := List.getElem?_eq_getElem hilt
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  have hp : (auxName taken i, vs) ∈ auxs := by
    rw [← hpair]
    exact List.getElem_mem hilt
  have hmem : auxName taken i ∈ (slots0 ++ auxs).map Prod.fst := by
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem (f := Prod.fst) hp))
  obtain ⟨i3, hi3⟩ := nameIndex_of_mem hmem
  -- the position is IN the aux half (freshness rules out the model half)
  rw [List.map_append] at hi3
  rcases nameIndex_append_inv hi3 with hmodel | ⟨j, hjaux, hjeq⟩
  · exfalso
    have hnotmem : auxName taken i ∉ slots0.map Prod.fst := by
      intro hcon
      exact auxName_not_mem (hsub _ hcon)
    obtain ⟨hlt4, hget4⟩ := nameIndex_some _ _ i3 hmodel
    exact hnotmem (List.mem_of_getElem? (a := auxName taken i)
      (i := i3) (l := slots0.map Prod.fst) (by rw [hget4]))
  · -- the aux-half index j: the name at j is auxName taken j, which
    -- equals auxName taken i only when j = i
    obtain ⟨hjlt, hnamej⟩ := nameIndex_some _ _ j hjaux
    -- auxs[j] is positioned (its name is auxName taken j)
    have hjlt' : j < auxs.length := by
      rw [List.length_map] at hjlt
      exact hjlt
    have hpairj : (auxs.map Prod.fst)[j]? = some (auxName taken j) := by
      have hget : auxs[j]? = some auxs[j] := List.getElem?_eq_getElem hjlt'
      have hname : auxs[j].1 = auxName taken j := hspec j auxs[j] hget
      have hmap : (auxs.map Prod.fst)[j]? = some auxs[j].1 := by
        have h2 : (auxs.map Prod.fst)[j]? = Option.map Prod.fst auxs[j]? :=
          List.getElem?_map
        rw [h2, hget]
        rfl
      rw [hmap, hname]
    rw [hnamej] at hpairj
    -- the names agree, so their positions agree
    have hsame : auxName taken j = auxName taken i :=
      (Option.some.inj hpairj.symm)
    have hji : j = i := auxName_inj hsame
    subst hji
    -- the lengths and shapes line up
    rw [List.length_map] at hjeq
    rw [List.map_append, ← hjeq]
    exact hi3

/-- A successful `compileArgVal` of an identifier through a slot
    position: the name resolved at that position. -/
theorem cav_slotRef {env : Store} {names : List String} {x : Ident} {i : Nat}
    (h : compileArgVal env names (.ident x) = .ok (.slotRef i)) :
    nameIndex names x.name = some i := by
  simp only [compileArgVal] at h
  cases hn : nameIndex names x.name with
  | none =>
      rw [hn] at h
      cases hex : env x with
      | none => rw [hex] at h; cases h
      | some v => rw [hex] at h; cases h
  | some i2 =>
      rw [hn] at h
      have : ArgVal.slotRef i2 = ArgVal.slotRef i := (Except.ok.inj h)
      injection this
      subst i2
      rfl

/-- A successful `compileArgVal` of an identifier to a Boolean
    literal value: the name did NOT resolve as a slot, and the
    parameter environment supplied the Boolean. -/
theorem cav_litVal_bool {env : Store} {names : List String} {x : Ident}
    {b : Bool}
    (h : compileArgVal env names (.ident x) = .ok (.litVal (.bool b))) :
    nameIndex names x.name = none ∧ env x = some (.bool b) := by
  simp only [compileArgVal] at h
  cases hn : nameIndex names x.name with
  | none =>
      rw [hn] at h
      cases hex : env x with
      | none => rw [hex] at h; cases h
      | some v =>
          rw [hex] at h
          have : ArgVal.litVal v = ArgVal.litVal (Value.bool b) :=
            (Except.ok.inj h)
          have h2 : v = Value.bool b := by injection this
          exact ⟨rfl, by rw [← h2]⟩
  | some i2 => rw [hn] at h; cases h

/-- The successful compile of a 2-identifier `int_ne` piece gives the
    slot resolutions and the neSlot form. -/
theorem compileConstraint_int_ne2_inv {env : Store} {names : List String}
    {x y : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "int_ne"
        , args := [.basic (.ident x), .basic (.ident y)]
        , anns := [] } = .ok dc) :
    ∃ i j, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      dc = .neSlot i j := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hext
    have hcdc : dc' = dc := (Except.ok.inj hcc)
    rcases extractConstraint_inv hext with
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨x', y', i, j, hname, hargs, hxi, hyi, h'⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · -- the int_ne arm: the identifiers resolve from the args
      injection hargs with hx' hrest
      injection hrest with hy'
      injection hx' with hxb
      injection hy' with hyb
      injection hxb with hx
      injection hyb with hy
      subst hx
      subst hy
      refine ⟨i, j, ?_, ?_, ?_⟩
      · rw [← hxi]
      · rw [← hyi]
      · exact hcdc.symm.trans h'
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
  · -- the fallback arm: `int_ne` is not among the fallback gate
    -- names (int_plus/int_le/int_lt/int_gt/int_ge/bool_not/bool_and/
    -- bool_or), so every gate's name test fails by `decide` and the
    -- compile reduces to the unsupported-predicate error —
    -- contradicting hcc
    exact absurd hcc (by intro hc; cases hc)

/-- The successful compile of a 3-identifier `bool_and` piece: either
    the extraction arm (all three names resolve, `boolAndSlot`), or
    the fallback arm — `bool_and`'s gate fires and a parameter-resolved
    operand compiles to `eqSlot`/`constEq` (the parameter case: the
    name does NOT resolve as a slot, and `env` supplies the Boolean).
    The honest five-way disjunction of the possible compiled forms. -/
theorem compileConstraint_bool_and3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_and"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    (∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .boolAndSlot i j k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool true) ∧ dc = .eqSlot i k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool false) ∧ dc = .constEq k (.bool false)) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool true) ∧ dc = .eqSlot j k) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool false) ∧ dc = .constEq k (.bool false)) := by
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm
    rename_i dc' hres
    cases hx : nameIndex names x.name with
    | some i =>
      cases hy : nameIndex names y.name with
      | some j =>
        cases hz : nameIndex names z.name with
        | some k =>
          refine Or.inl ⟨i, j, k, rfl, rfl, rfl, ?_⟩
          have hred : extractConstraint names
              { name := Ident.mk "bool_and"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = some (.boolAndSlot i j k) := by
            simp only [extractConstraint, hx, hy, hz]
          rw [hred] at hres
          have hcdc : dc' = .boolAndSlot i j k :=
            (Option.some.inj hres).symm
          rw [hcdc] at hcc
          exact (Except.ok.inj hcc).symm
        | none =>
          exfalso
          have hred : extractConstraint names
              { name := Ident.mk "bool_and"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = none := by
            simp only [extractConstraint, hx, hy, hz]
          exact absurd (hred.symm.trans hres) (by simp)
      | none =>
        exfalso
        have hred : extractConstraint names
            { name := Ident.mk "bool_and"
            , args := [.basic (.ident x), .basic (.ident y),
              .basic (.ident z)]
            , anns := [] } = none := by
          simp only [extractConstraint, hx, hy]
        exact absurd (hred.symm.trans hres) (by simp)
    | none =>
      exfalso
      have hred : extractConstraint names
          { name := Ident.mk "bool_and"
          , args := [.basic (.ident x), .basic (.ident y),
            .basic (.ident z)]
          , anns := [] } = none := by
        simp only [extractConstraint, hx]
      exact absurd (hred.symm.trans hres) (by simp)
  · -- the fallback arm: `bool_and`'s gate fires (the name and the
    -- three-element args are concrete); the do-block runs over the
    -- three identifiers' compileArgVals
    rw [if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_plus")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_le")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_lt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_gt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_ge")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "bool_not")
        (by decide)),
      if_pos ⟨rfl, rfl⟩] at hcc
    -- the do-block over the three identifier argOfs (rfl-reduced: the
    -- bang reads of the concrete three-element list are the
    -- identifiers themselves)
    have hcc2 : ((do
        let _a0 ← (Except.ok (.ident x) : Except String BasicExpr)
        let _a1 ← (Except.ok (.ident y) : Except String BasicExpr)
        let _a2 ← (Except.ok (.ident z) : Except String BasicExpr)
        match compileArgVal env names (.ident x),
            compileArgVal env names (.ident y),
            compileArgVal env names (.ident z) with
        | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ =>
            .error "unsupported bool_and argument shapes" :
        Except String DomConstraint)) = .ok dc := hcc
    split at hcc2
    · next i k hc0 hc1 hc2 =>
        exact Or.inr (Or.inl ⟨i, k, cav_slotRef hc0, cav_slotRef hc2,
          (cav_litVal_bool hc1).1, (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inl ⟨_, k, cav_slotRef hc0,
          cav_slotRef hc2, (cav_litVal_bool hc1).1,
          (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩))
    · next j k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    all_goals exact absurd hcc2 (by intro hc; injection hc)
/-- The successful compile of a 3-identifier `bool_or` piece: the
    honest five-way disjunction of the possible compiled forms (the
    extraction arm's `boolOrSlot` when all three names resolve, or
    `bool_or`'s fallback arm — a parameter-resolved operand compiles
    to `constEq k true`/`eqSlot i k` over the resolved positions). -/
theorem compileConstraint_bool_or3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_or"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    (∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .boolOrSlot i j k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool true) ∧ dc = .constEq k (.bool true)) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool false) ∧ dc = .eqSlot i k) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool true) ∧ dc = .constEq k (.bool true)) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool false) ∧ dc = .eqSlot j k) := by
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm
    rename_i dc' hres
    cases hx : nameIndex names x.name with
    | some i =>
      cases hy : nameIndex names y.name with
      | some j =>
        cases hz : nameIndex names z.name with
        | some k =>
          refine Or.inl ⟨i, j, k, rfl, rfl, rfl, ?_⟩
          have hred : extractConstraint names
              { name := Ident.mk "bool_or"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = some (.boolOrSlot i j k) := by
            simp only [extractConstraint, hx, hy, hz]
          rw [hred] at hres
          have hcdc : dc' = .boolOrSlot i j k :=
            (Option.some.inj hres).symm
          rw [hcdc] at hcc
          exact (Except.ok.inj hcc).symm
        | none =>
          exfalso
          have hred : extractConstraint names
              { name := Ident.mk "bool_or"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = none := by
            simp only [extractConstraint, hx, hy, hz]
          exact absurd (hred.symm.trans hres) (by simp)
      | none =>
        exfalso
        have hred : extractConstraint names
            { name := Ident.mk "bool_or"
            , args := [.basic (.ident x), .basic (.ident y),
              .basic (.ident z)]
            , anns := [] } = none := by
          simp only [extractConstraint, hx, hy]
        exact absurd (hred.symm.trans hres) (by simp)
    | none =>
      exfalso
      have hred : extractConstraint names
          { name := Ident.mk "bool_or"
          , args := [.basic (.ident x), .basic (.ident y),
            .basic (.ident z)]
          , anns := [] } = none := by
        simp only [extractConstraint, hx]
      exact absurd (hred.symm.trans hres) (by simp)
  · -- the fallback arm: `bool_or`'s gate fires; the do-block runs
    -- over the three identifiers' compileArgVals
    rw [if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_plus")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_le")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_lt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_gt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_ge")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "bool_not")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "bool_and")
        (by decide)),
      if_pos ⟨rfl, rfl⟩] at hcc
    -- the do-block over the three identifier argOfs (rfl-reduced)
    have hcc2 : ((do
        let _a0 ← (Except.ok (.ident x) : Except String BasicExpr)
        let _a1 ← (Except.ok (.ident y) : Except String BasicExpr)
        let _a2 ← (Except.ok (.ident z) : Except String BasicExpr)
        match compileArgVal env names (.ident x),
            compileArgVal env names (.ident y),
            compileArgVal env names (.ident z) with
        | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ =>
            .error "unsupported bool_or argument shapes" :
        Except String DomConstraint)) = .ok dc := hcc
    split at hcc2
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inl ⟨_, k, cav_slotRef hc0, cav_slotRef hc2,
          (cav_litVal_bool hc1).1, (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)
    · next i k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inl ⟨i, k, cav_slotRef hc0,
          cav_slotRef hc2, (cav_litVal_bool hc1).1,
          (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩))
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    · next j k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    all_goals exact absurd hcc2 (by intro hc; injection hc)
/-- The successful compile of a slot-identifier/bool-literal
    `bool_not` piece (through the fallback) gives the slot's
    resolution and the negated constEq form. -/
theorem compileConstraint_bool_not_lit_inv {env : Store} {names : List String}
    {x : Ident} {b : Bool} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_not"
        , args := [.basic (.ident x), .basic (.lit (.bool b))]
        , anns := [] } = .ok dc) :
    ∃ i, nameIndex names x.name = some i ∧
      dc = .constEq i (.bool (!b)) := by
  -- the extraction rejects this shape (bool_not with a literal)
  have hex : extractConstraint names
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } = none := by
    simp only [extractConstraint]
  -- the compile reduces to the fallback; the name gates select
  -- bool_not
  unfold compileConstraint at hcc
  rw [hex] at hcc
  simp only [hex] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_pos ⟨trivial, rfl⟩] at hcc
  -- the do-block reduces (argOf on the literal args)
  have ha0 : argOf
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } 0 = .ok (.ident x) := rfl
  have ha1 : argOf
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } 1 = .ok (.lit (.bool b)) := rfl
  rw [ha0, ha1] at hcc
  -- case on x's resolution: a slot (the success) or an env value/error
  cases hx : nameIndex names x.name with
  | some i =>
      -- the slot arm: the first match arm fires
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = .ok (ArgVal.slotRef i) := by
        rw [compileArgVal, hx]
      have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
          = .ok (ArgVal.litVal (Value.bool b)) := by
        rw [compileArgVal]
      -- the do-binds reduce definitionally; restate hcc in the
      -- reduced match form
      have hcc' : (match compileArgVal env names (BasicExpr.ident x),
          compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b)) with
        | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
            Except.ok (DomConstraint.constEq i (Value.bool !b))
        | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
            Except.ok (DomConstraint.constEq j (Value.bool !b))
        | Except.error e, _ => Except.error e
        | _, Except.error e => Except.error e
        | _, _ =>
            Except.error "unsupported bool_not argument shapes") = .ok dc := hcc
      rw [hc0, hc1] at hcc'
      refine ⟨i, ?_, ?_⟩
      · rw [← hx]
      · exact (Except.ok.inj hcc').symm
  | none =>
      -- x is not a slot: it resolves through env or errors; either
      -- way the match's first arm (slotRef, litVal) cannot fire with
      -- a slotRef for a0 — the compile either errors (contradiction)
      -- or produces a constEq over a LITERAL-resolved position,
      -- which is impossible (the arm requires a slotRef)
      exfalso
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = match env x with
          | some v => .ok (ArgVal.litVal v)
          | none => .error s!"unresolved argument '{x.name}'" := by
        rw [compileArgVal, hx]
        rfl
      -- restate hcc in the reduced match form and rewrite
      have hcc' : (match compileArgVal env names (BasicExpr.ident x),
          compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b)) with
        | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
            Except.ok (DomConstraint.constEq i (Value.bool !b))
        | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
            Except.ok (DomConstraint.constEq j (Value.bool !b))
        | Except.error e, _ => Except.error e
        | _, Except.error e => Except.error e
        | _, _ =>
            Except.error "unsupported bool_not argument shapes") = .ok dc := hcc
      rw [hc0] at hcc'
      -- case on env x: a value (litVal arm mismatch) or an error
      cases henv : env x with
      | some v =>
          -- the first argument compiles to a litVal; the match arms
          -- require a slotRef — the error arm
          have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
              = .ok (ArgVal.litVal (Value.bool b)) := by
            rw [compileArgVal]
          rw [hc1] at hcc'
          simp only [henv] at hcc'
          cases hcc'
      | none =>
          simp only [henv] at hcc'
          cases hcc'

end LeanFzn.Solver.Direct

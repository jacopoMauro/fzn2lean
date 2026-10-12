import LeanFzn.Parser.Grammar
open LeanFzn.Parser


/-
# Grammar Suffix Bounds and Consumption Bounds

Auxiliary results about the grammar relations of `FznGrammar.lean` used by the
completeness proof in `FznCompleteness.lean`:

* **Suffix bounds**: every derivation `Gr* toks ast rest` leaves a suffix
  `rest` of `toks`.  These bound the recursion depth of a derivation by the
  token count, which is the basis of fuel adequacy.
* **Consumption bounds**: every non-trivial derivation consumes at least one
  token, so recursive descents into sub-derivations strictly shorten the
  remaining token list.

`GrSepListTail`, `GrAnnotations` (members of mutual inductive blocks) and
`GrAnnExpr` (recursive through `GrSepList GrAnnExpr`) cannot be handled by
the `induction` tactic of Lean 4.33 on mutual types.  Since each of them
recurses only on itself, their proofs use strong induction on a
natural-number bound on the token-list length.
-/

namespace LeanFzn.Parser

open LeanFzn

open LeanFzn.Parser.Lexer

/-! ## Generic separated-list lemmas -/

/-- A separated-list-tail derivation leaves a suffix of the input.  The tail
    relation is self-recursive (within a mutual block), so the proof is a
    strong induction on a bound of the token-list length. -/
theorem GrSepListTail.suffix {elem : List Token → α → List Token → Prop}
    (helem : ∀ {t x r}, elem t x r → ∃ pre, t = pre ++ r)
    {toks xs rest} (h : GrSepListTail elem toks xs rest) :
    ∃ pre, toks = pre ++ rest := by
  have key : ∀ (m : Nat) (toks : List Token) (xs : List α) (rest : List Token),
      toks.length ≤ m → GrSepListTail elem toks xs rest →
      ∃ pre, toks = pre ++ rest := by
    intro m
    induction m with
    | zero =>
      intro toks xs rest hlen h
      cases h with
      | nil => exact ⟨[], rfl⟩
      | cons h₁ h₂ => simp only [List.length_cons] at hlen; omega
    | succ m ih =>
      intro toks xs rest hlen h
      cases h with
      | nil => exact ⟨[], rfl⟩
      | @cons ts₁ x ts₂ xs rest h₁ h₂ =>
        obtain ⟨pre₁, rfl⟩ := helem h₁
        have hlen₂ : ts₂.length ≤ m := by
          have h1 : (.comma :: (pre₁ ++ ts₂)).length ≤ m + 1 := hlen
          simp only [List.length_cons, List.length_append] at h1
          omega
        obtain ⟨pre₂, rfl⟩ := ih ts₂ xs rest hlen₂ h₂
        exact ⟨.comma :: pre₁ ++ pre₂, by simp⟩
  exact key toks.length toks xs rest (Nat.le_refl _) h

/-- A separated-list derivation leaves a suffix of the input. -/
theorem GrSepList.suffix {elem : List Token → α → List Token → Prop}
    (helem : ∀ {t x r}, elem t x r → ∃ pre, t = pre ++ r)
    {toks xs rest} (h : GrSepList elem toks xs rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | nil => exact ⟨[], rfl⟩
  | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
    obtain ⟨pre₂, rfl⟩ := h₂.suffix helem
    obtain ⟨pre₁, rfl⟩ := helem h₁
    exact ⟨pre₁ ++ pre₂, by simp⟩

/-- Bounded separated-list-tail suffix: like `GrSepListTail.suffix`, but the
    element property is only available for token lists up to length `m`.
    Used for the recursive `GrAnnExpr`, whose suffix property is proved by
    induction on the same bound. -/
theorem GrSepListTail.suffix_bounded {elem : List Token → α → List Token → Prop}
    {m : Nat} (helem : ∀ {t x r}, elem t x r → t.length ≤ m → ∃ pre, t = pre ++ r)
    {toks xs rest} (hbound : toks.length ≤ m)
    (h : GrSepListTail elem toks xs rest) :
    ∃ pre, toks = pre ++ rest := by
  have key : ∀ (n : Nat), n ≤ m → ∀ (toks : List Token) (xs : List α)
      (rest : List Token), toks.length ≤ n → GrSepListTail elem toks xs rest →
      ∃ pre, toks = pre ++ rest := by
    intro n
    induction n with
    | zero =>
      intro _ toks xs rest hn ht
      cases ht with
      | nil => exact ⟨[], rfl⟩
      | cons h₁ h₂ => simp only [List.length_cons] at hn; omega
    | succ n ihn =>
      intro hnm toks xs rest hn ht
      cases ht with
      | nil => exact ⟨[], rfl⟩
      | @cons ts₁ x ts₂ xs rest h₁ h₂ =>
        have hts₁ : ts₁.length ≤ n := by
          simp only [List.length_cons] at hn; omega
        have hts₁m : ts₁.length ≤ m := by omega
        obtain ⟨pre₁, rfl⟩ := helem h₁ hts₁m
        have hts₂ : ts₂.length ≤ n := by
          simp only [List.length_append] at hts₁; omega
        obtain ⟨pre₂, rfl⟩ := ihn (by omega) ts₂ xs rest hts₂ h₂
        exact ⟨.comma :: pre₁ ++ pre₂, by simp⟩
  exact key toks.length hbound toks xs rest (Nat.le_refl _) h

/-- Bounded separated-list suffix: the element property is only available
    for token lists up to length `m`. -/
theorem GrSepList.suffix_bounded {elem : List Token → α → List Token → Prop}
    {m : Nat} (helem : ∀ {t x r}, elem t x r → t.length ≤ m → ∃ pre, t = pre ++ r)
    {toks xs rest} (hbound : toks.length ≤ m)
    (h : GrSepList elem toks xs rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | nil => exact ⟨[], rfl⟩
  | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
    obtain ⟨pre₁, rfl⟩ := helem h₁ hbound
    have hts₂ : ts₂.length ≤ m := by
      simp only [List.length_append] at hbound
      omega
    obtain ⟨pre₂, rfl⟩ := h₂.suffix_bounded helem hts₂
    exact ⟨pre₁ ++ pre₂, by simp⟩


/-! ## Generic item-list lemmas -/

section ItemList
variable {item : List Token → α → List Token → Prop}

/-- An item-list derivation leaves a suffix of the input, given that each
    item does.  `GrItemList` is a standalone inductive, so plain structural
    induction applies. -/
theorem GrItemList.suffix (hsuf : ∀ {t x r}, item t x r → ∃ pre, t = pre ++ r)
    {toks xs rest} (h : GrItemList item toks xs rest) : ∃ pre, toks = pre ++ rest := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons h₁ h₂ ih =>
    obtain ⟨pre₂, rfl⟩ := ih
    obtain ⟨pre₁, rfl⟩ := hsuf h₁
    exact ⟨pre₁ ++ pre₂, by simp⟩

end ItemList

/-! ## Suffix and consumption bounds for the concrete relations -/

section SuffixBounds

variable {toks rest : List Token}

theorem GrIntAtom.suffix {i : Int} (h : GrIntAtom toks i rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h
  exact ⟨[.intLit _], rfl⟩

theorem GrBasicLiteral.suffix {l : BasicLiteral} (h : GrBasicLiteral toks l rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @bool b r => exact ⟨[.boolLit b], rfl⟩
  | @int i r => exact ⟨[.intLit i], rfl⟩
  | @intRange lo hi r => exact ⟨[.intLit lo, .dotDot, .intLit hi], rfl⟩
  | @intSet ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    exact ⟨.lBrace :: pre ++ [.rBrace], by simp⟩

theorem GrBasicLiteral.consumes_pos {l : BasicLiteral} (h : GrBasicLiteral toks l rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @bool b r => simp only [List.length_cons]; omega
  | @int i r => simp only [List.length_cons]; omega
  | @intRange lo hi r => simp only [List.length_cons]; omega
  | @intSet ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrBasicExpr.suffix {e : BasicExpr} (h : GrBasicExpr toks e rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @lit l ts r hl => exact hl.suffix
  | @ident x r => exact ⟨[.ident x], rfl⟩

theorem GrBasicExpr.consumes_pos {e : BasicExpr} (h : GrBasicExpr toks e rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @lit l ts r hl => exact hl.consumes_pos
  | @ident x r => simp only [List.length_cons]; omega

theorem GrExpr.suffix {e : Expr} (h : GrExpr toks e rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @basic b ts r hb => exact hb.suffix
  | @array ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrBasicExpr.suffix
    exact ⟨.lBrack :: pre ++ [.rBrack], by simp⟩

theorem GrParArrayLiteral.suffix {v : ParArrayLiteral}
    (h : GrParArrayLiteral toks v rest) : ∃ pre, toks = pre ++ rest := by
  cases h with
  | @mk ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrBasicLiteral.suffix
    exact ⟨.lBrack :: pre ++ [.rBrack], by simp⟩

/-- An annotation-expression derivation leaves a suffix of the input.
    `GrAnnExpr` is recursive through `GrSepList GrAnnExpr` (annotation calls
    and annotation arrays), so the proof is a strong induction on a bound of
    the token-list length, using the bounded separated-list lemmas with the
    induction hypothesis as the element property. -/
theorem GrAnnExpr.suffix {a : AnnExpr} (h : GrAnnExpr toks a rest) :
    ∃ pre, toks = pre ++ rest := by
  have key : ∀ (m : Nat) (toks : List Token) (a : AnnExpr) (rest : List Token),
      toks.length ≤ m → GrAnnExpr toks a rest → ∃ pre, toks = pre ++ rest := by
    intro m
    induction m with
    | zero =>
      intro toks a rest hlen h
      cases h with
      | @lit l ts r hl => have := hl.consumes_pos; omega
      | @ident x r => simp only [List.length_cons] at hlen; omega
      | @string s r => simp only [List.length_cons] at hlen; omega
      | @annCall x args ts r hid hne hl => simp only [List.length_cons] at hlen; omega
      | @array ts es r hl => simp only [List.length_cons] at hlen; omega
    | succ m ih =>
      intro toks a rest hlen h
      cases h with
      | @lit l ts r hl => exact hl.suffix
      | @ident x r => exact ⟨[.ident x], rfl⟩
      | @string s r => exact ⟨[.stringLit s], rfl⟩
      | @annCall x args ts r hid hne hl =>
        have helem : ∀ {t : List Token} {x : AnnExpr} {r : List Token},
            GrAnnExpr t x r → t.length ≤ m → ∃ pre, t = pre ++ r :=
          fun hd hlen' => ih _ _ _ hlen' hd
        have hts : ts.length ≤ m := by
          have h1 : (.ident x :: .lParen :: ts).length ≤ m + 1 := hlen
          simp only [List.length_cons] at h1
          omega
        obtain ⟨pre, rfl⟩ := hl.suffix_bounded helem hts
        exact ⟨.ident x :: .lParen :: pre ++ [.rParen], by simp⟩
      | @array ts es r hl =>
        have helem : ∀ {t : List Token} {x : AnnExpr} {r : List Token},
            GrAnnExpr t x r → t.length ≤ m → ∃ pre, t = pre ++ r :=
          fun hd hlen' => ih _ _ _ hlen' hd
        have hts : ts.length ≤ m := by
          have h1 : (.lBrack :: ts).length ≤ m + 1 := hlen
          simp only [List.length_cons] at h1
          omega
        obtain ⟨pre, rfl⟩ := hl.suffix_bounded helem hts
        exact ⟨.lBrack :: pre ++ [.rBrack], by simp⟩
  exact key toks.length toks a rest (Nat.le_refl _) h


theorem GrExpr.consumes_pos {e : Expr} (h : GrExpr toks e rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @basic b ts r hb => exact hb.consumes_pos
  | @array ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrBasicExpr.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrAnnExpr.consumes_pos {a : AnnExpr} (h : GrAnnExpr toks a rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @lit l ts r hl => exact hl.consumes_pos
  | @ident x r => simp only [List.length_cons]; omega
  | @string s r => simp only [List.length_cons]; omega
  | @annCall x args ts r hid hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrAnnExpr.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @array ts es r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrAnnExpr.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrAnnotation.suffix {a : Annotation} (h : GrAnnotation toks a rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @ident x r hid => exact ⟨[.ident x], rfl⟩
  | @call x args ts r hid hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrAnnExpr.suffix
    exact ⟨.ident x :: .lParen :: pre ++ [.rParen], by simp⟩

theorem GrAnnotation.consumes_pos {a : Annotation} (h : GrAnnotation toks a rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @ident x r hid => simp only [List.length_cons]; omega
  | @call x args ts r hid hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrAnnExpr.suffix
    simp only [List.length_cons, List.length_append]
    omega

/-- An annotations derivation leaves a suffix of the input.  `GrAnnotations`
    is a member of the large mutual block, so the proof is a strong induction
    on a bound of the token-list length. -/
theorem GrAnnotations.suffix {as : List Annotation} (h : GrAnnotations toks as rest) :
    ∃ pre, toks = pre ++ rest := by
  have key : ∀ (m : Nat) (toks : List Token) (as : List Annotation) (rest : List Token),
      toks.length ≤ m → GrAnnotations toks as rest → ∃ pre, toks = pre ++ rest := by
    intro m
    induction m with
    | zero =>
      intro toks as rest hlen h
      cases h with
      | nil => exact ⟨[], rfl⟩
      | @cons ts₁ a ts₂ as ts₃ h₁ h₂ => simp only [List.length_cons] at hlen; omega
    | succ m ih =>
      intro toks as rest hlen h
      cases h with
      | nil => exact ⟨[], rfl⟩
      | @cons ts₁ a ts₂ as ts₃ h₁ h₂ =>
        have hbound : ts₂.length ≤ m := by
          have h1 : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
          have hl : (.colonColon :: ts₁).length ≤ m + 1 := hlen
          simp only [List.length_cons] at hl
          omega
        obtain ⟨pre₂, rfl⟩ := ih _ _ _ hbound h₂
        obtain ⟨pre₁, rfl⟩ := h₁.suffix
        exact ⟨.colonColon :: pre₁ ++ pre₂, by simp⟩
  exact key toks.length toks as rest (Nat.le_refl _) h

theorem GrBasicParType.suffix {t : BasicParType} (h : GrBasicParType toks t rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | bool => exact ⟨[.kwBool], rfl⟩
  | int => exact ⟨[.kwInt], rfl⟩
  | setOfInt => exact ⟨[.kwSet, .kwOf, .kwInt], rfl⟩

theorem GrBasicVarType.suffix {t : BasicVarType} (h : GrBasicVarType toks t rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @parBool r => exact ⟨[.kwVar, .kwBool], rfl⟩
  | @parInt r => exact ⟨[.kwVar, .kwInt], rfl⟩
  | @parSetOfInt r => exact ⟨[.kwVar, .kwSet, .kwOf, .kwInt], rfl⟩
  | @intRange lo hi r => exact ⟨[.kwVar, .intLit lo, .dotDot, .intLit hi], rfl⟩
  | @intSet es ts r hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    exact ⟨.kwVar :: .lBrace :: pre ++ [.rBrace], by simp⟩
  | @setOfIntRange lo hi r =>
    exact ⟨[.kwVar, .kwSet, .kwOf, .intLit lo, .dotDot, .intLit hi], rfl⟩
  | @setOfIntSet es ts r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    exact ⟨.kwVar :: .kwSet :: .kwOf :: .lBrace :: pre ++ [.rBrace], by simp⟩

theorem GrBasicVarType.consumes_pos {t : BasicVarType} (h : GrBasicVarType toks t rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @parBool r => simp only [List.length_cons]; omega
  | @parInt r => simp only [List.length_cons]; omega
  | @parSetOfInt r => simp only [List.length_cons]; omega
  | @intRange lo hi r => simp only [List.length_cons]; omega
  | @intSet es ts r hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @setOfIntRange lo hi r => simp only [List.length_cons]; omega
  | @setOfIntSet es ts r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrIndexSet.suffix {i : IndexSet} (h : GrIndexSet toks i rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @mk hi r => exact ⟨[.intLit 1, .dotDot, .intLit hi], rfl⟩

theorem GrBasicPredParamType.suffix {t : BasicPredParamType}
    (h : GrBasicPredParamType toks t rest) : ∃ pre, toks = pre ++ rest := by
  cases h with
  | @par ts p r hp => exact hp.suffix
  | @var ts v r hv => exact hv.suffix
  | @intRange lo hi r => exact ⟨[.intLit lo, .dotDot, .intLit hi], rfl⟩
  | @intSet es ts r hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    exact ⟨.lBrace :: pre ++ [.rBrace], by simp⟩
  | @setOfIntRange lo hi r => exact ⟨[.kwSet, .kwOf, .intLit lo, .dotDot, .intLit hi], rfl⟩
  | @setOfIntSet es ts r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    exact ⟨.kwSet :: .kwOf :: .lBrace :: pre ++ [.rBrace], by simp⟩

theorem GrBasicPredParamType.consumes_pos {t : BasicPredParamType}
    (h : GrBasicPredParamType toks t rest) : 1 ≤ toks.length - rest.length := by
  cases h with
  | @par ts p r hp => cases hp <;> simp only [List.length_cons] <;> omega
  | @var ts v r hv => exact hv.consumes_pos
  | @intRange lo hi r => simp only [List.length_cons]; omega
  | @intSet es ts r hne hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @setOfIntRange lo hi r => simp only [List.length_cons]; omega
  | @setOfIntSet es ts r hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrIntAtom.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrPredIndexSet.suffix {i : PredIndexSet} (h : GrPredIndexSet toks i rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | int => exact ⟨[.kwInt], rfl⟩
  | @range ts i r hi => exact hi.suffix

theorem GrPredParamType.suffix {t : PredParamType} (h : GrPredParamType toks t rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @basic ts b r hb => exact hb.suffix
  | @array ts₁ i ts₂ el r hi hb =>
    obtain ⟨pre₂, rfl⟩ := hb.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    exact ⟨.kwArray :: .lBrack :: pre₁ ++ .rBrack :: .kwOf :: pre₂, by simp⟩

theorem GrPredParamType.consumes_pos {t : PredParamType} (h : GrPredParamType toks t rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @basic ts b r hb => exact hb.consumes_pos
  | @array ts₁ i ts₂ el r hi hb =>
    obtain ⟨pre₂, rfl⟩ := hb.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrPredParam.suffix {p : PredParam} (h : GrPredParam toks p rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @mk x t ts r hid ht =>
    obtain ⟨pre, rfl⟩ := ht.suffix
    exact ⟨pre ++ [.colon, .ident x], by simp⟩

theorem GrPredParam.consumes_pos {p : PredParam} (h : GrPredParam toks p rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @mk x t ts r hid ht =>
    have h1 := ht.consumes_pos
    obtain ⟨pre, rfl⟩ := ht.suffix
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega

theorem GrPredicateItem.suffix {p : PredicateItem} (h : GrPredicateItem toks p rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @mk x ts ps r hid hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrPredParam.suffix
    exact ⟨.kwPredicate :: .ident x :: .lParen :: pre ++ [.rParen, .semi], by simp⟩

theorem GrPredicateItem.consumes_pos {p : PredicateItem} (h : GrPredicateItem toks p rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @mk x ts ps r hid hl =>
    obtain ⟨pre, rfl⟩ := hl.suffix GrPredParam.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrParDeclItem.suffix {d : ParDeclItem} (h : GrParDeclItem toks d rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @basic ts₁ t x ts₂ v r ht hv =>
    obtain ⟨pre₂, rfl⟩ := hv.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    exact ⟨pre₁ ++ .colon :: .ident x :: .eq :: pre₂ ++ [.semi], by simp⟩
  | @array ts₁ i ts₂ t x ts₃ v r hi ht hv =>
    obtain ⟨pre₃, rfl⟩ := hv.suffix
    obtain ⟨pre₂, rfl⟩ := ht.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    exact ⟨.kwArray :: .lBrack :: pre₁ ++ .rBrack :: .kwOf :: pre₂ ++ .colon :: .ident x :: .eq
      :: pre₃ ++ [.semi], by simp⟩

theorem GrParDeclItem.consumes_pos {d : ParDeclItem} (h : GrParDeclItem toks d rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @basic ts₁ t x ts₂ v r ht hv =>
    obtain ⟨pre₂, rfl⟩ := hv.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @array ts₁ i ts₂ t x ts₃ v r hi ht hv =>
    obtain ⟨pre₃, rfl⟩ := hv.suffix
    obtain ⟨pre₂, rfl⟩ := ht.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrVarDeclItem.suffix {d : VarDeclItem} (h : GrVarDeclItem toks d rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @basicNoAssign ts t x ts₂ a r ht ha =>
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    exact ⟨pre₁ ++ .colon :: .ident x :: pre₂ ++ [.semi], by simp⟩
  | @basicAssign ts t x ts₂ a ts₃ v r ht ha hv =>
    obtain ⟨pre₃, rfl⟩ := hv.suffix
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    exact ⟨pre₁ ++ .colon :: .ident x :: pre₂ ++ .eq :: pre₃ ++ [.semi], by simp⟩
  | @array ts₁ i ts₂ t x ts₃ a ts₄ es r hi ht ha hl =>
    obtain ⟨pre₄, rfl⟩ := hl.suffix GrBasicExpr.suffix
    obtain ⟨pre₃, rfl⟩ := ha.suffix
    obtain ⟨pre₂, rfl⟩ := ht.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    exact ⟨.kwArray :: .lBrack :: pre₁ ++ .rBrack :: .kwOf :: pre₂ ++ .colon :: .ident x :: pre₃
      ++ .eq :: .lBrack :: pre₄ ++ [.rBrack, .semi], by simp⟩

theorem GrVarDeclItem.consumes_pos {d : VarDeclItem} (h : GrVarDeclItem toks d rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @basicNoAssign ts t x ts₂ a r ht ha =>
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @basicAssign ts t x ts₂ a ts₃ v r ht ha hv =>
    obtain ⟨pre₃, rfl⟩ := hv.suffix
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := ht.suffix
    simp only [List.length_cons, List.length_append]
    omega
  | @array ts₁ i ts₂ t x ts₃ a ts₄ es r hi ht ha hl =>
    obtain ⟨pre₄, rfl⟩ := hl.suffix GrBasicExpr.suffix
    obtain ⟨pre₃, rfl⟩ := ha.suffix
    obtain ⟨pre₂, rfl⟩ := ht.suffix
    obtain ⟨pre₁, rfl⟩ := hi.suffix
    simp only [List.length_cons, List.length_append]
    omega

theorem GrConstraintItem.suffix {c : ConstraintItem} (h : GrConstraintItem toks c rest) :
    ∃ pre, toks = pre ++ rest := by
  cases h with
  | @mk x args ts₁ ts₂ a r hid hl ha =>
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := hl.suffix GrExpr.suffix
    exact ⟨.kwConstraint :: .ident x :: .lParen :: pre₁ ++ .rParen :: pre₂ ++ [.semi], by simp⟩

theorem GrConstraintItem.consumes_pos {c : ConstraintItem} (h : GrConstraintItem toks c rest) :
    1 ≤ toks.length - rest.length := by
  cases h with
  | @mk x args ts₁ ts₂ a r hid hl ha =>
    obtain ⟨pre₂, rfl⟩ := ha.suffix
    obtain ⟨pre₁, rfl⟩ := hl.suffix GrExpr.suffix
    simp only [List.length_cons, List.length_append]
    omega

end SuffixBounds

end LeanFzn.Parser

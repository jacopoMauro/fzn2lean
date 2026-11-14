/-
Purpose: Each printable solution token is consumed by the actual lexer, at any
input offset and with any accumulator; whitespace boundaries remain explicit.
Dependencies: LexerRender proves identifier and decimal integer lexing.
DAG: LexerRender -> LexerToken -> LexerLayout -> emitter string round trip.
-/
import LeanFzn.Parser.Proofs.LexerRender

namespace LeanFzn.Parser.Lexer

private theorem digit_not_alpha {c : Char} (h : isDigit c = true) : isAlpha c = false := by
  simp only [isDigit, isAlpha, Char.le_def, UInt32.le_iff_toNat_le, Bool.and_eq_true,
    Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_true_eq,
    decide_eq_false_iff_not] at *
  change 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 at h
  change (65 ≤ c.val.toNat → ¬ c.val.toNat ≤ 90) ∧
    (97 ≤ c.val.toNat → ¬ c.val.toNat ≤ 122)
  constructor <;> intro hh <;> omega

private theorem int_toString_head (i : Int) : ∃ c cs,
    (toString i).toList = c :: cs ∧ (isDigit c || c == '-') = true ∧
    isAlpha c = false ∧ (c == '_') = false := by
  cases i with
  | ofNat n =>
      have hne : n.repr.toList ≠ [] := by rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
      obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
      have hc : isDigit c = true := isDigit_of_mem_nat_repr (by rw [hcs]; simp)
      refine ⟨c, cs, hcs, by simp [hc], digit_not_alpha hc, ?_⟩
      apply beq_eq_false_iff_ne.mpr
      intro h
      subst c
      contradiction
  | negSucc n =>
      refine ⟨'-', (n+1).repr.toList, ?_, by decide, by decide, by decide⟩
      change ("-" ++ (n+1).repr).toList = _
      simp

/-- A printed scalar/punctuation token has a nonempty, nontrivia first character. -/
theorem renderSolutionToken_head (t : Token) (ht : PrintableSolutionToken t) :
    ∃ c cs, (renderSolutionToken t).toList = c :: cs ∧
      isWhitespace c = false ∧ (c == '%') = false := by
  cases t with
  | ident s =>
      obtain ⟨⟨c, cs, hc, hfirst, _⟩, _⟩ := ht
      refine ⟨c, cs, hc, ?_, ?_⟩
      · unfold isWhitespace
        apply Bool.or_eq_false_iff.mpr
        constructor
        · apply Bool.or_eq_false_iff.mpr
          constructor
          · apply Bool.or_eq_false_iff.mpr
            constructor <;> apply beq_eq_false_iff_ne.mpr <;>
              intro h <;> subst c <;> simp [isAlpha] at hfirst
          · apply beq_eq_false_iff_ne.mpr
            intro h; subst c; simp [isAlpha] at hfirst
        · apply beq_eq_false_iff_ne.mpr
          intro h; subst c; simp [isAlpha] at hfirst
      · apply beq_eq_false_iff_ne.mpr
        intro h; subst c; simp [isAlpha] at hfirst
  | intLit i =>
      obtain ⟨c, cs, hc, hfirst, _⟩ := int_toString_head i
      refine ⟨c, cs, hc, ?_, ?_⟩
      · unfold isWhitespace
        apply Bool.or_eq_false_iff.mpr
        constructor
        · apply Bool.or_eq_false_iff.mpr
          constructor
          · apply Bool.or_eq_false_iff.mpr
            constructor <;> apply beq_eq_false_iff_ne.mpr <;>
              intro h <;> subst c <;> simp [isDigit] at hfirst
          · apply beq_eq_false_iff_ne.mpr
            intro h; subst c; simp [isDigit] at hfirst
        · apply beq_eq_false_iff_ne.mpr
          intro h; subst c; simp [isDigit] at hfirst
      · apply beq_eq_false_iff_ne.mpr
        intro h; subst c; simp [isDigit] at hfirst
  | boolLit b => cases b <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | lParen | rParen | lBrack | rBrack | lBrace | rBrace | comma | semi | eq | dotDot =>
      exact ⟨_, _, rfl, by decide, by decide⟩
  | _ => cases ht

/-- The rendered token length is always positive. -/
theorem renderSolutionToken_length_pos (t : Token) (ht : PrintableSolutionToken t) :
    0 < (renderSolutionToken t).length := by
  obtain ⟨c, cs, hc, _, _⟩ := renderSolutionToken_head t ht
  rw [← String.length_toList, hc]
  simp

/-- Every printable token is recovered from its canonical spelling in an
arbitrary character context. -/
theorem lexToken_renderSolutionToken (t : Token) (ht : PrintableSolutionToken t)
    (pre tail : Array Char)
    (h : pre.size < (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail).size) :
    lexToken (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
      pre.size h =
      .ok (t, ⟨pre.size + (renderSolutionToken t).length, by
        have := renderSolutionToken_length_pos t ht; omega⟩) := by
  cases t with
  | ident s =>
      obtain ⟨⟨c, cs, hc, hfirst, htail⟩, hkey, hres⟩ := ht
      have hw := lexToken_word s c cs hc hfirst htail hres pre tail h
      simpa only [renderSolutionToken, hkey, Option.getD] using hw
  | boolLit b =>
      cases b
      · exact lexToken_word "false" 'f' ['a', 'l', 's', 'e'] rfl
          (by decide) (by decide) (by decide) pre tail h
      · exact lexToken_word "true" 't' ['r', 'u', 'e'] rfl
          (by decide) (by decide) (by decide) pre tail h
  | intLit i => exact lexToken_toString i pre tail h
  | lParen =>
      have hg : (pre ++ (renderSolutionToken .lParen).toList.toArray ++ #[' '] ++ tail)[pre.size] = '(' := by
        change (pre ++ #['('] ++ #[' '] ++ tail)[pre.size] = '('
        simpa only [Array.append_assoc] using
          input_get_head pre '(' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | rParen =>
      have hg : (pre ++ (renderSolutionToken .rParen).toList.toArray ++ #[' '] ++ tail)[pre.size] = ')' := by
        change (pre ++ #[')'] ++ #[' '] ++ tail)[pre.size] = ')'
        simpa only [Array.append_assoc] using
          input_get_head pre ')' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | lBrack =>
      have hg : (pre ++ (renderSolutionToken .lBrack).toList.toArray ++ #[' '] ++ tail)[pre.size] = '[' := by
        change (pre ++ #['['] ++ #[' '] ++ tail)[pre.size] = '['
        simpa only [Array.append_assoc] using
          input_get_head pre '[' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | rBrack =>
      have hg : (pre ++ (renderSolutionToken .rBrack).toList.toArray ++ #[' '] ++ tail)[pre.size] = ']' := by
        change (pre ++ #[']'] ++ #[' '] ++ tail)[pre.size] = ']'
        simpa only [Array.append_assoc] using
          input_get_head pre ']' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | lBrace =>
      have hg : (pre ++ (renderSolutionToken .lBrace).toList.toArray ++ #[' '] ++ tail)[pre.size] = '{' := by
        change (pre ++ #['{'] ++ #[' '] ++ tail)[pre.size] = '{'
        simpa only [Array.append_assoc] using
          input_get_head pre '{' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | rBrace =>
      have hg : (pre ++ (renderSolutionToken .rBrace).toList.toArray ++ #[' '] ++ tail)[pre.size] = '}' := by
        change (pre ++ #['}'] ++ #[' '] ++ tail)[pre.size] = '}'
        simpa only [Array.append_assoc] using
          input_get_head pre '}' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | comma =>
      have hg : (pre ++ (renderSolutionToken .comma).toList.toArray ++ #[' '] ++ tail)[pre.size] = ',' := by
        change (pre ++ #[','] ++ #[' '] ++ tail)[pre.size] = ','
        simpa only [Array.append_assoc] using
          input_get_head pre ',' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | semi =>
      have hg : (pre ++ (renderSolutionToken .semi).toList.toArray ++ #[' '] ++ tail)[pre.size] = ';' := by
        change (pre ++ #[';'] ++ #[' '] ++ tail)[pre.size] = ';'
        simpa only [Array.append_assoc] using
          input_get_head pre ';' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | eq =>
      have hg : (pre ++ (renderSolutionToken .eq).toList.toArray ++ #[' '] ++ tail)[pre.size] = '=' := by
        change (pre ++ #['='] ++ #[' '] ++ tail)[pre.size] = '='
        simpa only [Array.append_assoc] using
          input_get_head pre '=' (#[' '] ++ tail)
      unfold lexToken
      simp only [hg]
      rfl
  | dotDot =>
      have hg : (pre ++ (renderSolutionToken .dotDot).toList.toArray ++ #[' '] ++ tail)[pre.size] = '.' := by
        change (pre ++ #['.', '.'] ++ #[' '] ++ tail)[pre.size] = '.'
        simp only [show #['.', '.'] = #['.'] ++ #['.'] from rfl]
        simpa only [Array.append_assoc] using
          input_get_head pre '.' (#['.'] ++ #[' '] ++ tail)
      have hg2 : (pre ++ (renderSolutionToken .dotDot).toList.toArray ++ #[' '] ++ tail)[pre.size+1]! = '.' := by
        change (pre ++ #['.', '.'] ++ #[' '] ++ tail)[pre.size+1]! = '.'
        simp only [show #['.', '.'] = #['.'] ++ #['.'] from rfl]
        have hg := input_getElem!_head (pre.push '.') '.' (#[' '] ++ tail)
        simpa only [Array.size_push, Array.push_eq_append, Array.size_append,
          Array.size_singleton, Array.append_assoc] using hg
      unfold lexToken
      simp only [hg, hg2]
      have hb : pre.size + 1 < (pre ++ (renderSolutionToken .dotDot).toList.toArray ++ #[' '] ++ tail).size := by
        simp [renderSolutionToken]; omega
      simp only [hb, decide_true, beq_self_eq_true, Bool.and_self, ite_true]
      rfl
  | _ => cases ht

/-- A token spelling starts at a significant character, so trivia skipping
leaves its position unchanged. -/
theorem skipTrivia_renderSolutionToken (t : Token) (ht : PrintableSolutionToken t)
    (pre tail : Array Char) :
    skipTrivia (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
      pre.size = pre.size := by
  obtain ⟨c, cs, hc, hw, hp⟩ := renderSolutionToken_head t ht
  have hlt : pre.size < (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail).size := by
    have := renderSolutionToken_length_pos t ht
    simp only [Array.size_append, List.size_toArray, String.length_toList]
    omega
  have hg : (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)[pre.size] = c := by
    simp only [hc, List.toArray_cons c cs]
    simpa only [Array.append_assoc] using
      input_get_head pre c (cs.toArray ++ #[' '] ++ tail)
  rw [skipTrivia.eq_def]
  simp only [hlt, ↓reduceDIte, hg, hw, hp, Bool.false_eq_true, ite_false]

private def renderedLexContinue (s : Input) (pos : Nat) (acc : Array Token) :
    Except String (Array Token) := do
  if h : pos < s.size then
    let (tok, ⟨pos', _⟩) ← lexToken s pos h
    tokenizeAux s pos' (acc.push tok)
  else pure acc

private theorem tokenizeAux_renderedContinue (s : Input) (pos : Nat) (acc : Array Token) :
    tokenizeAux s pos acc = renderedLexContinue s (skipTrivia s pos) acc := by
  rw [tokenizeAux.eq_def]
  rfl

/-- The actual lexer consumes one rendered token, for arbitrary left/right
contexts and token accumulator. No lexer-success premise is assumed. -/
theorem tokenizeAux_renderSolutionToken_step (t : Token) (ht : PrintableSolutionToken t)
    (pre tail : Array Char) (acc : Array Token) :
    tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
      pre.size acc =
    tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
      (pre.size + (renderSolutionToken t).length) (acc.push t) := by
  have hlt : pre.size < (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail).size := by
    have := renderSolutionToken_length_pos t ht
    simp only [Array.size_append, List.size_toArray, String.length_toList]
    omega
  have hs := skipTrivia_renderSolutionToken t ht pre tail
  have hl := lexToken_renderSolutionToken t ht pre tail hlt
  rw [tokenizeAux_renderedContinue, hs]
  unfold renderedLexContinue
  simp only [hlt, ↓reduceDIte, hl, Bind.bind, Except.bind]

end LeanFzn.Parser.Lexer

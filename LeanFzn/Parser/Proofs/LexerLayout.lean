/-
Purpose: Lift atomic token rendering to complete solution token streams, with
arbitrary whitespace and preserved assignment-line boundaries.
Dependencies: SolutionRender fixes canonical token spellings; LexerToken
supplies the atomic lexer step used to verify complete rendered text.
DAG: LexerRender -> LexerToken -> LexerLayout -> Integration.Emit.RoundTrip.
-/
import LeanFzn.Parser.Proofs.LexerToken
import Lean
import Init.Data.Array.Lemmas

namespace LeanFzn.Parser.Lexer

/-- Character-level layouts consisting solely of printable tokens, explicit
lexical boundaries, and whitespace. This relation does not call the lexer. -/
inductive RenderedSolutionTokens : List Char → List Token → Prop where
  | nil : RenderedSolutionTokens [] []
  | whitespace (c : Char) (hc : isWhitespace c = true) :
      RenderedSolutionTokens cs ts → RenderedSolutionTokens (c :: cs) ts
  | token (t : Token) (ht : PrintableSolutionToken t) :
      RenderedSolutionTokens cs ts →
      RenderedSolutionTokens ((renderSolutionToken t).toList ++ ' ' :: cs) (t :: ts)

/-- Canonical printing is one of the independent lexical layouts. -/
theorem renderedSolutionTokens (ts : List Token)
    (h : ∀ t ∈ ts, PrintableSolutionToken t) :
    RenderedSolutionTokens (renderSolutionTokens ts).toList ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih =>
      simpa only [renderSolutionTokens, String.toList_append, List.append_assoc,
        List.cons_append, List.nil_append, show " ".toList = [' '] from rfl] using
        RenderedSolutionTokens.token t (h t (by simp))
          (ih (fun x hx => h x (by simp [hx])))

/-- Lexical layouts compose without identifying neighboring tokens. -/
theorem RenderedSolutionTokens.append {cs ds : List Char} {ts us : List Token}
    (hc : RenderedSolutionTokens cs ts) (hd : RenderedSolutionTokens ds us) :
    RenderedSolutionTokens (cs ++ ds) (ts ++ us) := by
  induction hc with
  | nil => exact hd
  | whitespace c hc _ ih => exact .whitespace c hc ih
  | token t ht _ ih =>
      simpa only [List.append_assoc, List.cons_append] using
        RenderedSolutionTokens.token t ht ih

private def lexContinue (s : Input) (pos : Nat) (acc : Array Token) : Except String (Array Token) := do
  if h : pos < s.size then
    let (tok, ⟨pos', _⟩) ← lexToken s pos h
    tokenizeAux s pos' (acc.push tok)
  else pure acc

private theorem tokenizeAux_continue (s : Input) (pos : Nat) (acc : Array Token) :
    tokenizeAux s pos acc = lexContinue s (skipTrivia s pos) acc := by
  rw [tokenizeAux.eq_def]
  rfl

/-- Moving past one known whitespace character leaves tokenization unchanged. -/
theorem tokenizeAux_whitespace (s : Input) (pos : Nat) (acc : Array Token)
    (h : pos < s.size) (hw : isWhitespace s[pos] = true) :
    tokenizeAux s pos acc = tokenizeAux s (pos + 1) acc := by
  have hskip : skipTrivia s pos = skipTrivia s (pos + 1) := by
    rw [skipTrivia.eq_def]
    simp only [h, dite_eq_left, hw, ite_true]
  rw [tokenizeAux_continue, tokenizeAux_continue, hskip]

private theorem listToArray_append (xs ys : List α) :
    (xs ++ ys).toArray = xs.toArray ++ ys.toArray := by
  apply Array.ext'
  simp

private theorem getElem_prefix_char (pre tail : Array Char) (c : Char) :
    (pre ++ #[c] ++ tail)[pre.size]'(by simp; omega) = c := by
  simp (disch := omega) [Array.getElem_append]

/-- Internal compositional lifting lemma. The atomic rendering fact is proved
separately; this helper introduces no lexical-success premise on output text. -/
theorem tokenizeAux_of_rendered_step
    (step : ∀ (t : Token), PrintableSolutionToken t →
      ∀ (pre tail : Array Char) (acc : Array Token),
        tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail) pre.size acc =
        tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
          (pre.size + (renderSolutionToken t).length) (acc.push t))
    {cs : List Char} {ts : List Token} (h : RenderedSolutionTokens cs ts)
    (pre : Array Char) (acc : Array Token) :
    tokenizeAux (pre ++ cs.toArray) pre.size acc = .ok (acc ++ ts.toArray) := by
  induction h generalizing pre acc with
  | nil =>
      change tokenizeAux pre pre.size acc = .ok (acc ++ #[])
      simp only [Array.append_empty]
      rw [tokenizeAux.eq_def]
      have hs : skipTrivia pre pre.size = pre.size := by
        rw [skipTrivia.eq_def]
        simp
      simp only [hs, Nat.lt_irrefl]
      rfl
  | @whitespace cs ts c hc h ih =>
      rw [List.toArray_cons]
      have hws := tokenizeAux_whitespace (pre ++ #[c] ++ cs.toArray) pre.size acc (by simp)
        (by simpa only [getElem_prefix_char] using hc)
      rw [show pre ++ (#[c] ++ cs.toArray) = pre ++ #[c] ++ cs.toArray by rw [Array.append_assoc]]
      rw [hws]
      simpa only [Array.push_eq_append, Array.size_append, Array.size_singleton,
        List.length_cons, List.length_nil, Nat.add_zero] using ih (pre ++ #[c]) acc
  | @token cs ts t ht h ih =>
      rw [listToArray_append, List.toArray_cons]
      rw [← Array.append_assoc, ← Array.append_assoc]
      rw [step t ht]
      have hws := tokenizeAux_whitespace
        ((pre ++ (renderSolutionToken t).toList.toArray) ++ #[' '] ++ cs.toArray)
        (pre ++ (renderSolutionToken t).toList.toArray).size (acc.push t)
        (by simp) (by rw [getElem_prefix_char]; rfl)
      simp only [Array.size_append, List.size_toArray, String.length_toList] at hws
      rw [hws]
      have hrec := ih (pre ++ (renderSolutionToken t).toList.toArray ++ #[' ']) (acc.push t)
      rw [List.toArray_cons t]
      simpa only [Array.size_append, Array.size_singleton, List.size_toArray,
        String.length_toList, List.length_cons, List.length_nil, Nat.add_zero,
        Array.push_eq_append, Array.append_assoc, Nat.add_assoc, Nat.zero_add] using hrec

/-- Rendering successive assignment token chunks with physical newlines is
also an independent lexical layout of their concatenated tokens. -/
theorem renderedSolutionTokenLines (tss : List (List Token))
    (h : ∀ ts ∈ tss, ∀ t ∈ ts, PrintableSolutionToken t) :
    RenderedSolutionTokens
      (String.intercalate "\n" (tss.map renderSolutionTokens)).toList tss.flatten := by
  induction tss with
  | nil => exact .nil
  | cons ts tss ih =>
      cases tss with
      | nil =>
          simpa only [List.map_cons, List.map_nil, String.intercalate_singleton,
            List.flatten_cons, List.flatten_nil, List.append_nil] using
            renderedSolutionTokens ts (h ts (by simp))
      | cons us tss =>
          have hfirst := renderedSolutionTokens ts (h ts (by simp))
          have hrest := ih (fun xs hx => h xs (by simp [hx]))
          have hgap := RenderedSolutionTokens.whitespace '\n' (by rfl) hrest
          simpa only [List.map_cons, String.intercalate_cons_cons,
            String.toList_append, List.append_assoc, List.flatten_cons,
            show "\n".toList = ['\n'] from rfl, List.cons_append, List.nil_append] using
            hfirst.append hgap

/-- A character-level lexical layout tokenizes to exactly its specified tokens,
provided the separately proved atomic token-rendering step is available. -/
theorem tokenize_of_rendered_step
    (step : ∀ (t : Token), PrintableSolutionToken t →
      ∀ (pre tail : Array Char) (acc : Array Token),
        tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail) pre.size acc =
        tokenizeAux (pre ++ (renderSolutionToken t).toList.toArray ++ #[' '] ++ tail)
          (pre.size + (renderSolutionToken t).length) (acc.push t))
    {s : String} {ts : List Token} (h : RenderedSolutionTokens s.toList ts) :
    tokenize s = .ok ts.toArray := by
  have hh := tokenizeAux_of_rendered_step step h #[] #[]
  simpa only [Array.empty_append, Array.size_empty, String.toList,
    Array.toArray_toList, tokenize] using hh

/-- Complete lexical round trip for canonical non-float solution token text.
The only precondition describes characters and token kinds, not lexer success. -/
theorem tokenize_renderSolutionTokens (ts : List Token)
    (h : ∀ t ∈ ts, PrintableSolutionToken t) :
    tokenize (renderSolutionTokens ts) = .ok ts.toArray := by
  exact tokenize_of_rendered_step tokenizeAux_renderSolutionToken_step
    (renderedSolutionTokens ts h)

/-- Complete lexical round trip for the multiline layout used by actual solver
emission: line boundaries do not alter any literal or array/set delimiter. -/
theorem tokenize_renderSolutionTokenLines (tss : List (List Token))
    (h : ∀ ts ∈ tss, ∀ t ∈ ts, PrintableSolutionToken t) :
    tokenize (String.intercalate "\n" (tss.map renderSolutionTokens)) =
      .ok tss.flatten.toArray := by
  exact tokenize_of_rendered_step tokenizeAux_renderSolutionToken_step
    (renderedSolutionTokenLines tss h)

end LeanFzn.Parser.Lexer

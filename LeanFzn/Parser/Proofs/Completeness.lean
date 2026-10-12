import LeanFzn.Parser.Proofs.Correctness
import LeanFzn.Parser.Suffix
open LeanFzn.Semantics LeanFzn.Parser


-- See `FznCorrectness.lean`: split-driven proofs carry per-branch load-bearing
-- hypotheses that the simp linter flags as unused.
set_option linter.unusedSimpArgs false

/-
# Parser Completeness (integer/Boolean fragment)

We prove that the fuelled recursive-descent parser is complete with respect
to the grammar relations of `FznGrammar.lean`:

**Completeness** (`parseModel_complete`): if the string `s` derives the model
`m` according to the grammar (`Grammar s m`), then `parseModel s = .ok m`.

## Proof strategy

Each parser function `parseX fuel st` gets a lemma of the form

```
GrX st.remaining ast rest → (fuel adequacy) → (boundary hypotheses) →
  ∃ st', parseX fuel st = .ok (ast, st') ∧ st'.remaining = rest
```

The bridge between the array-based parser state and the list-based grammar
relation is `State.remaining` (as in `FznCorrectness.lean`).

### Fuel adequacy

The parser is fuelled; completeness requires that the fuel never runs out.
The invariant maintained throughout is

```
2 * st.remaining.length + K ≤ fuel
```

for a per-parser constant `K`.  The factor 2 is needed because
`parseAnnExpr` → `parseAnnExprArrayContents` → `parseAnnExpr` consumes two
fuel units per token of nesting.  The top-level fuel `parseFuel toks =
8 * (toks.size + 1)` satisfies `2 * n + 4 ≤ 8 * (n + 1)` for every `n`.

### Boundary hypotheses

The grammar relations are nondeterministic where the parser commits to a
branch by one-token lookahead.  Completeness lemmas therefore carry
hypotheses about the tokens that follow the parsed phrase:

* separated lists end at a known delimiter (`.rBrace`, `.rBrack`, `.rParen`,
  `.semi`, or `.comma`), which distinguishes the empty list from an element;
* an integer literal is not the start of a range (`rest ≠ .dotDot :: r`);
* a plain annotation identifier is not followed by `(`;
* an empty annotation list is not followed by `::`.

These hypotheses are discharged inductively from the structure of the
enclosing derivation.  Technically, the boundary is baked into the type of
the derivation hypothesis (e.g. `GrSepList GrIntAtom st.remaining elems
(.rBrace :: r')`), which keeps the recursive-call indices unified.
-/

open LeanFzn.Semantics

namespace LeanFzn.Parser

open LeanFzn

open LeanFzn.Parser.Lexer LeanFzn.Parser

/-! ## Additional bridge lemmas -/

/-- `check t st = false` when the remaining tokens do not start with `t`. -/
theorem check_false_of_remaining_ne {t : Token} {st : State}
    (h : ∀ r, st.remaining ≠ t :: r) : check t st = false := by
  cases hcc : check t st with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨rest, hrest⟩ := check_remaining hcc
    exact h rest hrest

/-- The parser does not see `t` next when the remaining tokens do not start
    with `t`. -/
theorem peek?_ne_of_remaining_ne {t : Token} {st : State}
    (h : ∀ r, st.remaining ≠ t :: r) : st.peek? ≠ some t := by
  intro hcon
  have htrue : check t st = true := by
    unfold check; rw [hcon]; simp
  obtain ⟨rest, hrest⟩ := check_remaining htrue
  exact h rest hrest

/-! ## Completeness of the integer-list parsers -/

/-- Completeness of the `"," int` continuation of an integer list ending at
    `}`.  The tail parser is self-recursive, so this lemma recurses on
    itself (through the fuel). -/
theorem parseIntListTail_complete {fuel st elems r'}
    (h : GrSepListTail GrIntAtom st.remaining elems (.rBrace :: r'))
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parseIntListTail fuel st = .ok (elems, st') ∧ st'.remaining = .rBrace :: r' := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseIntListTail
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ i ts₂ xs rst h₁ h₂ =>
      cases h₁
      have hrem : st.remaining = .comma :: .intLit i :: ts₂ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      obtain ⟨hi, hremi⟩ := parseIntLit_complete hremc
      have h₂' : GrSepListTail GrIntAtom st.advance.advance.remaining xs (.rBrace :: r') := by
        rw [hremi]; exact h₂
      have hfuel' : 2 * st.advance.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 2 + st.advance.advance.remaining.length := by
          rw [hremi, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntListTail_complete h₂' hfuel'
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseIntListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hi, hparse, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of comma-separated integer lists ending at `}`. -/
theorem parseIntList_complete {fuel st elems r'}
    (h : GrSepList GrIntAtom st.remaining elems (.rBrace :: r'))
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parseIntList fuel st = .ok (elems, st') ∧ st'.remaining = .rBrace :: r' := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseIntList
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ i ts₂ xs ts₃ h₁ h₂ =>
      cases h₁
      have hrem : st.remaining = .intLit i :: ts₂ := heq
      obtain ⟨hi, hremi⟩ := parseIntLit_complete hrem
      have h₂' : GrSepListTail GrIntAtom st.advance.remaining xs (.rBrace :: r') := by
        rw [hremi]; exact h₂
      have hfuel' : 2 * st.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hremi, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntListTail_complete h₂' hfuel'
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseIntList
      simp only [peek?_eq_of_remaining_cons hrem, hi, hparse, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the non-empty integer list parser. -/
theorem parseNonemptyIntList_complete {fuel st elems r'}
    (h : GrSepList GrIntAtom st.remaining elems (.rBrace :: r'))
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) (hne : elems ≠ []) :
    ∃ st', parseNonemptyIntList fuel st = .ok (elems, st') ∧ st'.remaining = .rBrace :: r' := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil => exact absurd rfl hne
    | @cons ts₁ i ts₂ ys ts₃ h₁ h₂ =>
      cases h₁
      have hrem : st.remaining = .intLit i :: ts₂ := heq
      obtain ⟨hi, hremi⟩ := parseIntLit_complete hrem
      have h₂' : GrSepListTail GrIntAtom st.advance.remaining ys (.rBrace :: r') := by
        rw [hremi]; exact h₂
      have hfuel' : 2 * st.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hremi, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntListTail_complete h₂' hfuel'
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseNonemptyIntList
      simp only [hi, hparse, Bind.bind, Except.bind, pure, Except.pure]

/-! ## Completeness of basic literals -/

/-- Completeness of the basic-literal parser.  The hypothesis `hnd`
    (the tokens after the literal do not continue with `..`) rules out the
    range reading of an integer literal. -/
theorem parseBasicLiteral_complete {fuel st l rest}
    (h : GrBasicLiteral st.remaining l rest)
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel)
    (hnd : ∀ r, rest ≠ .dotDot :: r) :
    ∃ st', parseBasicLiteral fuel st = .ok (l, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @bool b r =>
      have hrem : st.remaining = .boolLit b :: rest := heq
      obtain ⟨hb, hrem1⟩ := parseBoolLit_complete hrem
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseBasicLiteral
      simp only [peek?_eq_of_remaining_cons hrem, hb, Bind.bind, Except.bind,
        pure, Except.pure]
    | @int i r =>
      have hrem : st.remaining = .intLit i :: rest := heq
      obtain ⟨hi, hrem1⟩ := parseIntLit_complete hrem
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseBasicLiteral
      simp only [peek?_eq_of_remaining_cons hrem, hi, Bind.bind, Except.bind,
        pure, Except.pure]
      have hchk : check .dotDot st.advance = false :=
        check_false_of_remaining_ne (fun r hr => hnd r (by rw [hrem1] at hr; exact hr))
      simp only [hchk]
      simp
    | @intRange lo hi r =>
      have hrem : st.remaining = .intLit lo :: .dotDot :: .intLit hi :: rest := heq
      obtain ⟨hlo, hrem1⟩ := parseIntLit_complete hrem
      obtain ⟨hdot, hrem2⟩ := expectTok_complete (what := "'..'") hrem1
      obtain ⟨hhi, hrem3⟩ := parseIntLit_complete hrem2
      refine ⟨st.advance.advance.advance, ?_, hrem3⟩
      unfold parseBasicLiteral
      simp only [peek?_eq_of_remaining_cons hrem, hlo, hdot, hhi, Bind.bind, Except.bind,
        pure, Except.pure]
      have hchk : check .dotDot st.advance = true := by
        unfold check
        rw [peek?_eq_of_remaining_cons hrem1]
        rfl
      simp only [hchk, ↓reduceIte]
    | @intSet ts es r hl =>
      have hrem : st.remaining = .lBrace :: ts := heq
      obtain ⟨hbr, hrem1⟩ := expectTok_complete (what := "'{'") hrem
      have hl' : GrSepList GrIntAtom st.advance.remaining es (.rBrace :: rest) := by
        rw [hrem1]; exact hl
      have hfuel' : 2 * st.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntList_complete hl' hfuel'
      obtain ⟨hbr', hrem2⟩ := expectTok_complete (what := "'}'") hrem₁
      refine ⟨st₁.advance, ?_, hrem2⟩
      unfold parseBasicLiteral
      simp only [peek?_eq_of_remaining_cons hrem, hbr, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]

/-! ## Completeness of the expression parsers -/

/-- Head-token analysis: a basic-literal derivation starts with a literal
    token, never an identifier. -/
theorem GrBasicLiteral.head_not_ident {toks : List Token} {l : BasicLiteral} {rest : List Token}
    (h : GrBasicLiteral toks l rest) :
    ∃ (t : Token) (r : List Token), toks = t :: r ∧ (∀ x, t ≠ .ident x) := by
  cases h with
  | bool => rename_i b; exact ⟨.boolLit b, rest, rfl, by simp⟩
  | int => rename_i i; exact ⟨.intLit i, rest, rfl, by simp⟩
  | intRange => rename_i lo hi; exact ⟨.intLit lo, .dotDot :: .intLit hi :: rest, rfl, by simp⟩
  | intSet => rename_i ts es hl; exact ⟨.lBrace, ts, rfl, by simp⟩

/-- Completeness of the basic-expression parser.  The hypothesis `hnd`
    rules out the range reading of an integer literal (see
    `parseBasicLiteral_complete`). -/
theorem parseBasicExpr_complete {fuel st e rest}
    (h : GrBasicExpr st.remaining e rest)
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel)
    (hnd : ∀ r, rest ≠ .dotDot :: r) :
    ∃ st', parseBasicExpr fuel st = .ok (e, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @lit l ts r hl =>
      have hl' : GrBasicLiteral st.remaining ts rest := by rw [heq]; exact hl
      have hfuel' : 2 * st.remaining.length + 2 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicLiteral_complete hl' hfuel' hnd
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseBasicExpr
      obtain ⟨t, r, hrem, hne⟩ := GrBasicLiteral.head_not_ident hl
      rw [← heq] at hrem
      have hpeek := peek?_eq_of_remaining_cons hrem
      cases t with
      | ident x => exact absurd rfl (hne x)
      | _ =>
        simp only [hpeek, hparse, Bind.bind, Except.bind, pure, Except.pure]
    | @ident x r =>
      have hrem : st.remaining = .ident x :: rest := heq
      obtain ⟨hx, hrem1⟩ := parseIdent_complete hrem
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseBasicExpr
      simp only [peek?_eq_of_remaining_cons hrem, hx, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Head-token analysis: a basic-expression derivation starts with a token
    that is not `[` (an identifier or a literal token). -/
theorem GrBasicExpr.head_not_lBrack {toks : List Token} {e : BasicExpr} {rest : List Token}
    (h : GrBasicExpr toks e rest) :
    ∃ (t : Token) (r : List Token), toks = t :: r ∧ t ≠ .lBrack := by
  cases h with
  | @lit l ts r hl =>
    cases hl with
    | bool => rename_i b; exact ⟨.boolLit b, rest, rfl, by simp⟩
    | int => rename_i i; exact ⟨.intLit i, rest, rfl, by simp⟩
    | intRange => rename_i lo hi; exact ⟨.intLit lo, _, rfl, by simp⟩
    | intSet => rename_i ts es hl; exact ⟨.lBrace, ts, rfl, by simp⟩
  | ident => rename_i x; exact ⟨.ident x, rest, rfl, by simp⟩

/-- Head-token analysis: a basic-expression derivation starts with a token
    that is not `]` either (an identifier or a literal token). -/
theorem GrBasicExpr.head_not_rBrack {toks : List Token} {e : BasicExpr} {rest : List Token}
    (h : GrBasicExpr toks e rest) :
    ∃ (t : Token) (r : List Token), toks = t :: r ∧ t ≠ .rBrack := by
  cases h with
  | @lit l ts r hl =>
    cases hl with
    | bool => rename_i b; exact ⟨.boolLit b, rest, rfl, by simp⟩
    | int => rename_i i; exact ⟨.intLit i, rest, rfl, by simp⟩
    | intRange => rename_i lo hi; exact ⟨.intLit lo, _, rfl, by simp⟩
    | intSet => rename_i ts es hl; exact ⟨.lBrace, ts, rfl, by simp⟩
  | ident => rename_i x; exact ⟨.ident x, rest, rfl, by simp⟩

/-! ## Completeness of the expression-list parsers -/

/-! Completeness of the comma-separated basic-expression lists ending at
    `]`.  The list parsers are mutually recursive (list / tail), so their
    completeness lemmas are mutually recursive too.  The boundary (the list
    ends at `.rBrack`) both makes the empty case deterministic and rules out
    the range reading of integer literals inside the list (the token after an
    element is `,` or `]`, never `..`). -/
mutual
theorem parseBasicExprList_complete {fuel st elems rest}
    (h : GrSepList GrBasicExpr st.remaining elems (.rBrack :: rest))
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel) :
    ∃ st', parseBasicExprList fuel st = .ok (elems, st') ∧ st'.remaining = .rBrack :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseBasicExprList
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      -- the element's rest ts₂ is followed by `,` or `]`: never `..`
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrBasicExpr st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 3 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicExpr_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrBasicExpr st₁.remaining xs (.rBrack :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseBasicExprListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseBasicExprList
      -- the head is an element token, not `]`
      obtain ⟨t, r, hrem, hne⟩ := GrBasicExpr.head_not_rBrack h₁
      rw [← heq] at hrem
      have hpeek := peek?_eq_of_remaining_cons hrem
      cases t with
      | rBrack => exact absurd rfl hne
      | _ =>
        simp only [hpeek, hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]

theorem parseBasicExprListTail_complete {fuel st elems rest}
    (h : GrSepListTail GrBasicExpr st.remaining elems (.rBrack :: rest))
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel) :
    ∃ st', parseBasicExprListTail fuel st = .ok (elems, st') ∧ st'.remaining = .rBrack :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseBasicExprListTail
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs rst h₁ h₂ =>
      have hrem : st.remaining = .comma :: ts₁ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrBasicExpr st.advance.remaining x ts₂ := by
        rw [hremc]; exact h₁
      have hfuel' : 2 * st.advance.remaining.length + 3 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st.advance.remaining.length = ts₁.length := by rw [hremc]
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicExpr_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrBasicExpr st₁.remaining xs (.rBrack :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseBasicExprListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseBasicExprListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]
end

/-- Completeness of the array-literal parser. -/
theorem parseArrayLiteral_complete {fuel st elems rest}
    (h : GrExpr st.remaining (.array elems) rest)
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel)
    (_hnd : ∀ r, rest ≠ .dotDot :: r) :
    ∃ st', parseArrayLiteral fuel st = .ok (elems, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @array ts es r hl =>
      have hrem : st.remaining = .lBrack :: ts := heq
      obtain ⟨hbr, hrem1⟩ := expectTok_complete (what := "'['") hrem
      have hl' : GrSepList GrBasicExpr st.advance.remaining elems (.rBrack :: rest) := by
        rw [hrem1]; exact hl
      have hfuel' : 2 * st.advance.remaining.length + 4 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicExprList_complete hl' hfuel'
      obtain ⟨hbr', hrem2⟩ := expectTok_complete (what := "']'") hrem₁
      refine ⟨st₁.advance, ?_, hrem2⟩
      unfold parseArrayLiteral
      simp only [hbr, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the expression parser. -/
theorem parseExpr_complete {fuel st e rest}
    (h : GrExpr st.remaining e rest)
    (hfuel : 2 * st.remaining.length + 5 ≤ fuel)
    (hnd : ∀ r, rest ≠ .dotDot :: r) :
    ∃ st', parseExpr fuel st = .ok (e, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @basic b ts r hb =>
      have hb' : GrBasicExpr st.remaining ts rest := by rw [heq]; exact hb
      have hfuel' : 2 * st.remaining.length + 3 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicExpr_complete hb' hfuel' hnd
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseExpr
      obtain ⟨t, r, hrem, hne⟩ := GrBasicExpr.head_not_lBrack hb
      rw [← heq] at hrem
      have hpeek := peek?_eq_of_remaining_cons hrem
      cases t with
      | lBrack => exact absurd rfl hne
      | _ =>
        simp only [hpeek, hparse, Bind.bind, Except.bind, pure, Except.pure]
    | @array ts es r hl =>
      -- the parser delegates to parseArrayLiteral on `[`
      have hrem : st.remaining = .lBrack :: ts := heq
      have hfuel' : 2 * st.remaining.length + 4 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ :=
        parseArrayLiteral_complete (by rw [hrem]; exact GrExpr.array hl) hfuel' hnd
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseExpr
      simp only [peek?_eq_of_remaining_cons hrem, hparse, Bind.bind, Except.bind,
        pure, Except.pure]

/-! ## Completeness of the parameter-array-literal parsers -/

/-! Completeness of the comma-separated basic-literal lists ending at `]`.
    Mutually recursive (list / tail), as in `FznCorrectness.lean`. -/
mutual
theorem parseBasicLiteralList_complete {fuel st elems rest}
    (h : GrSepList GrBasicLiteral st.remaining elems (.rBrack :: rest))
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel) :
    ∃ st', parseBasicLiteralList fuel st = .ok (elems, st') ∧ st'.remaining = .rBrack :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseBasicLiteralList
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      -- the element's rest ts₂ is followed by `,` or `]`: never `..`
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrBasicLiteral st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 2 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicLiteral_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrBasicLiteral st₁.remaining xs (.rBrack :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 1 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseBasicLiteralListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseBasicLiteralList
      -- the head is a literal token, not `]`
      obtain ⟨t, r, hrem, hne⟩ := GrBasicLiteral.head_not_ident h₁
      have hpeek := peek?_eq_of_remaining_cons (by rw [heq]; exact hrem)
      cases t with
      | rBrack =>
        -- contradiction: a literal derivation cannot start with `]`
        exfalso
        have h₁'' : GrBasicLiteral (.rBrack :: r) x ts₂ := hrem ▸ h₁
        cases h₁''
      | _ =>
        simp only [hpeek, hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]

theorem parseBasicLiteralListTail_complete {fuel st elems rest}
    (h : GrSepListTail GrBasicLiteral st.remaining elems (.rBrack :: rest))
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parseBasicLiteralListTail fuel st = .ok (elems, st') ∧ st'.remaining = .rBrack :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseBasicLiteralListTail
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs rst h₁ h₂ =>
      have hrem : st.remaining = .comma :: ts₁ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrBasicLiteral st.advance.remaining x ts₂ := by
        rw [hremc]; exact h₁
      have hfuel' : 2 * st.advance.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st.advance.remaining.length = ts₁.length := by rw [hremc]
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicLiteral_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrBasicLiteral st₁.remaining xs (.rBrack :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 1 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseBasicLiteralListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseBasicLiteralListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]
end

/-- Completeness of the parameter-array-literal parser. -/
theorem parseParArrayLiteral_complete {fuel st elems rest}
    (h : GrParArrayLiteral st.remaining elems rest)
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel) :
    ∃ st', parseParArrayLiteral fuel st = .ok (elems, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @mk ts es r hl =>
      have hrem : st.remaining = .lBrack :: ts := heq
      obtain ⟨hbr, hrem1⟩ := expectTok_complete (what := "'['") hrem
      have hl' : GrSepList GrBasicLiteral st.advance.remaining elems (.rBrack :: rest) := by
        rw [hrem1]; exact hl
      have hfuel' : 2 * st.advance.remaining.length + 3 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicLiteralList_complete hl' hfuel'
      obtain ⟨hbr', hrem2⟩ := expectTok_complete (what := "']'") hrem₁
      refine ⟨st₁.advance, ?_, hrem2⟩
      unfold parseParArrayLiteral
      simp only [hbr, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]

/-! ## Completeness of the annotation parsers -/

/-- Head-token analysis: an annotation-expression derivation starts with a
    token that is not `]`. -/
theorem GrAnnExpr.head_not_rBrack {toks : List Token} {a : AnnExpr} {rest : List Token}
    (h : GrAnnExpr toks a rest) :
    ∃ (t : Token) (r : List Token), toks = t :: r ∧ t ≠ .rBrack := by
  cases h with
  | @lit l ts r hl =>
    cases hl with
    | bool => rename_i b; exact ⟨.boolLit b, rest, rfl, by simp⟩
    | int => rename_i i; exact ⟨.intLit i, rest, rfl, by simp⟩
    | intRange => rename_i lo hi; exact ⟨.intLit lo, _, rfl, by simp⟩
    | intSet => rename_i ts es hl; exact ⟨.lBrace, ts, rfl, by simp⟩
  | ident => rename_i x; exact ⟨.ident x, rest, rfl, by simp⟩
  | string => rename_i s; exact ⟨.stringLit s, rest, rfl, by simp⟩
  | annCall => rename_i x args ts hid hne hl; exact ⟨.ident x, .lParen :: ts, rfl, by simp⟩
  | array => rename_i ts es hl; exact ⟨.lBrack, ts, rfl, by simp⟩

/-! The annotation parsers are mutually recursive: an annotation call takes a
    list of annotation expressions, which may be nested annotation calls or
    annotation arrays.  The completeness lemmas are therefore a mutual block.
    The fuel invariant `2 * st.remaining.length + K ≤ fuel` is maintained
    because every recursive call either keeps the same remaining length with
    one less fuel (list heads) or strictly shortens the remaining list. -/
mutual
/-- Completeness of the annotation-expression parser.  The hypotheses rule
    out the other readings of the leading token: an integer literal is not a
    range (`hnd`), and a plain identifier is not followed by `(` (`hnp`). -/
theorem parseAnnExpr_complete {fuel st a rest}
    (h : GrAnnExpr st.remaining a rest)
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel)
    (hnd : ∀ r, rest ≠ .dotDot :: r)
    (hnp : ∀ r, rest ≠ .lParen :: r) :
    ∃ st', parseAnnExpr fuel st = .ok (a, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @lit l ts r hl =>
      have hl' : GrBasicLiteral st.remaining ts rest := by rw [heq]; exact hl
      have hfuel' : 2 * st.remaining.length + 2 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicLiteral_complete hl' hfuel' hnd
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseAnnExpr
      -- the head is a literal token (boolLit/intLit/lBrace): catch-all branch
      obtain ⟨t, r, hrem, hne⟩ := GrBasicLiteral.head_not_ident hl
      have hpeek := peek?_eq_of_remaining_cons (by rw [heq]; exact hrem)
      cases t with
      | ident x => exact absurd rfl (hne x)
      | stringLit s =>
        exfalso
        have hl'' : GrBasicLiteral (.stringLit s :: r) ts rest := hrem ▸ hl
        cases hl''
      | lBrack =>
        exfalso
        have hl'' : GrBasicLiteral (.lBrack :: r) ts rest := hrem ▸ hl
        cases hl''
      | _ =>
        simp only [hpeek, hparse, Bind.bind, Except.bind, pure, Except.pure]
    | @ident x r =>
      have hrem : st.remaining = .ident x :: rest := heq
      obtain ⟨hx, hrem1⟩ := parseIdent_complete hrem
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseAnnExpr
      simp only [peek?_eq_of_remaining_cons hrem, hx, Bind.bind, Except.bind, pure, Except.pure]
      have hpeek : st.advance.peek? ≠ some .lParen :=
        peek?_ne_of_remaining_ne (fun r hr => hnp r (by rw [hrem1] at hr; exact hr))
      cases hp : st.advance.peek? with
      | none => rfl
      | some t =>
        cases t with
        | lParen => exact absurd hp hpeek
        | _ => rfl
    | @string s r =>
      have hrem : st.remaining = .stringLit s :: rest := heq
      obtain ⟨hs, hrem1⟩ := parseStringLit_complete hrem
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseAnnExpr
      simp only [peek?_eq_of_remaining_cons hrem, hs, Bind.bind, Except.bind, pure, Except.pure]
    | @annCall x args ts r hid hne hl =>
      have hrem : st.remaining = .ident x :: .lParen :: ts := heq
      obtain ⟨hx, hrem1⟩ := parseIdent_complete hrem
      have hrem1' : st.advance.remaining = .lParen :: ts := by
        obtain ⟨hpos, htok, htail⟩ := state_of_remaining_cons hrem
        exact htail
      obtain ⟨hlp, hrem2⟩ := expectTok_complete (what := "'('") hrem1'
      have hl' : GrSepList GrAnnExpr st.advance.advance.remaining args (.rParen :: rest) := by
        rw [hrem2]; exact hl
      have hfuel' : 2 * st.advance.advance.remaining.length + 4 ≤ fuel := by
        have hlen : st.remaining.length = 2 + st.advance.advance.remaining.length := by
          rw [hrem2, hrem]
          simp only [List.length_cons]
          omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExprList_complete hl' hfuel' hne
      obtain ⟨hrp, hrem₃⟩ := expectTok_complete (what := "')'") hrem₁
      refine ⟨st₁.advance, ?_, hrem₃⟩
      unfold parseAnnExpr
      simp only [peek?_eq_of_remaining_cons hrem, hx, Bind.bind, Except.bind, pure, Except.pure]
      -- the inner peek? is `(`: take the call branch
      have hpeek : st.advance.peek? = some .lParen :=
        peek?_eq_of_remaining_cons hrem1'
      simp only [hpeek, ↓reduceIte, hlp, hparse, hrp]
      -- the identifier does not start with `_` (it is a predicate identifier)
      have hnx : ¬ (⟨x⟩ : Ident).name.startsWith "_" := by
        rw [IsPredIdent] at hid
        simpa using hid
      simp only [hnx, ↓reduceIte]
      simp
    | @array ts es r hl =>
      have hrem : st.remaining = .lBrack :: ts := heq
      obtain ⟨hlb, hrem1⟩ := expectTok_complete (what := "'['") hrem
      have hl' : GrSepList GrAnnExpr st.advance.remaining es (.rBrack :: rest) := by
        rw [hrem1]; exact hl
      have hfuel' : 2 * st.advance.remaining.length + 4 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExprArrayContents_complete hl' hfuel'
      obtain ⟨hrb, hrem2⟩ := expectTok_complete (what := "']'") hrem₁
      refine ⟨st₁.advance, ?_, hrem2⟩
      unfold parseAnnExpr
      simp only [peek?_eq_of_remaining_cons hrem, hlb, hparse, hrb, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the non-empty annotation-expression list parser
    (arguments of an annotation call, ending at `)`).  The list is non-empty
    by the grammar (`args ≠ []` in `GrAnnExpr.annCall`), so the `nil` case
    of the separated list is refuted by `hne`. -/
theorem parseAnnExprList_complete {fuel st elems rest}
    (h : GrSepList GrAnnExpr st.remaining elems (.rParen :: rest))
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel)
    (hne : elems ≠ []) :
    ∃ st', parseAnnExprList fuel st = .ok (elems, st') ∧ st'.remaining = .rParen :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil => exact absurd rfl hne
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      -- the element's rest ts₂ is followed by `,` or `)`: never `..` or `(`
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have hnp : ∀ r, ts₂ ≠ .lParen :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrAnnExpr st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 3 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExpr_complete h₁' hfuel' hnd hnp
      have h₂' : GrSepListTail GrAnnExpr st₁.remaining xs (.rParen :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ :=
        parseAnnExprListTail_complete h₂' hfuel''
          (fun r hr => by simp at hr) (fun r hr => by simp at hr) (fun r hr => by simp at hr)
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseAnnExprList
      simp only [hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]

/-- Completeness of the `"," ann-expr` continuation.  The boundary `bnd` is
    the token list at which the list ends; it must not start with a comma
    (otherwise the parser would continue), nor with `..` or `(` (so that the
    preceding element cannot be misread as a range or a call). -/
theorem parseAnnExprListTail_complete {fuel st elems bnd}
    (h : GrSepListTail GrAnnExpr st.remaining elems bnd)
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel)
    (hnc : ∀ r, bnd ≠ .comma :: r)
    (hnd : ∀ r, bnd ≠ .dotDot :: r)
    (hnp : ∀ r, bnd ≠ .lParen :: r) :
    ∃ st', parseAnnExprListTail fuel st = .ok (elems, st') ∧ st'.remaining = bnd := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseAnnExprListTail
      have hpeek : st.peek? ≠ some .comma :=
        peek?_ne_of_remaining_ne (fun r hr => hnc r (by rw [heq] at hr; exact hr))
      cases hp : st.peek? with
      | none => rfl
      | some t =>
        cases t with
        | comma => exact absurd hp hpeek
        | _ => rfl
    | @cons ts₁ x ts₂ xs rst h₁ h₂ =>
      have hrem : st.remaining = .comma :: ts₁ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      have hnd' : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; exact hnd r hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have hnp' : ∀ r, ts₂ ≠ .lParen :: r := by
        cases h₂ with
        | nil => intro r hr; exact hnp r hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrAnnExpr st.advance.remaining x ts₂ := by
        rw [hremc]; exact h₁
      have hfuel' : 2 * st.advance.remaining.length + 3 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st.advance.remaining.length = ts₁.length := by rw [hremc]
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExpr_complete h₁' hfuel' hnd' hnp'
      have h₂' : GrSepListTail GrAnnExpr st₁.remaining xs bnd := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseAnnExprListTail_complete h₂' hfuel'' hnc hnd hnp
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseAnnExprListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the annotation-array-contents parser (ending at `]`). -/
theorem parseAnnExprArrayContents_complete {fuel st elems rest}
    (h : GrSepList GrAnnExpr st.remaining elems (.rBrack :: rest))
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel) :
    ∃ st', parseAnnExprArrayContents fuel st = .ok (elems, st') ∧ st'.remaining = .rBrack :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseAnnExprArrayContents
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have hnp : ∀ r, ts₂ ≠ .lParen :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrAnnExpr st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 3 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExpr_complete h₁' hfuel' hnd hnp
      have h₂' : GrSepListTail GrAnnExpr st₁.remaining xs (.rBrack :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ :=
        parseAnnExprListTail_complete h₂' hfuel''
          (fun r hr => by simp at hr) (fun r hr => by simp at hr) (fun r hr => by simp at hr)
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseAnnExprArrayContents
      -- the head is an ann-expr token, not `]`
      obtain ⟨t, r, hrem, hne⟩ := GrAnnExpr.head_not_rBrack h₁
      have hpeek := peek?_eq_of_remaining_cons (by rw [heq]; exact hrem)
      cases t with
      | rBrack =>
        exfalso
        have h₁'' : GrAnnExpr (.rBrack :: r) x ts₂ := hrem ▸ h₁
        cases h₁'' with
        | @lit l ts r hl => cases hl
      | _ =>
        simp only [hpeek, hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]
end

/-- Completeness of the annotation parser.  The hypothesis `hnp` rules out
    the call reading of a plain identifier. -/
theorem parseAnnotation_complete {fuel st a rest}
    (h : GrAnnotation st.remaining a rest)
    (hfuel : 2 * st.remaining.length + 5 ≤ fuel)
    (hnp : ∀ r, rest ≠ .lParen :: r) :
    ∃ st', parseAnnotation fuel st = .ok (a, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @ident x r hid =>
      have hrem : st.remaining = .ident x :: rest := heq
      obtain ⟨hx, hrem1⟩ := parsePredIdent_complete hrem hid
      refine ⟨st.advance, ?_, hrem1⟩
      unfold parseAnnotation
      simp only [peek?_eq_of_remaining_cons hrem, hx, Bind.bind, Except.bind, pure, Except.pure]
      have hpeek : st.advance.peek? ≠ some .lParen :=
        peek?_ne_of_remaining_ne (fun r hr => hnp r (by rw [hrem1] at hr; exact hr))
      cases hp : st.advance.peek? with
      | none => rfl
      | some t =>
        cases t with
        | lParen => exact absurd hp hpeek
        | _ => rfl
    | @call x args ts r hid hne hl =>
      have hrem : st.remaining = .ident x :: .lParen :: ts := heq
      obtain ⟨hx, hrem1⟩ := parsePredIdent_complete hrem hid
      have hrem1' : st.advance.remaining = .lParen :: ts := by
        obtain ⟨hpos, htok, htail⟩ := state_of_remaining_cons hrem
        exact htail
      obtain ⟨hlp, hrem2⟩ := expectTok_complete (what := "'('") hrem1'
      have hl' : GrSepList GrAnnExpr st.advance.advance.remaining args (.rParen :: rest) := by
        rw [hrem2]; exact hl
      have hfuel' : 2 * st.advance.advance.remaining.length + 4 ≤ fuel := by
        have hlen : st.remaining.length = 2 + st.advance.advance.remaining.length := by
          rw [hrem2, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnExprList_complete hl' hfuel' hne
      obtain ⟨hrp, hrem₃⟩ := expectTok_complete (what := "')'") hrem₁
      refine ⟨st₁.advance, ?_, hrem₃⟩
      unfold parseAnnotation
      simp only [peek?_eq_of_remaining_cons hrem, hx, Bind.bind, Except.bind, pure, Except.pure]
      have hpeek : st.advance.peek? = some .lParen :=
        peek?_eq_of_remaining_cons hrem1'
      simp only [hpeek, ↓reduceIte, hlp, hparse, hrp]

/-- Completeness of the annotations parser.  The hypotheses rule out the
    cons reading of an empty annotation list (`hnc`) and the call reading of
    a trailing plain identifier (`hnp`). -/
theorem parseAnnotations_complete {fuel st as rest}
    (h : GrAnnotations st.remaining as rest)
    (hfuel : 2 * st.remaining.length + 6 ≤ fuel)
    (hnc : ∀ r, rest ≠ .colonColon :: r)
    (hnp : ∀ r, rest ≠ .lParen :: r) :
    ∃ st', parseAnnotations fuel st = .ok (as, st') ∧ st'.remaining = rest := by
  -- length-bound induction (GrAnnotations is a member of a mutual block and
  -- recurses only on itself); the fuel is universally quantified so that the
  -- induction hypothesis applies at the smaller fuel of the recursive call
  have key : ∀ (m : Nat) (st : State) (as : List Annotation) (rest : List Token),
      st.remaining.length ≤ m → GrAnnotations st.remaining as rest →
      (∀ r, rest ≠ .colonColon :: r) → (∀ r, rest ≠ .lParen :: r) →
      ∀ f, 2 * st.remaining.length + 6 ≤ f →
      ∃ st', parseAnnotations f st = .ok (as, st') ∧ st'.remaining = rest := by
    intro m
    induction m with
    | zero =>
      intro st as rest hlen h hnc' hnp' f hfuel'
      generalize heq : st.remaining = toks at h
      cases h with
      | nil =>
        refine ⟨st, ?_, heq⟩
        cases f with
        | zero => omega
        | succ f =>
          unfold parseAnnotations
          have hpeek : st.peek? ≠ some .colonColon :=
            peek?_ne_of_remaining_ne (fun r hr => hnc' r (by rw [heq] at hr; exact hr))
          cases hp : st.peek? with
          | none => rfl
          | some t =>
            cases t with
            | colonColon => exact absurd hp hpeek
            | _ => rfl
      | @cons ts₁ a ts₂ as ts₃ h₁ h₂ =>
        exfalso
        have hrem : st.remaining = .colonColon :: ts₁ := heq
        rw [hrem] at hlen
        simp only [List.length_cons] at hlen
        omega
    | succ m ih =>
      intro st as rest hlen h hnc' hnp' f hfuel'
      generalize heq : st.remaining = toks at h
      cases h with
      | nil =>
        refine ⟨st, ?_, heq⟩
        cases f with
        | zero => omega
        | succ f =>
          unfold parseAnnotations
          have hpeek : st.peek? ≠ some .colonColon :=
            peek?_ne_of_remaining_ne (fun r hr => hnc' r (by rw [heq] at hr; exact hr))
          cases hp : st.peek? with
          | none => rfl
          | some t =>
            cases t with
            | colonColon => exact absurd hp hpeek
            | _ => rfl
      | @cons ts₁ a ts₂ as ts₃ h₁ h₂ =>
        cases f with
        | zero => omega
        | succ f =>
          have hrem : st.remaining = .colonColon :: ts₁ := heq
          obtain ⟨hcc, hremc⟩ := expectTok_complete (what := "'::'") hrem
          -- the annotation's rest ts₂ is where the remaining annotations start:
          -- either `.colonColon :: ...` (more) or `rest` (end) — never `.lParen :: r`
          have hnp'' : ∀ r, ts₂ ≠ .lParen :: r := by
            cases h₂ with
            | nil => intro r hr; exact hnp' r hr
            | @cons ts₁' a' ts₂' as' ts₃' h₁' h₂' => intro r hr; simp at hr
          have hfuel'' : 2 * st.advance.remaining.length + 5 ≤ f := by
            have hlen' : st.remaining.length = 1 + st.advance.remaining.length := by
              rw [hremc, hrem]; simp only [List.length_cons]; omega
            have h2 := hfuel'
            rw [hlen'] at h2
            omega
          have h₁' : GrAnnotation st.advance.remaining a ts₂ := by
            rw [hremc]; exact h₁
          obtain ⟨st₁, hparse, hrem₁⟩ := parseAnnotation_complete h₁' hfuel'' hnp''
          have h₂' : GrAnnotations st₁.remaining as rest := by rw [hrem₁]; exact h₂
          have hbound : st₁.remaining.length ≤ m := by
            have hcp := h₁.consumes_pos
            have hlen' : st.remaining.length = 1 + ts₁.length := by
              rw [hrem]; simp only [List.length_cons]; omega
            have hlen'' : st₁.remaining.length = ts₂.length := by rw [hrem₁]
            omega
          have hfuel₃ : 2 * st₁.remaining.length + 6 ≤ f := by
            have hcp := h₁.consumes_pos
            have hlen' : st.remaining.length = 1 + ts₁.length := by
              rw [hrem]; simp only [List.length_cons]; omega
            have hlen'' : st₁.remaining.length = ts₂.length := by rw [hrem₁]
            omega
          have hnc'' : ∀ r, rest ≠ .colonColon :: r := hnc'
          obtain ⟨st₂, hparse₂, hrem₂⟩ := ih st₁ as rest hbound h₂' hnc'' hnp' f hfuel₃
          refine ⟨st₂, ?_, hrem₂⟩
          unfold parseAnnotations
          simp only [peek?_eq_of_remaining_cons hrem, hcc, hparse, hparse₂, Bind.bind,
            Except.bind, pure, Except.pure]
  exact key st.remaining.length st as rest (Nat.le_refl _) h hnc hnp fuel hfuel

/-! ## Completeness of the type parsers -/

/-- Completeness of the basic-var-type parser. -/
theorem parseBasicVarType_complete {fuel st t rest}
    (h : GrBasicVarType st.remaining t rest)
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parseBasicVarType fuel st = .ok (t, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @parBool r =>
      have hrem : st.remaining = .kwVar :: .kwBool :: rest := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hb, hrem2⟩ := expectTok_complete (what := "'bool'") hrem1
      refine ⟨st.advance.advance, ?_, hrem2⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hb, Bind.bind, Except.bind,
        pure, Except.pure]
    | @parInt r =>
      have hrem : st.remaining = .kwVar :: .kwInt :: rest := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hb, hrem2⟩ := expectTok_complete (what := "'int'") hrem1
      refine ⟨st.advance.advance, ?_, hrem2⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hb, Bind.bind, Except.bind,
        pure, Except.pure]
    | @parSetOfInt r =>
      have hrem : st.remaining = .kwVar :: .kwSet :: .kwOf :: .kwInt :: rest := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hs, hrem2⟩ := expectTok_complete (what := "'set'") hrem1
      obtain ⟨ho, hrem3⟩ := expectTok_complete (what := "'of'") hrem2
      obtain ⟨hi, hrem4⟩ := expectTok_complete (what := "'int'") hrem3
      refine ⟨st.advance.advance.advance.advance, ?_, hrem4⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hs, peek?_eq_of_remaining_cons hrem2,
        ho, peek?_eq_of_remaining_cons hrem3, hi, Bind.bind, Except.bind,
        pure, Except.pure]
    | @intRange lo hi r =>
      have hrem : st.remaining = .kwVar :: .intLit lo :: .dotDot :: .intLit hi :: rest := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hr, hrem4⟩ := parseIntRange_complete hrem1
      refine ⟨st.advance.advance.advance.advance, ?_, hrem4⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hr, Bind.bind, Except.bind,
        pure, Except.pure]
    | @intSet es ts r hne hl =>
      have hrem : st.remaining = .kwVar :: .lBrace :: ts := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hb, hrem2⟩ := expectTok_complete (what := "'{'") hrem1
      have hl' : GrSepList GrIntAtom st.advance.advance.remaining es (.rBrace :: rest) := by
        rw [hrem2]; exact hl
      have hfuel' : 2 * st.advance.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 2 + st.advance.advance.remaining.length := by
          rw [hrem2, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseNonemptyIntList_complete hl' hfuel' hne
      obtain ⟨hbr', hrem3⟩ := expectTok_complete (what := "'}'") hrem₁
      refine ⟨st₁.advance, ?_, hrem3⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hb, hparse, hbr', Bind.bind,
        Except.bind, pure, Except.pure]
    | @setOfIntRange lo hi r =>
      have hrem : st.remaining =
          .kwVar :: .kwSet :: .kwOf :: .intLit lo :: .dotDot :: .intLit hi :: rest := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hs, hrem2⟩ := expectTok_complete (what := "'set'") hrem1
      obtain ⟨ho, hrem3⟩ := expectTok_complete (what := "'of'") hrem2
      obtain ⟨hr, hrem6⟩ := parseIntRange_complete hrem3
      refine ⟨st.advance.advance.advance.advance.advance.advance, ?_, hrem6⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hs, peek?_eq_of_remaining_cons hrem2,
        ho, peek?_eq_of_remaining_cons hrem3, hr, Bind.bind, Except.bind,
        pure, Except.pure]
    | @setOfIntSet es ts r hl =>
      have hrem : st.remaining = .kwVar :: .kwSet :: .kwOf :: .lBrace :: es := heq
      obtain ⟨hv, hrem1⟩ := expectTok_complete (what := "'var'") hrem
      obtain ⟨hs, hrem2⟩ := expectTok_complete (what := "'set'") hrem1
      obtain ⟨ho, hrem3⟩ := expectTok_complete (what := "'of'") hrem2
      obtain ⟨hb, hrem4⟩ := expectTok_complete (what := "'{'") hrem3
      have hl' : GrSepList GrIntAtom st.advance.advance.advance.advance.remaining ts (.rBrace :: rest) := by
        rw [hrem4]; exact hl
      have hfuel' : 2 * st.advance.advance.advance.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 4 + st.advance.advance.advance.advance.remaining.length := by
          rw [hrem4, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntList_complete hl' hfuel'
      obtain ⟨hbr', hrem5⟩ := expectTok_complete (what := "'}'") hrem₁
      refine ⟨st₁.advance, ?_, hrem5⟩
      unfold parseBasicVarType
      simp only [hv, peek?_eq_of_remaining_cons hrem1, hs, peek?_eq_of_remaining_cons hrem2,
        ho, peek?_eq_of_remaining_cons hrem3, hb, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the basic-pred-param-type parser. -/
theorem parseBasicPredParamType_complete {fuel st t rest}
    (h : GrBasicPredParamType st.remaining t rest)
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel) :
    ∃ st', parseBasicPredParamType fuel st = .ok (t, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @par ts p r hp =>
      -- the parser handles basic par types inline (bool/int/set branches)
      cases hp with
      | bool =>
        have hrem : st.remaining = .kwBool :: rest := heq
        obtain ⟨hb, hrem1⟩ := expectTok_complete (what := "'bool'") hrem
        refine ⟨st.advance, ?_, hrem1⟩
        unfold parseBasicPredParamType
        simp only [peek?_eq_of_remaining_cons hrem, hb, Bind.bind, Except.bind,
          pure, Except.pure]
      | int =>
        have hrem : st.remaining = .kwInt :: rest := heq
        obtain ⟨hb, hrem1⟩ := expectTok_complete (what := "'int'") hrem
        refine ⟨st.advance, ?_, hrem1⟩
        unfold parseBasicPredParamType
        simp only [peek?_eq_of_remaining_cons hrem, hb, Bind.bind, Except.bind,
          pure, Except.pure]
      | setOfInt =>
        have hrem : st.remaining = .kwSet :: .kwOf :: .kwInt :: rest := heq
        obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'set'") hrem
        obtain ⟨ho, hrem2⟩ := expectTok_complete (what := "'of'") hrem1
        obtain ⟨hi, hrem3⟩ := expectTok_complete (what := "'int'") hrem2
        refine ⟨st.advance.advance.advance, ?_, hrem3⟩
        unfold parseBasicPredParamType
        simp only [peek?_eq_of_remaining_cons hrem, hs, peek?_eq_of_remaining_cons hrem1,
          ho, peek?_eq_of_remaining_cons hrem2, hi, Bind.bind, Except.bind,
          pure, Except.pure]
    | @var ts v r hv =>
      have hv' : GrBasicVarType st.remaining v rest := by rw [heq]; exact hv
      have hfuel' : 2 * st.remaining.length + 1 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicVarType_complete hv' hfuel'
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parseBasicPredParamType
      -- the head is `var`: take the var branch
      have hpeek : st.peek? = some .kwVar := by
        cases hv with
        | @parBool r => exact peek?_eq_of_remaining_cons heq
        | @parInt r => exact peek?_eq_of_remaining_cons heq
        | @parSetOfInt r => exact peek?_eq_of_remaining_cons heq
        | @intRange lo hi r => exact peek?_eq_of_remaining_cons heq
        | @intSet es ts r hne hl => exact peek?_eq_of_remaining_cons heq
        | @setOfIntRange lo hi r => exact peek?_eq_of_remaining_cons heq
        | @setOfIntSet es ts r hl => exact peek?_eq_of_remaining_cons heq
      simp only [hpeek, hparse, Bind.bind, Except.bind, pure, Except.pure]
    | @intRange lo hi r =>
      have hrem : st.remaining = .intLit lo :: .dotDot :: .intLit hi :: rest := heq
      obtain ⟨hr, hrem3⟩ := parseIntRange_complete hrem
      refine ⟨st.advance.advance.advance, ?_, hrem3⟩
      unfold parseBasicPredParamType
      simp only [peek?_eq_of_remaining_cons hrem, hr, Bind.bind, Except.bind,
        pure, Except.pure]
    | @intSet es ts r hne hl =>
      have hrem : st.remaining = .lBrace :: ts := heq
      obtain ⟨hb, hrem1⟩ := expectTok_complete (what := "'{'") hrem
      have hl' : GrSepList GrIntAtom st.advance.remaining es (.rBrace :: rest) := by
        rw [hrem1]; exact hl
      have hfuel' : 2 * st.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseNonemptyIntList_complete hl' hfuel' hne
      obtain ⟨hbr', hrem2⟩ := expectTok_complete (what := "'}'") hrem₁
      refine ⟨st₁.advance, ?_, hrem2⟩
      unfold parseBasicPredParamType
      simp only [peek?_eq_of_remaining_cons hrem, hb, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]
    | @setOfIntRange lo hi r =>
      have hrem : st.remaining = .kwSet :: .kwOf :: .intLit lo :: .dotDot :: .intLit hi :: rest := heq
      obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'set'") hrem
      obtain ⟨ho, hrem2⟩ := expectTok_complete (what := "'of'") hrem1
      obtain ⟨hr, hrem5⟩ := parseIntRange_complete hrem2
      refine ⟨st.advance.advance.advance.advance.advance, ?_, hrem5⟩
      unfold parseBasicPredParamType
      simp only [peek?_eq_of_remaining_cons hrem, hs, peek?_eq_of_remaining_cons hrem1,
        ho, peek?_eq_of_remaining_cons hrem2, hr, Bind.bind, Except.bind,
        pure, Except.pure]
    | @setOfIntSet es ts r hl =>
      have hrem : st.remaining = .kwSet :: .kwOf :: .lBrace :: es := heq
      obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'set'") hrem
      obtain ⟨ho, hrem2⟩ := expectTok_complete (what := "'of'") hrem1
      obtain ⟨hb, hrem3⟩ := expectTok_complete (what := "'{'") hrem2
      have hl' : GrSepList GrIntAtom st.advance.advance.advance.remaining ts (.rBrace :: rest) := by
        rw [hrem3]; exact hl
      have hfuel' : 2 * st.advance.advance.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 3 + st.advance.advance.advance.remaining.length := by
          rw [hrem3, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseIntList_complete hl' hfuel'
      obtain ⟨hbr', hrem4⟩ := expectTok_complete (what := "'}'") hrem₁
      refine ⟨st₁.advance, ?_, hrem4⟩
      unfold parseBasicPredParamType
      simp only [peek?_eq_of_remaining_cons hrem, hs, peek?_eq_of_remaining_cons hrem1,
        ho, peek?_eq_of_remaining_cons hrem2, hb, hparse, hbr', Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the pred-param-type parser. -/
theorem parsePredParamType_complete {fuel st t rest}
    (h : GrPredParamType st.remaining t rest)
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel) :
    ∃ st', parsePredParamType fuel st = .ok (t, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @basic ts b r hb =>
      have hb' : GrBasicPredParamType st.remaining b rest := by rw [heq]; exact hb
      have hfuel' : 2 * st.remaining.length + 2 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicPredParamType_complete hb' hfuel'
      refine ⟨st₁, ?_, hrem₁⟩
      unfold parsePredParamType
      -- the head is not `array`: catch-all branch
      have hpeek : st.peek? ≠ some .kwArray := by
        intro hcon
        cases hb with
        | @par ts p r hp =>
          cases hp with
          | bool => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
          | int => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
          | setOfInt => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @var ts v r hv =>
          have hk : st.peek? = some .kwVar := by
            cases hv with
            | @parBool r => exact peek?_eq_of_remaining_cons heq
            | @parInt r => exact peek?_eq_of_remaining_cons heq
            | @parSetOfInt r => exact peek?_eq_of_remaining_cons heq
            | @intRange lo hi r => exact peek?_eq_of_remaining_cons heq
            | @intSet es ts r hne hl => exact peek?_eq_of_remaining_cons heq
            | @setOfIntRange lo hi r => exact peek?_eq_of_remaining_cons heq
            | @setOfIntSet es ts r hl => exact peek?_eq_of_remaining_cons heq
          rw [hk] at hcon; simp at hcon
        | @intRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @intSet es ts r hne hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntSet es ts r hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
      cases hp : st.peek? with
      | none => simp only [hparse, Bind.bind, Except.bind, pure, Except.pure]
      | some t =>
        cases t with
        | kwArray => exact absurd hp hpeek
        | _ => simp only [hparse, Bind.bind, Except.bind, pure, Except.pure]
    | @array ts₁ i ts₂ el r hi hb =>
      -- the index set consumes at least 3 tokens: `int` or `1 .. n`
      have hcp : 3 ≤ ts₁.length - ts₂.length := by
        cases hi with
        | int =>
            simp only [List.length_cons]; omega
        | @range ts i r hidx =>
            have hts : ∃ n, ts₁ = .intLit 1 :: .dotDot :: .intLit n :: .rBrack :: .kwOf :: ts₂ := by
              cases hidx with
              | @mk hi r => exact ⟨hi, rfl⟩
            obtain ⟨n, hts⟩ := hts
            rw [hts]; simp only [List.length_cons]; omega
      have hrem : st.remaining = .kwArray :: .lBrack :: ts₁ := heq
      obtain ⟨ha, hrem1⟩ := expectTok_complete (what := "'array'") hrem
      obtain ⟨hlb, hrem2⟩ := expectTok_complete (what := "'['") hrem1
      have hi' : GrPredIndexSet st.advance.advance.remaining i (.rBrack :: .kwOf :: ts₂) := by
        rw [hrem2]; exact hi
      obtain ⟨st₁, hidx, hrem₃⟩ := parsePredIndexSet_complete hi'
      obtain ⟨hrb, hrem4⟩ := expectTok_complete (what := "']'") hrem₃
      obtain ⟨hof, hrem5⟩ := expectTok_complete (what := "'of'") hrem4
      have hb' : GrBasicPredParamType st₁.advance.advance.remaining el rest := by
        rw [hrem5]; exact hb
      have hfuel' : 2 * st₁.advance.advance.remaining.length + 2 ≤ fuel := by
        have hlen1 : st.remaining.length = 2 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st₁.advance.advance.remaining.length = ts₂.length := by rw [hrem5]
        omega
      obtain ⟨st₂, hparse, hrem₆⟩ := parseBasicPredParamType_complete hb' hfuel'
      refine ⟨st₂, ?_, hrem₆⟩
      unfold parsePredParamType
      simp only [peek?_eq_of_remaining_cons hrem, ha, peek?_eq_of_remaining_cons hrem1,
        hlb, hidx, hrb, hof, hparse, Bind.bind, Except.bind, pure, Except.pure]

/-- Completeness of the pred-param parser. -/
theorem parsePredParam_complete {fuel st p rest}
    (h : GrPredParam st.remaining p rest)
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel) :
    ∃ st', parsePredParam fuel st = .ok (p, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases h with
    | @mk x t ts r hid ht =>
      have ht' : GrPredParamType st.remaining ts (.colon :: .ident x :: rest) := ht
      have hfuel' : 2 * st.remaining.length + 3 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parsePredParamType_complete ht' hfuel'
      obtain ⟨hc, hrem2⟩ := expectTok_complete (what := "':'") hrem₁
      obtain ⟨hx, hrem3⟩ := parsePredIdent_complete hrem2 hid
      refine ⟨st₁.advance.advance, ?_, hrem3⟩
      unfold parsePredParam
      simp only [hparse, hc, hx, Bind.bind, Except.bind, pure, Except.pure]

/-! ## Completeness of the pred-param-list parsers -/

/-! Completeness of the comma-separated predicate-parameter lists ending at
    `)`.  Mutually recursive (list / tail), as in `FznCorrectness.lean`. -/
mutual
theorem parsePredParamList_complete {fuel st elems rest}
    (h : GrSepList GrPredParam st.remaining elems (.rParen :: .semi :: rest))
    (hfuel : 2 * st.remaining.length + 5 ≤ fuel) :
    ∃ st', parsePredParamList fuel st = .ok (elems, st') ∧ st'.remaining = .rParen :: .semi :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parsePredParamList
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      have h₁' : GrPredParam st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 4 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parsePredParam_complete h₁' hfuel'
      have h₂' : GrSepListTail GrPredParam st₁.remaining xs (.rParen :: .semi :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 3 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parsePredParamListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parsePredParamList
      -- the head is a param token, not `)`
      have hpeek : st.peek? ≠ some .rParen := by
        intro hcon
        have hrem' : ∃ (t : Token) (r : List Token), st.remaining = t :: r ∧ t ≠ .rParen := by
          cases h₁ with
          | @mk x t ts r hid ht =>
            cases ht with
            | @basic ts b r hb =>
              cases hb with
              | @par ts p r hp =>
                cases hp with
                | bool => exact ⟨.kwBool, _, heq, by simp⟩
                | int => exact ⟨.kwInt, _, heq, by simp⟩
                | setOfInt => exact ⟨.kwSet, _, heq, by simp⟩
              | @var ts v r hv =>
                cases hv with
                | @parBool r => exact ⟨.kwVar, _, heq, by simp⟩
                | @parInt r => exact ⟨.kwVar, _, heq, by simp⟩
                | @parSetOfInt r => exact ⟨.kwVar, _, heq, by simp⟩
                | @intRange lo hi r => exact ⟨.kwVar, _, heq, by simp⟩
                | @intSet es ts r hne hl => exact ⟨.kwVar, _, heq, by simp⟩
                | @setOfIntRange lo hi r => exact ⟨.kwVar, _, heq, by simp⟩
                | @setOfIntSet es ts r hl => exact ⟨.kwVar, _, heq, by simp⟩
              | @intRange lo hi r => exact ⟨.intLit lo, _, heq, by simp⟩
              | @intSet es ts r hne hl => exact ⟨.lBrace, _, heq, by simp⟩
              | @setOfIntRange lo hi r => exact ⟨.kwSet, _, heq, by simp⟩
              | @setOfIntSet es ts r hl => exact ⟨.kwSet, _, heq, by simp⟩
            | @array ts₁ i ts₂ el r hi hb => exact ⟨.kwArray, _, heq, by simp⟩
        obtain ⟨t, r, hrem', hne⟩ := hrem'
        rw [peek?_eq_of_remaining_cons hrem'] at hcon
        injection hcon with hcon'
        exact hne hcon'
      cases hp : st.peek? with
      | none => simp only [hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]
      | some t =>
        cases t with
        | rParen => exact absurd hp hpeek
        | _ => simp only [hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]

theorem parsePredParamListTail_complete {fuel st elems rest}
    (h : GrSepListTail GrPredParam st.remaining elems (.rParen :: .semi :: rest))
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel) :
    ∃ st', parsePredParamListTail fuel st = .ok (elems, st') ∧ st'.remaining = .rParen :: .semi :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parsePredParamListTail
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs rst h₁ h₂ =>
      have hrem : st.remaining = .comma :: ts₁ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      have h₁' : GrPredParam st.advance.remaining x ts₂ := by
        rw [hremc]; exact h₁
      have hfuel' : 2 * st.advance.remaining.length + 4 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st.advance.remaining.length = ts₁.length := by rw [hremc]
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parsePredParam_complete h₁' hfuel'
      have h₂' : GrSepListTail GrPredParam st₁.remaining xs (.rParen :: .semi :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 3 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parsePredParamListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parsePredParamListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]
end

/-! ## Completeness of the expression-list parsers (constraint arguments) -/

/-! Completeness of the comma-separated expression lists ending at `)`. -/
mutual
theorem parseExprList_complete {fuel st elems rest}
    (h : GrSepList GrExpr st.remaining elems (.rParen :: rest))
    (hfuel : 2 * st.remaining.length + 6 ≤ fuel) :
    ∃ st', parseExprList fuel st = .ok (elems, st') ∧ st'.remaining = .rParen :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseExprList
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs ts₃ h₁ h₂ =>
      -- the element's rest ts₂ is followed by `,` or `)`: never `..`
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrExpr st.remaining x ts₂ := by rw [heq]; exact h₁
      have hfuel' : 2 * st.remaining.length + 5 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseExpr_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrExpr st₁.remaining xs (.rParen :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 4 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseExprListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseExprList
      -- the head is an expr token, not `)`
      have hpeek : st.peek? ≠ some .rParen := by
        intro hcon
        have hrem' : ∃ (t : Token) (r : List Token), st.remaining = t :: r ∧ t ≠ .rParen := by
          cases h₁ with
          | @basic b ts r hb =>
            cases hb with
            | @lit l ts r hl =>
              cases hl with
              | bool => rename_i b; exact ⟨.boolLit b, _, heq, by simp⟩
              | int => rename_i i; exact ⟨.intLit i, _, heq, by simp⟩
              | intRange => rename_i lo hi; exact ⟨.intLit lo, _, heq, by simp⟩
              | intSet => rename_i ts es hl; exact ⟨.lBrace, _, heq, by simp⟩
            | ident => rename_i x; exact ⟨.ident x, _, heq, by simp⟩
          | @array ts es r hl => exact ⟨.lBrack, _, heq, by simp⟩
        obtain ⟨t, r, hrem', hne⟩ := hrem'
        rw [peek?_eq_of_remaining_cons hrem'] at hcon
        injection hcon with hcon'
        exact hne hcon'
      cases hp : st.peek? with
      | none => simp only [hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]
      | some t =>
        cases t with
        | rParen => exact absurd hp hpeek
        | _ => simp only [hparse, hparse₂, Bind.bind, Except.bind, pure, Except.pure]

theorem parseExprListTail_complete {fuel st elems rest}
    (h : GrSepListTail GrExpr st.remaining elems (.rParen :: rest))
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel) :
    ∃ st', parseExprListTail fuel st = .ok (elems, st') ∧ st'.remaining = .rParen :: rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | nil =>
      refine ⟨st, ?_, heq⟩
      unfold parseExprListTail
      simp only [peek?_eq_of_remaining_cons heq, pure, Except.pure]
    | @cons ts₁ x ts₂ xs rst h₁ h₂ =>
      have hrem : st.remaining = .comma :: ts₁ := heq
      obtain ⟨hc, hremc⟩ := expectTok_complete (what := "','") hrem
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        cases h₂ with
        | nil => intro r hr; simp at hr
        | @cons ts₁' x' ts₂' xs' r'' h₁' h₂' => intro r hr; simp at hr
      have h₁' : GrExpr st.advance.remaining x ts₂ := by
        rw [hremc]; exact h₁
      have hfuel' : 2 * st.advance.remaining.length + 5 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        have hlen2 : st.advance.remaining.length = ts₁.length := by rw [hremc]
        omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseExpr_complete h₁' hfuel' hnd
      have h₂' : GrSepListTail GrExpr st₁.remaining xs (.rParen :: rest) := by
        rw [hrem₁]; exact h₂
      have hfuel'' : 2 * st₁.remaining.length + 4 ≤ fuel := by
        have hge : 1 ≤ ts₁.length - ts₂.length := h₁.consumes_pos
        have hlen2 : st₁.remaining.length = ts₂.length := by rw [hrem₁]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := parseExprListTail_complete h₂' hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseExprListTail
      simp only [peek?_eq_of_remaining_cons hrem, hc, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]
end

/-! ## Completeness of the item parsers -/

/-- Completeness of the predicate-item parser. -/
theorem parsePredicateItem_complete {fuel st p rest}
    (h : GrPredicateItem st.remaining p rest)
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parsePredicateItem fuel st = .ok (p, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @mk x ts ps r hid hl =>
      have hrem : st.remaining = .kwPredicate :: .ident x :: .lParen :: ts := heq
      obtain ⟨hp, hrem1⟩ := expectTok_complete (what := "'predicate'") hrem
      obtain ⟨hx, hrem2⟩ := parsePredIdent_complete hrem1 hid
      obtain ⟨hlp, hrem3⟩ := expectTok_complete (what := "'('") hrem2
      have hl' : GrSepList GrPredParam st.advance.advance.advance.remaining ps (.rParen :: .semi :: rest) := by
        rw [hrem3]; exact hl
      have hfuel' : 2 * st.advance.advance.advance.remaining.length + 5 ≤ fuel := by
        have hlen : st.remaining.length = 3 + st.advance.advance.advance.remaining.length := by
          rw [hrem3, hrem]
          simp only [List.length_cons]
          omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₄⟩ := parsePredParamList_complete hl' hfuel'
      obtain ⟨hrp, hrem5⟩ := expectTok_complete (what := "')'") hrem₄
      obtain ⟨hs, hrem6⟩ := expectTok_complete (what := "';'") hrem5
      refine ⟨st₁.advance.advance, ?_, hrem6⟩
      unfold parsePredicateItem
      simp only [peek?_eq_of_remaining_cons hrem, hp, hx, hlp, hparse, hrp, hs, Bind.bind,
        Except.bind, pure, Except.pure]

/-- Completeness of the par-decl-item parser. -/
theorem parseParDeclItem_complete {fuel st d rest}
    (h : GrParDeclItem st.remaining d rest)
    (hfuel : 2 * st.remaining.length + 3 ≤ fuel) :
    ∃ st', parseParDeclItem fuel st = .ok (d, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @basic ts₁ t x ts₂ v r ht hv =>
      -- the head is a basic par type token (bool/int/set): catch-all branch
      have hpeek : st.peek? ≠ some .kwArray := by
        intro hcon
        cases ht with
        | bool => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | int => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | setOfInt => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
      have ht' : GrBasicParType st.remaining t (.colon :: .ident x :: .eq :: ts₂) := by
        rw [heq]; exact ht
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicParType_complete ht'
      obtain ⟨hc, hrem2⟩ := expectTok_complete (what := "':'") hrem₁
      obtain ⟨hx, hrem3⟩ := parseIdent_complete hrem2
      obtain ⟨he, hrem4⟩ := expectTok_complete (what := "'='") hrem3
      -- the literal's rest is followed by `;`: never `..`
      have hnd : ∀ r, ts₂ ≠ .dotDot :: r := by
        intro r hr
        rw [hr] at hv
        cases hv
      have hnd' : ∀ r, (.semi :: rest) ≠ .dotDot :: r := by
        intro r hr; simp at hr
      have hv' : GrBasicLiteral st₁.advance.advance.advance.remaining v (.semi :: rest) := by
        rw [hrem4]; exact hv
      have hfuel'' : 2 * st₁.advance.advance.advance.remaining.length + 2 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := by
          cases ht with
          | bool => simp only [List.length_cons]; omega
          | int => simp only [List.length_cons]; omega
          | setOfInt => simp only [List.length_cons]; omega
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.advance.advance.advance.remaining.length = ts₂.length := by rw [hrem4]
        omega
      obtain ⟨st₂, hparse₂, hrem₅⟩ := parseBasicLiteral_complete hv' hfuel'' hnd'
      obtain ⟨hs, hrem6⟩ := expectTok_complete (what := "';'") hrem₅
      refine ⟨st₂.advance, ?_, hrem6⟩
      unfold parseParDeclItem
      cases hp : st.peek? with
      | none => simp only [hparse, hc, hx, he, hparse₂, hs, Bind.bind, Except.bind, pure, Except.pure]
      | some t =>
        cases t with
        | kwArray => exact absurd hp hpeek
        | _ => simp only [hparse, hc, hx, he, hparse₂, hs, Bind.bind, Except.bind, pure, Except.pure]
    | @array ts₁ i ts₂ t x ts₃ v r hi ht hv =>
      -- the index set consumes exactly 5 tokens (`1 .. n`)
      have hge2 : ts₁.length = 5 + ts₂.length := by
        cases hi with
        | @mk hi r => simp only [List.length_cons]; omega
      have hrem : st.remaining = .kwArray :: .lBrack :: ts₁ := heq
      obtain ⟨ha, hrem1⟩ := expectTok_complete (what := "'array'") hrem
      obtain ⟨hlb, hrem2⟩ := expectTok_complete (what := "'['") hrem1
      have hi' : GrIndexSet st.advance.advance.remaining i (.rBrack :: .kwOf :: ts₂) := by
        rw [hrem2]; exact hi
      obtain ⟨st₁, hidx, hrem₃⟩ := parseIndexSet_complete hi'
      obtain ⟨hrb, hrem4⟩ := expectTok_complete (what := "']'") hrem₃
      obtain ⟨hof, hrem5⟩ := expectTok_complete (what := "'of'") hrem4
      have ht' : GrBasicParType st₁.advance.advance.remaining t
          (.colon :: .ident x :: .eq :: ts₃) := by
        rw [hrem5]; exact ht
      obtain ⟨st₂, hparse, hrem₆⟩ := parseBasicParType_complete ht'
      obtain ⟨hc, hrem7⟩ := expectTok_complete (what := "':'") hrem₆
      obtain ⟨hx, hrem8⟩ := parseIdent_complete hrem7
      obtain ⟨he, hrem9⟩ := expectTok_complete (what := "'='") hrem8
      have hv' : GrParArrayLiteral st₂.advance.advance.advance.remaining v (.semi :: rest) := by
        rw [hrem9]; exact hv
      have hfuel'' : 2 * st₂.advance.advance.advance.remaining.length + 3 ≤ fuel := by
        have hge : 1 ≤ ts₂.length - ts₃.length := by
          cases ht with
          | bool => simp only [List.length_cons]; omega
          | int => simp only [List.length_cons]; omega
          | setOfInt => simp only [List.length_cons]; omega
        have hlen : st.remaining.length = 7 + ts₂.length := by
          rw [hrem]
          simp only [List.length_cons]
          rw [hge2]
          omega
        have hlen2 : st₂.advance.advance.advance.remaining.length = ts₃.length := by rw [hrem9]
        omega
      obtain ⟨st₃, hparse₂, hrem₁₀⟩ := parseParArrayLiteral_complete hv' hfuel''
      obtain ⟨hs, hrem₁₁⟩ := expectTok_complete (what := "';'") hrem₁₀
      refine ⟨st₃.advance, ?_, hrem₁₁⟩
      unfold parseParDeclItem
      simp only [peek?_eq_of_remaining_cons hrem, ha, peek?_eq_of_remaining_cons hrem1,
        hlb, hidx, hrb, hof, hparse, hc, hx, he, hparse₂, hs, Bind.bind, Except.bind,
        pure, Except.pure]

/-- Completeness of the var-decl-item parser. -/
theorem parseVarDeclItem_complete {fuel st d rest}
    (h : GrVarDeclItem st.remaining d rest)
    (hfuel : 2 * st.remaining.length + 7 ≤ fuel) :
    ∃ st', parseVarDeclItem fuel st = .ok (d, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @basicNoAssign ts t x ts₂ a r ht ha =>
      -- the head is `var`: catch-all branch
      have hpeek : st.peek? ≠ some .kwArray := by
        intro hcon
        cases ht with
        | @parBool r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @parInt r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @parSetOfInt r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @intRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @intSet es ts r hne hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntSet es ts r hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
      have ht' : GrBasicVarType st.remaining t (.colon :: .ident x :: ts₂) := by
        rw [heq]; exact ht
      have hfuel' : 2 * st.remaining.length + 1 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicVarType_complete ht' hfuel'
      obtain ⟨hc, hrem2⟩ := expectTok_complete (what := "':'") hrem₁
      obtain ⟨hx, hrem3⟩ := parseIdent_complete hrem2
      -- the annotations' rest is `;`: not `::` and not `(`
      have hnc : ∀ r, (.semi :: rest) ≠ .colonColon :: r := by intro r hr; simp at hr
      have hnp : ∀ r, (.semi :: rest) ≠ .lParen :: r := by intro r hr; simp at hr
      have ha' : GrAnnotations st₁.advance.advance.remaining a (.semi :: rest) := by
        rw [hrem3]; exact ha
      have hfuel'' : 2 * st₁.advance.advance.remaining.length + 6 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := by
          have hc := ht.consumes_pos
          simp only [List.length_cons] at hc
          omega
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.advance.advance.remaining.length = ts₂.length := by rw [hrem3]
        omega
      obtain ⟨st₂, hparse₂, hrem₄⟩ := parseAnnotations_complete ha' hfuel'' hnc hnp
      obtain ⟨hs, hrem5⟩ := expectTok_complete (what := "';'") hrem₄
      refine ⟨st₂.advance, ?_, hrem5⟩
      unfold parseVarDeclItem
      cases hp : st.peek? with
      | none =>
        simp only [hparse, hc, hx, hparse₂, hs, Bind.bind, Except.bind, pure, Except.pure]
        -- the inner peek? after annotations is `;`: not `=`
        have hpeek2 : st₂.peek? ≠ some .eq := by
          intro hcon2
          rw [peek?_eq_of_remaining_cons hrem₄] at hcon2; simp at hcon2
        cases hp2 : st₂.peek? with
        | none => rfl
        | some t =>
          cases t with
          | eq => exact absurd hp2 hpeek2
          | _ => rfl
      | some t =>
        cases t with
        | kwArray => exact absurd hp hpeek
        | _ =>
          simp only [hparse, hc, hx, hparse₂, hs, Bind.bind, Except.bind, pure, Except.pure]
          have hpeek2 : st₂.peek? ≠ some .eq := by
            intro hcon2
            rw [peek?_eq_of_remaining_cons hrem₄] at hcon2; simp at hcon2
          cases hp2 : st₂.peek? with
          | none => rfl
          | some t =>
            cases t with
            | eq => exact absurd hp2 hpeek2
            | _ => rfl
    | @basicAssign ts t x ts₂ a ts₃ v r ht ha hv =>
      have hpeek : st.peek? ≠ some .kwArray := by
        intro hcon
        cases ht with
        | @parBool r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @parInt r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @parSetOfInt r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @intRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @intSet es ts r hne hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntRange lo hi r => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
        | @setOfIntSet es ts r hl => rw [peek?_eq_of_remaining_cons heq] at hcon; simp at hcon
      have ht' : GrBasicVarType st.remaining t (.colon :: .ident x :: ts₂) := by
        rw [heq]; exact ht
      have hfuel' : 2 * st.remaining.length + 1 ≤ fuel := by omega
      obtain ⟨st₁, hparse, hrem₁⟩ := parseBasicVarType_complete ht' hfuel'
      obtain ⟨hc, hrem2⟩ := expectTok_complete (what := "':'") hrem₁
      obtain ⟨hx, hrem3⟩ := parseIdent_complete hrem2
      have hnc : ∀ r, (.eq :: ts₃) ≠ .colonColon :: r := by intro r hr; simp at hr
      have hnp : ∀ r, (.eq :: ts₃) ≠ .lParen :: r := by intro r hr; simp at hr
      have ha' : GrAnnotations st₁.advance.advance.remaining a (.eq :: ts₃) := by
        rw [hrem3]; exact ha
      have hfuel'' : 2 * st₁.advance.advance.remaining.length + 6 ≤ fuel := by
        have hge : 1 ≤ toks.length - ts₂.length := by
          have hc := ht.consumes_pos
          simp only [List.length_cons] at hc
          omega
        have hlen : st.remaining.length = toks.length := by rw [heq]
        have hlen2 : st₁.advance.advance.remaining.length = ts₂.length := by rw [hrem3]
        omega
      obtain ⟨st₂, hparse₂, hrem₄⟩ := parseAnnotations_complete ha' hfuel'' hnc hnp
      obtain ⟨he, hrem5⟩ := expectTok_complete (what := "'='") hrem₄
      -- the basic-expr's rest is `;`: never `..`
      have hnd : ∀ r, ts₃ ≠ .dotDot :: r := by
        intro r hr
        rw [hr] at hv
        cases hv with
        | lit hl => cases hl
      have hnd' : ∀ r, (.semi :: rest) ≠ .dotDot :: r := by intro r hr; simp at hr
      have hv' : GrBasicExpr st₂.advance.remaining v (.semi :: rest) := by
        rw [hrem5]; exact hv
      have hfuel''' : 2 * st₂.advance.remaining.length + 3 ≤ fuel := by
        -- the annotations derivation leaves a suffix of `ts₂` ending at
        -- `.eq :: ts₃`, so `ts₃` is strictly shorter than `ts₂`
        have hge : 1 ≤ ts₂.length - ts₃.length := by
          have hs := ha.suffix
          obtain ⟨pre, hpre⟩ := hs
          rw [hpre]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen2 : st₂.advance.remaining.length = ts₃.length := by rw [hrem5]
        have hge2 : 1 ≤ toks.length - ts₂.length := by
          have hc := ht.consumes_pos
          simp only [List.length_cons] at hc
          omega
        have hlen : st.remaining.length = toks.length := by rw [heq]
        omega
      obtain ⟨st₃, hparse₃, hrem₆⟩ := parseBasicExpr_complete hv' hfuel''' hnd'
      obtain ⟨hs, hrem7⟩ := expectTok_complete (what := "';'") hrem₆
      refine ⟨st₃.advance, ?_, hrem7⟩
      unfold parseVarDeclItem
      cases hp : st.peek? with
      | none =>
        simp only [hparse, hc, hx, hparse₂, he, hparse₃, hs, Bind.bind, Except.bind,
          pure, Except.pure]
        have hpeek2 : st₂.peek? = some .eq := peek?_eq_of_remaining_cons hrem₄
        simp only [hpeek2, ↓reduceIte]
      | some t =>
        cases t with
        | kwArray => exact absurd hp hpeek
        | _ =>
          simp only [hparse, hc, hx, hparse₂, he, hparse₃, hs, Bind.bind, Except.bind,
            pure, Except.pure]
          have hpeek2 : st₂.peek? = some .eq := peek?_eq_of_remaining_cons hrem₄
          simp only [hpeek2, ↓reduceIte]
    | @array ts₁ i ts₂ t x ts₃ a ts₄ es r hi ht ha hl =>
      -- the index set consumes exactly 5 tokens (`1 .. n`)
      have hge2 : ts₁.length = 5 + ts₂.length := by
        cases hi with
        | @mk hi r => simp only [List.length_cons]; omega
      have hrem : st.remaining = .kwArray :: .lBrack :: ts₁ := heq
      obtain ⟨ha', hrem1⟩ := expectTok_complete (what := "'array'") hrem
      obtain ⟨hlb, hrem2⟩ := expectTok_complete (what := "'['") hrem1
      have hi' : GrIndexSet st.advance.advance.remaining i (.rBrack :: .kwOf :: ts₂) := by
        rw [hrem2]; exact hi
      obtain ⟨st₁, hidx, hrem₃⟩ := parseIndexSet_complete hi'
      obtain ⟨hrb, hrem4⟩ := expectTok_complete (what := "']'") hrem₃
      obtain ⟨hof, hrem5⟩ := expectTok_complete (what := "'of'") hrem4
      have ht' : GrBasicVarType st₁.advance.advance.remaining t (.colon :: .ident x :: ts₃) := by
        rw [hrem5]; exact ht
      have hfuel' : 2 * st₁.advance.advance.remaining.length + 1 ≤ fuel := by
        have hlen : st.remaining.length = 7 + st₁.advance.advance.remaining.length := by
          rw [hrem5, hrem]
          simp only [List.length_cons]
          rw [hge2]
          omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₂, hparse, hrem₆⟩ := parseBasicVarType_complete ht' hfuel'
      obtain ⟨hc, hrem7⟩ := expectTok_complete (what := "':'") hrem₆
      obtain ⟨hx, hrem8⟩ := parseIdent_complete hrem7
      have hnc : ∀ r, (.eq :: .lBrack :: ts₄) ≠ .colonColon :: r := by intro r hr; simp at hr
      have hnp : ∀ r, (.eq :: .lBrack :: ts₄) ≠ .lParen :: r := by intro r hr; simp at hr
      have ha'' : GrAnnotations st₂.advance.advance.remaining a (.eq :: .lBrack :: ts₄) := by
        rw [hrem8]; exact ha
      have hfuel'' : 2 * st₂.advance.advance.remaining.length + 6 ≤ fuel := by
        have hge : 1 ≤ ts₂.length - ts₃.length := by
          have hc := ht.consumes_pos
          simp only [List.length_cons] at hc
          omega
        have hlen : st.remaining.length = 7 + ts₂.length := by
          rw [hrem]
          simp only [List.length_cons]
          rw [hge2]
          omega
        have hlen2 : st₂.advance.advance.remaining.length = ts₃.length := by rw [hrem8]
        omega
      obtain ⟨st₃, hparse₂, hrem₉⟩ := parseAnnotations_complete ha'' hfuel'' hnc hnp
      obtain ⟨he, hrem₁₀⟩ := expectTok_complete (what := "'='") hrem₉
      -- the array literal: `[ <basic-expr>, ... ]` up to `;`
      have hvarr : GrExpr st₃.advance.remaining (.array es) (.semi :: rest) := by
        rw [hrem₁₀]; exact GrExpr.array hl
      have hnd : ∀ r, (.semi :: rest) ≠ .dotDot :: r := by intro r hr; simp at hr
      have hfuel''' : 2 * st₃.advance.remaining.length + 4 ≤ fuel := by
        -- the annotations derivation leaves a suffix of `ts₃` ending at
        -- `.eq :: .lBrack :: ts₄`, so `ts₄` is strictly shorter than `ts₃`
        have hge : 1 ≤ ts₃.length - ts₄.length := by
          have hs := ha.suffix
          obtain ⟨pre, hpre⟩ := hs
          rw [hpre]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen2 : st₃.advance.remaining.length = 1 + ts₄.length := by
          rw [hrem₁₀]; simp only [List.length_cons]; omega
        have hge3 : 1 ≤ ts₂.length - ts₃.length := by
          have hc := ht.consumes_pos
          simp only [List.length_cons] at hc
          omega
        have hlen : st.remaining.length = 7 + ts₂.length := by
          rw [hrem]
          simp only [List.length_cons]
          rw [show ts₁.length = 5 + ts₂.length from hge2]
          omega
        omega
      obtain ⟨st₄, hparse₃, hrem₁₂⟩ := parseArrayLiteral_complete hvarr hfuel''' hnd
      obtain ⟨hs, hrem₁₃⟩ := expectTok_complete (what := "';'") hrem₁₂
      refine ⟨st₄.advance, ?_, hrem₁₃⟩
      unfold parseVarDeclItem
      simp only [peek?_eq_of_remaining_cons hrem, ha', peek?_eq_of_remaining_cons hrem1,
        hlb, hidx, hrb, hof, hparse, hc, hx, hparse₂, he, hparse₃, hs, Bind.bind,
        Except.bind, pure, Except.pure]

/-- Completeness of the constraint-item parser. -/
theorem parseConstraintItem_complete {fuel st c rest}
    (h : GrConstraintItem st.remaining c rest)
    (hfuel : 2 * st.remaining.length + 1 ≤ fuel) :
    ∃ st', parseConstraintItem fuel st = .ok (c, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @mk x ts₁ args ts₂ a r hid hl ha =>
      have hrem : st.remaining = .kwConstraint :: .ident x :: .lParen :: ts₁ := heq
      obtain ⟨hc, hrem1⟩ := expectTok_complete (what := "'constraint'") hrem
      obtain ⟨hx, hrem2⟩ := parsePredIdent_complete hrem1 hid
      obtain ⟨hlp, hrem3⟩ := expectTok_complete (what := "'('") hrem2
      have hl' : GrSepList GrExpr st.advance.advance.advance.remaining args (.rParen :: ts₂) := by
        rw [hrem3]; exact hl
      have hfuel' : 2 * st.advance.advance.advance.remaining.length + 6 ≤ fuel := by
        have hlen : st.remaining.length = 3 + st.advance.advance.advance.remaining.length := by
          rw [hrem3, hrem]
          simp only [List.length_cons]
          omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₄⟩ := parseExprList_complete hl' hfuel'
      obtain ⟨hrp, hrem5⟩ := expectTok_complete (what := "')'") hrem₄
      -- the annotations' rest is `;`: not `::` and not `(`
      have hnc : ∀ r, (.semi :: rest) ≠ .colonColon :: r := by intro r hr; simp at hr
      have hnp : ∀ r, (.semi :: rest) ≠ .lParen :: r := by intro r hr; simp at hr
      have ha' : GrAnnotations st₁.advance.remaining a (.semi :: rest) := by
        rw [hrem5]; exact ha
      have hfuel'' : 2 * st₁.advance.remaining.length + 6 ≤ fuel := by
        -- the argument list leaves a suffix of `ts₁` ending at `.rParen :: ts₂`
        have hge : 1 ≤ ts₁.length - ts₂.length := by
          have hs := hl.suffix GrExpr.suffix
          obtain ⟨pre, hpre⟩ := hs
          rw [hpre]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen2 : st₁.advance.remaining.length = ts₂.length := by rw [hrem5]
        have hlen : st.remaining.length = 3 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₆⟩ := parseAnnotations_complete ha' hfuel'' hnc hnp
      obtain ⟨hs, hrem7⟩ := expectTok_complete (what := "';'") hrem₆
      refine ⟨st₂.advance, ?_, hrem7⟩
      unfold parseConstraintItem
      simp only [peek?_eq_of_remaining_cons hrem, hc, hx, hlp, hparse, hrp, hparse₂, hs,
        Bind.bind, Except.bind, pure, Except.pure]

/-- Completeness of the solve-item parser. -/
theorem parseSolveItem_complete {fuel st si rest}
    (h : GrSolveItem st.remaining si rest)
    (hfuel : 2 * st.remaining.length + 5 ≤ fuel) :
    ∃ st', parseSolveItem fuel st = .ok (si, st') ∧ st'.remaining = rest := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    generalize heq : st.remaining = toks at h
    cases h with
    | @satisfy ts a r ha =>
      have hrem : st.remaining = .kwSolve :: ts := heq
      obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'solve'") hrem
      -- the annotations' rest is `satisfy ;`: not `::` and not `(`
      have hnc : ∀ r, (.kwSatisfy :: .semi :: rest) ≠ .colonColon :: r := by
        intro r hr; simp at hr
      have hnp : ∀ r, (.kwSatisfy :: .semi :: rest) ≠ .lParen :: r := by
        intro r hr; simp at hr
      have ha' : GrAnnotations st.advance.remaining a (.kwSatisfy :: .semi :: rest) := by
        rw [hrem1]; exact ha
      have hfuel' : 2 * st.advance.remaining.length + 6 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₂⟩ := parseAnnotations_complete ha' hfuel' hnc hnp
      obtain ⟨hsat, hrem₃⟩ := expectTok_complete (what := "'satisfy'") hrem₂
      obtain ⟨hsemi, hrem₄⟩ := expectTok_complete (what := "';'") hrem₃
      refine ⟨st₁.advance.advance, ?_, hrem₄⟩
      unfold parseSolveItem
      simp only [peek?_eq_of_remaining_cons hrem, hs, hparse, Bind.bind, Except.bind,
        pure, Except.pure]
      have hpeek : st₁.peek? = some .kwSatisfy := peek?_eq_of_remaining_cons hrem₂
      simp only [hpeek, ↓reduceIte, hsat, hsemi]
    | @minimize ts₁ a ts₂ e r ha he =>
      have hrem : st.remaining = .kwSolve :: ts₁ := heq
      obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'solve'") hrem
      -- the annotations' rest is `minimize ...`: not `::` and not `(`
      have hnc : ∀ r, (.kwMinimize :: ts₂) ≠ .colonColon :: r := by
        intro r hr; simp at hr
      have hnp : ∀ r, (.kwMinimize :: ts₂) ≠ .lParen :: r := by
        intro r hr; simp at hr
      have ha' : GrAnnotations st.advance.remaining a (.kwMinimize :: ts₂) := by
        rw [hrem1]; exact ha
      have hfuel' : 2 * st.advance.remaining.length + 6 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₂⟩ := parseAnnotations_complete ha' hfuel' hnc hnp
      obtain ⟨hmin, hrem₃⟩ := expectTok_complete (what := "'minimize'") hrem₂
      -- the basic-expr's rest is `;`: never `..`
      have hnd : ∀ r, (.semi :: rest) ≠ .dotDot :: r := by intro r hr; simp at hr
      have he' : GrBasicExpr st₁.advance.remaining e (.semi :: rest) := by
        rw [hrem₃]; exact he
      have hfuel'' : 2 * st₁.advance.remaining.length + 3 ≤ fuel := by
        -- the annotations derivation leaves a suffix of `ts₁` ending at
        -- `.kwMinimize :: ts₂`, so `ts₂` is strictly shorter than `ts₁`
        have hge : 1 ≤ ts₁.length - ts₂.length := by
          have hs := ha.suffix
          obtain ⟨pre, hpre⟩ := hs
          rw [hpre]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen2 : st₁.advance.remaining.length = ts₂.length := by rw [hrem₃]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₄⟩ := parseBasicExpr_complete he' hfuel'' hnd
      obtain ⟨hsemi, hrem₅⟩ := expectTok_complete (what := "';'") hrem₄
      refine ⟨st₂.advance, ?_, hrem₅⟩
      unfold parseSolveItem
      simp only [peek?_eq_of_remaining_cons hrem, hs, hparse, Bind.bind, Except.bind,
        pure, Except.pure]
      have hpeek : st₁.peek? = some .kwMinimize := peek?_eq_of_remaining_cons hrem₂
      simp only [hpeek, ↓reduceIte, hmin, hparse₂, hsemi]
    | @maximize ts₁ a ts₂ e r ha he =>
      have hrem : st.remaining = .kwSolve :: ts₁ := heq
      obtain ⟨hs, hrem1⟩ := expectTok_complete (what := "'solve'") hrem
      -- the annotations' rest is `maximize ...`: not `::` and not `(`
      have hnc : ∀ r, (.kwMaximize :: ts₂) ≠ .colonColon :: r := by
        intro r hr; simp at hr
      have hnp : ∀ r, (.kwMaximize :: ts₂) ≠ .lParen :: r := by
        intro r hr; simp at hr
      have ha' : GrAnnotations st.advance.remaining a (.kwMaximize :: ts₂) := by
        rw [hrem1]; exact ha
      have hfuel' : 2 * st.advance.remaining.length + 6 ≤ fuel := by
        have hlen : st.remaining.length = 1 + st.advance.remaining.length := by
          rw [hrem1, hrem]; simp only [List.length_cons]; omega
        have h2 := hfuel
        rw [hlen] at h2
        omega
      obtain ⟨st₁, hparse, hrem₂⟩ := parseAnnotations_complete ha' hfuel' hnc hnp
      obtain ⟨hmax, hrem₃⟩ := expectTok_complete (what := "'maximize'") hrem₂
      -- the basic-expr's rest is `;`: never `..`
      have hnd : ∀ r, (.semi :: rest) ≠ .dotDot :: r := by intro r hr; simp at hr
      have he' : GrBasicExpr st₁.advance.remaining e (.semi :: rest) := by
        rw [hrem₃]; exact he
      have hfuel'' : 2 * st₁.advance.remaining.length + 3 ≤ fuel := by
        -- the annotations derivation leaves a suffix of `ts₁` ending at
        -- `.kwMaximize :: ts₂`, so `ts₂` is strictly shorter than `ts₁`
        have hge : 1 ≤ ts₁.length - ts₂.length := by
          have hs := ha.suffix
          obtain ⟨pre, hpre⟩ := hs
          rw [hpre]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen2 : st₁.advance.remaining.length = ts₂.length := by rw [hrem₃]
        have hlen : st.remaining.length = 1 + ts₁.length := by
          rw [hrem]; simp only [List.length_cons]; omega
        omega
      obtain ⟨st₂, hparse₂, hrem₄⟩ := parseBasicExpr_complete he' hfuel'' hnd
      obtain ⟨hsemi, hrem₅⟩ := expectTok_complete (what := "';'") hrem₄
      refine ⟨st₂.advance, ?_, hrem₅⟩
      unfold parseSolveItem
      simp only [peek?_eq_of_remaining_cons hrem, hs, hparse, Bind.bind, Except.bind,
        pure, Except.pure]
      have hpeek : st₁.peek? = some .kwMaximize := peek?_eq_of_remaining_cons hrem₂
      simp only [hpeek, ↓reduceIte, hmax, hparse₂, hsemi]
end LeanFzn.Parser

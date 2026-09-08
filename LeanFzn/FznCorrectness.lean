import LeanFzn.FznParser
import LeanFzn.FznGrammar
import LeanFzn.FznSemantics

/-
# Parser Correctness (integer/Boolean fragment)

We prove that the parser is sound and complete with respect to the grammar
relation of `FznGrammar.lean`:

* **Soundness** (`parseModel_sound`): if `parseModel s = .ok m`, then `s`
  derives `m` according to the grammar — the produced AST is valid FlatZinc.
* **Completeness** (`parseModel_complete`): if `s` derives `m`, then
  `parseModel s = .ok m` — every valid FlatZinc string is accepted.

Together with totality of `parseModel` (it is a total Lean function), these
give the decoder characterisation: the parser succeeds iff the input is valid,
and when it fails the input is not valid FlatZinc.

## Proof strategy

The parser is fuelled and works on a `State` (token array + index); the grammar
relation works on `List Token`.  The bridge is `State.remaining`.  Both
directions are proved by mutual induction over the parser functions / grammar
relations, using:

1. *Prefix*: every parser function, on success, splits `st.remaining` into the
   consumed prefix (which drives the grammar derivation) and `st'.remaining`.
2. *Fuel monotonicity*: a parse that succeeds with some fuel succeeds with any
   larger fuel, so the specific fuel bound does not matter for validity.
-/

namespace LeanFzn

open LeanFzn.Lexer LeanFzn.Parser

/-! ## Basic bridge lemmas -/

/-- `expect` on success consumes exactly the head token. -/
theorem expect_remaining {pred what st t st'} :
    expect pred what st = .ok (t, st') →
    st.remaining = t :: st'.remaining ∧ st'.pos = st.pos + 1 := by
  intro h
  unfold expect at h
  simp only at h
  split at h
  · rename_i hlt
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      constructor
      · unfold State.remaining State.advance
        rw [List.drop_eq_getElem_cons hlt]
        simp [List.tail_drop]
      · rfl
    · contradiction
  · contradiction

/-- `expectTok` on success consumes exactly the given head token. -/
theorem expectTok_remaining {t what st st'} :
    expectTok t what st = .ok st' →
    st.remaining = t :: st'.remaining ∧ st'.pos = st.pos + 1 := by
  intro h
  unfold expectTok at h
  split at h
  · rename_i hlt
    split at h
    · rename_i heq
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, rfl⟩
      unfold State.remaining State.advance
      rw [List.drop_eq_getElem_cons hlt]
      have hgl : st.toks.toList[st.pos] = t := by
        rw [Array.getElem_toList hlt]
        exact heq
      rw [hgl]
    · contradiction
  · contradiction

/-- `parseIdent` on success consumes exactly the head identifier token. -/
theorem parseIdent_remaining {st x st'} :
    parseIdent st = .ok (x, st') →
    st.remaining = .ident x.name :: st'.remaining := by
  intro h
  unfold parseIdent at h
  split at h
  · rename_i s st'' hexp
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hst⟩ := h
    subst hx
    have ⟨hrem, hpos⟩ := expect_remaining hexp
    rw [← hst]
    exact hrem
  · contradiction
  · contradiction

/-- A successful restricted-identifier parse satisfies `<identifier>`. -/
theorem parsePredIdent_isPredIdent {st x st'}
    (h : parsePredIdent st = .ok (x, st')) : IsPredIdent x.name := by
  unfold parsePredIdent at h
  cases hpi : parseIdent st with
  | error e => rw [hpi] at h; contradiction
  | ok val =>
    obtain ⟨x', st''⟩ := val
    rw [hpi] at h
    simp only at h
    split at h
    · contradiction
    · rename_i hn
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hb : x'.name.startsWith "_" with
      | false => exact hb
      | true => exact False.elim (hn hb)

/-- `parsePredIdent` on success consumes exactly the head identifier token. -/
theorem parsePredIdent_remaining {st x st'} :
    parsePredIdent st = .ok (x, st') →
    st.remaining = .ident x.name :: st'.remaining := by
  intro h
  unfold parsePredIdent at h
  cases hpi : parseIdent st with
  | error e => rw [hpi] at h; contradiction
  | ok val =>
    obtain ⟨x', st''⟩ := val
    rw [hpi] at h
    simp only at h
    split at h
    · contradiction
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact parseIdent_remaining hpi

/-- `parseIntLit` on success consumes exactly the head int token. -/
theorem parseIntLit_remaining {st i st'} :
    parseIntLit st = .ok (i, st') →
    st.remaining = .intLit i :: st'.remaining := by
  intro h
  unfold parseIntLit at h
  split at h
  · rename_i s st'' hexp
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hst⟩ := h
    subst hx
    have ⟨hrem, hpos⟩ := expect_remaining hexp
    rw [← hst]
    exact hrem
  · contradiction
  · contradiction

/-- `parseBoolLit` on success consumes exactly the head bool token. -/
theorem parseBoolLit_remaining {st b st'} :
    parseBoolLit st = .ok (b, st') →
    st.remaining = .boolLit b :: st'.remaining := by
  intro h
  unfold parseBoolLit at h
  split at h
  · rename_i s st'' hexp
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hst⟩ := h
    subst hx
    have ⟨hrem, hpos⟩ := expect_remaining hexp
    rw [← hst]
    exact hrem
  · contradiction
  · contradiction

/-- `parseStringLit` on success consumes exactly the head string token. -/
theorem parseStringLit_remaining {st s st'} :
    parseStringLit st = .ok (s, st') →
    st.remaining = .stringLit s :: st'.remaining := by
  intro h
  unfold parseStringLit at h
  split at h
  · rename_i s' st'' hexp
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hst⟩ := h
    subst hx
    have ⟨hrem, hpos⟩ := expect_remaining hexp
    rw [← hst]
    exact hrem
  · contradiction
  · contradiction

/-- `check t st = true` means the head of `remaining` is `t`. -/
theorem check_remaining {t st} :
    check t st = true → ∃ rest, st.remaining = t :: rest := by
  intro h
  unfold check State.peek? at h
  split at h
  · rename_i t' hlt
    -- h : decide (t' = t) = true, hlt : (if pos < size then some toks[pos] else none) = some t'
    have h1 : t' = t := of_decide_eq_true h
    split at hlt
    · rename_i hpos
      simp only [Option.some.injEq] at hlt
      -- hlt : st.toks[st.pos] = t'
      have hgl : st.toks.toList[st.pos] = t := by
        rw [Array.getElem_toList hpos, hlt]; exact h1
      unfold State.remaining
      rw [List.drop_eq_getElem_cons hpos]
      exact ⟨st.toks.toList.drop (st.pos + 1), by rw [hgl]⟩
    · contradiction
  · contradiction

/-! ## Completeness bridge lemmas -/

/-- A non-empty `remaining` list exposes the current array element and shows
    that advancing leaves exactly its tail. -/
theorem state_of_remaining_cons {st : State} {t : Token} {rest : List Token}
    (h : st.remaining = t :: rest) :
    ∃ hpos : st.pos < st.toks.size,
      st.toks[st.pos]'hpos = t ∧ st.advance.remaining = rest := by
  have hpos : st.pos < st.toks.size := by
    have hlen : 0 < st.remaining.length := by rw [h]; simp
    unfold State.remaining at hlen
    simp only [Array.length_toList, List.length_drop] at hlen
    omega
  have hdrop := List.drop_eq_getElem_cons (l := st.toks.toList) hpos
  unfold State.remaining at h
  rw [hdrop] at h
  have hhead : st.toks.toList[st.pos] = t := by simp_all
  have htail : st.toks.toList.drop (st.pos + 1) = rest := by simp_all
  refine ⟨hpos, ?_, ?_⟩
  · simpa only [Array.getElem_toList] using hhead
  · exact htail

/-- A non-empty remainder determines the parser state's current token. -/
theorem peek?_eq_of_remaining_cons {st : State} {t : Token} {rest : List Token}
    (h : st.remaining = t :: rest) : st.peek? = some t := by
  obtain ⟨hpos, htok, _⟩ := state_of_remaining_cons h
  unfold State.peek?
  simp only [hpos, htok, ↓reduceDIte]

/-- Completeness of exact-token consumption. -/
theorem expectTok_complete {st : State} {t : Token} {rest : List Token} {what : String}
    (h : st.remaining = t :: rest) :
    expectTok t what st = .ok st.advance ∧ st.advance.remaining = rest := by
  obtain ⟨hpos, htok, hrem⟩ := state_of_remaining_cons h
  constructor
  · unfold expectTok
    simp only [hpos, htok, ↓reduceDIte, ↓reduceIte]
  · exact hrem

/-- Completeness of predicate-based token consumption. -/
theorem expect_complete {st : State} {t : Token} {rest : List Token}
    {pred : Token → Bool} {what : String}
    (hrem : st.remaining = t :: rest) (hpred : pred t = true) :
    expect pred what st = .ok (t, st.advance) ∧ st.advance.remaining = rest := by
  obtain ⟨hpos, htok, htail⟩ := state_of_remaining_cons hrem
  constructor
  · unfold expect
    simp only [hpos, htok, hpred, ↓reduceDIte, ↓reduceIte]
  · exact htail

/-- Completeness of unrestricted identifier parsing. -/
theorem parseIdent_complete {st : State} {x : String} {rest : List Token}
    (h : st.remaining = .ident x :: rest) :
    parseIdent st = .ok (⟨x⟩, st.advance) ∧ st.advance.remaining = rest := by
  constructor
  · unfold parseIdent
    rw [(expect_complete h (by rfl)).1]
  · exact (state_of_remaining_cons h).choose_spec.2

/-- Completeness of restricted FlatZinc identifier parsing. -/
theorem parsePredIdent_complete {st : State} {x : String} {rest : List Token}
    (h : st.remaining = .ident x :: rest) (hx : IsPredIdent x) :
    parsePredIdent st = .ok (⟨x⟩, st.advance) ∧ st.advance.remaining = rest := by
  obtain ⟨hident, hrem⟩ := parseIdent_complete h
  constructor
  · unfold parsePredIdent
    simp only [hident]
    simp only [IsPredIdent] at hx
    simp [hx]
  · exact hrem

/-- Completeness of integer-literal parsing. -/
theorem parseIntLit_complete {st : State} {i : Int} {rest : List Token}
    (h : st.remaining = .intLit i :: rest) :
    parseIntLit st = .ok (i, st.advance) ∧ st.advance.remaining = rest := by
  constructor
  · unfold parseIntLit
    rw [(expect_complete h (by rfl)).1]
  · exact (state_of_remaining_cons h).choose_spec.2

/-- Completeness of Boolean-literal parsing. -/
theorem parseBoolLit_complete {st : State} {b : Bool} {rest : List Token}
    (h : st.remaining = .boolLit b :: rest) :
    parseBoolLit st = .ok (b, st.advance) ∧ st.advance.remaining = rest := by
  constructor
  · unfold parseBoolLit
    rw [(expect_complete h (by rfl)).1]
  · exact (state_of_remaining_cons h).choose_spec.2

/-- Completeness of annotation-string parsing. -/
theorem parseStringLit_complete {st : State} {s : String} {rest : List Token}
    (h : st.remaining = .stringLit s :: rest) :
    parseStringLit st = .ok (s, st.advance) ∧ st.advance.remaining = rest := by
  constructor
  · unfold parseStringLit
    rw [(expect_complete h (by rfl)).1]
  · exact (state_of_remaining_cons h).choose_spec.2

/-- Completeness of an integer atom directly from its grammar derivation. -/
theorem parseIntLit_complete_of_grammar {st : State} {i : Int} {rest : List Token}
    (h : GrIntAtom st.remaining i rest) :
    parseIntLit st = .ok (i, st.advance) ∧ st.advance.remaining = rest := by
  generalize heq : st.remaining = toks at h
  cases h
  exact parseIntLit_complete heq

/-- Completeness of `<index-set>`, including the exact resulting remainder. -/
theorem parseIndexSet_complete {st : State} {idx : IndexSet} {rest : List Token}
    (h : GrIndexSet st.remaining idx rest) :
    ∃ st', parseIndexSet st = .ok (idx, st') ∧ st'.remaining = rest := by
  generalize heq : st.remaining = toks at h
  cases h with
  | @mk hi rest =>
    obtain ⟨hi1, hrem1⟩ := parseIntLit_complete heq
    have hdrem : st.advance.remaining = .dotDot :: .intLit hi :: rest := hrem1
    obtain ⟨hd, hrem2⟩ := expectTok_complete (what := "'..'") hdrem
    obtain ⟨hi2, hrem3⟩ := parseIntLit_complete hrem2
    refine ⟨st.advance.advance.advance, ?_, hrem3⟩
    unfold parseIndexSet
    simp only [hi1, Bind.bind, Except.bind]
    simp
    rw [hd]
    simp only [Bind.bind, Except.bind]
    rw [hi2]
    rfl

/-- Completeness of the non-recursive basic parameter-type parser. -/
theorem parseBasicParType_complete {fuel : Nat} {st : State}
    {t : BasicParType} {rest : List Token} (hfuel : 0 < fuel)
    (h : GrBasicParType st.remaining t rest) :
    ∃ st', parseBasicParType fuel st = .ok (t, st') ∧ st'.remaining = rest := by
  generalize heq : st.remaining = toks at h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    cases h with
    | bool =>
      obtain ⟨hkw, hrem⟩ := expectTok_complete (what := "'bool'") heq
      refine ⟨st.advance, ?_, hrem⟩
      unfold parseBasicParType
      simp only [peek?_eq_of_remaining_cons heq, hkw, Bind.bind, Except.bind,
        pure, Except.pure]
    | int =>
      obtain ⟨hkw, hrem⟩ := expectTok_complete (what := "'int'") heq
      refine ⟨st.advance, ?_, hrem⟩
      unfold parseBasicParType
      simp only [peek?_eq_of_remaining_cons heq, hkw, Bind.bind, Except.bind,
        pure, Except.pure]
    | setOfInt =>
      obtain ⟨hset, hrem1⟩ := expectTok_complete (what := "'set'") heq
      obtain ⟨hof, hrem2⟩ := expectTok_complete (what := "'of'") hrem1
      obtain ⟨hint, hrem3⟩ := expectTok_complete (what := "'int'") hrem2
      refine ⟨st.advance.advance.advance, ?_, hrem3⟩
      unfold parseBasicParType
      simp only [peek?_eq_of_remaining_cons heq, hset, hof, hint, Bind.bind,
        Except.bind, pure, Except.pure]

/-- Completeness of predicate array index parsing (`int` or `1..n`). -/
theorem parsePredIndexSet_complete {st : State} {idx : PredIndexSet}
    {rest : List Token} (h : GrPredIndexSet st.remaining idx rest) :
    ∃ st', parsePredIndexSet st = .ok (idx, st') ∧ st'.remaining = rest := by
  generalize heq : st.remaining = toks at h
  cases h with
  | int =>
    obtain ⟨hkw, hrem⟩ := expectTok_complete (what := "'int'") heq
    refine ⟨st.advance, ?_, hrem⟩
    unfold parsePredIndexSet
    simp only [peek?_eq_of_remaining_cons heq, hkw, Bind.bind, Except.bind,
      pure, Except.pure]
  | range hidx =>
    cases hidx with
    | @mk hi rest =>
      have hpeek := peek?_eq_of_remaining_cons heq
      have hgr : GrIndexSet st.remaining ⟨hi⟩ rest := by
        rw [heq]
        exact GrIndexSet.mk
      obtain ⟨st', hparse, hrem⟩ := parseIndexSet_complete hgr
      refine ⟨st', ?_, hrem⟩
      unfold parsePredIndexSet
      simp only [hpeek, hparse, Bind.bind, Except.bind, pure, Except.pure]

/-! ## Soundness of the expression-level parsers

Each lemma has the form: if the parser succeeds on `st` producing `ast` and
`st'`, then the grammar derives `ast` from `st.remaining`, leaving
`st'.remaining`.  Proved by mutual induction on the fuel. -/

/- Soundness of the integer-list parsers. -/
mutual
theorem parseIntList_sound {fuel st elems st'} :
    parseIntList fuel st = .ok (elems, st') →
    GrSepList GrIntAtom st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseIntList at h
    simp only at h
    split at h
    · rename_i i hpk
      cases hpi : parseIntLit st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨i', st₁⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parseIntListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hremi := parseIntLit_remaining hpi
          have hgrtail := parseIntListTail_sound hpt
          rw [hremi]
          exact GrSepList.cons GrIntAtom.mk hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
theorem parseIntListTail_sound {fuel st elems st'} :
    parseIntListTail fuel st = .ok (elems, st') →
    GrSepListTail GrIntAtom st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseIntListTail at h
    simp only at h
    split at h
    · rename_i hpk
      cases hcomma : expectTok .comma "','" st with
      | error e => rw [hcomma] at h; contradiction
      | ok st₁ =>
        rw [hcomma] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpi : parseIntLit st₁ with
        | error e => rw [hpi] at h; contradiction
        | ok val =>
          obtain ⟨i, st₂⟩ := val
          rw [hpi] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseIntListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hcomma
            have hremi := parseIntLit_remaining hpi
            have hgrtail := parseIntListTail_sound hpt
            rw [hremc, hremi]
            exact GrSepListTail.cons GrIntAtom.mk hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
end

/-- Soundness and non-emptiness of the non-empty integer-list parser. -/
theorem parseNonemptyIntList_sound {fuel st elems st'}
    (h : parseNonemptyIntList fuel st = .ok (elems, st')) :
    elems ≠ [] ∧ GrSepList GrIntAtom st.remaining elems st'.remaining := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseNonemptyIntList at h
    simp only at h
    cases hpi : parseIntLit st with
    | error e => rw [hpi] at h; contradiction
    | ok val =>
      obtain ⟨i, st₁⟩ := val
      rw [hpi] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpt : parseIntListTail fuel st₁ with
      | error e => rw [hpt] at h; contradiction
      | ok val2 =>
        obtain ⟨rest, st₂⟩ := val2
        rw [hpt] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, ?_⟩
        rw [parseIntLit_remaining hpi]
        exact GrSepList.cons GrIntAtom.mk (parseIntListTail_sound hpt)

/-- Soundness of the set-literal parser. -/
theorem parseSetLiteral_sound {fuel st s st'} :
    parseSetLiteral fuel st = .ok (s, st') →
    GrSetLiteral st.remaining s st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseSetLiteral at h
    simp only at h
    split at h
    · -- lBrace: { ints }
      rename_i hpk
      cases hl : expectTok .lBrace "'{'" st with
      | error e => rw [hl] at h; contradiction
      | ok st₁ =>
        rw [hl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpi : parseIntList fuel st₁ with
        | error e => rw [hpi] at h; contradiction
        | ok val =>
          obtain ⟨elems, st₂⟩ := val
          rw [hpi] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hr : expectTok .rBrace "'}'" st₂ with
          | error e => rw [hr] at h; contradiction
          | ok st₃ =>
            rw [hr] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hrem1, _⟩ := expectTok_remaining hl
            have hgr := parseIntList_sound hpi
            have ⟨hrem2, _⟩ := expectTok_remaining hr
            rw [hrem2] at hgr
            rw [hrem1]
            exact GrSetLiteral.intSet hgr
    · -- intLit: lo .. hi
      rename_i lo hpk
      cases hpi : parseIntLit st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨lo', st₁⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hd : expectTok .dotDot "'..'" st₁ with
        | error e => rw [hd] at h; contradiction
        | ok st₂ =>
          rw [hd] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi2 : parseIntLit st₂ with
          | error e => rw [hpi2] at h; contradiction
          | ok val2 =>
            obtain ⟨hi', st₃⟩ := val2
            rw [hpi2] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hrem1 := parseIntLit_remaining hpi
            have ⟨hrem2, _⟩ := expectTok_remaining hd
            have hrem3 := parseIntLit_remaining hpi2
            rw [hrem1, hrem2, hrem3]
            exact GrSetLiteral.intRange
    · contradiction

/-- Soundness of the basic-literal parser. -/
theorem parseBasicLiteral_sound {fuel st l st'} :
    parseBasicLiteral fuel st = .ok (l, st') →
    GrBasicLiteral st.remaining l st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicLiteral at h
    simp only at h
    split at h
    · -- boolLit
      rename_i b hpk
      cases hpb : parseBoolLit st with
      | error e => rw [hpb] at h; contradiction
      | ok val =>
        obtain ⟨b', st₁⟩ := val
        rw [hpb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrem := parseBoolLit_remaining hpb
        rw [hrem]
        exact GrBasicLiteral.bool
    · -- intLit: int or int range set
      rename_i i hpk
      cases hpi : parseIntLit st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨i', st₁⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        split at h
        · -- dotDot follows: int range
          rename_i hchk
          cases hd : expectTok .dotDot "'..'" st₁ with
          | error e => rw [hd] at h; contradiction
          | ok st₂ =>
            rw [hd] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hpi2 : parseIntLit st₂ with
            | error e => rw [hpi2] at h; contradiction
            | ok val2 =>
              obtain ⟨hi', st₃⟩ := val2
              rw [hpi2] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrem1 := parseIntLit_remaining hpi
              have ⟨hrem2, _⟩ := expectTok_remaining hd
              have hrem3 := parseIntLit_remaining hpi2
              rw [hrem1, hrem2, hrem3]
              exact GrBasicLiteral.intRange
        · -- plain int
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hrem := parseIntLit_remaining hpi
          rw [hrem]
          exact GrBasicLiteral.int
    · -- lBrace: int set
      rename_i hpk
      cases hps : parseSetLiteral fuel st with
      | error e => rw [hps] at h; contradiction
      | ok val =>
        obtain ⟨s, st₁⟩ := val
        rw [hps] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseSetLiteral_sound hps
        -- st.remaining starts with lBrace, so the intRange case is impossible
        have ⟨rest0, hrem0⟩ := check_remaining (by
          unfold check; rw [hpk]; rfl : check .lBrace st = true)
        rw [hrem0] at hgr
        cases hgr with
        | intSet hlist =>
          rw [hrem0]
          exact GrBasicLiteral.intSet hlist
    · contradiction

/-- Soundness of the basic-expression parser. -/
theorem parseBasicExpr_sound {fuel st e st'} :
    parseBasicExpr fuel st = .ok (e, st') →
    GrBasicExpr st.remaining e st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicExpr at h
    simp only at h
    split at h
    · -- ident
      rename_i x hpk
      cases hpi : parseIdent st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨x', st₁⟩ := val
        rw [hpi] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrem := parseIdent_remaining hpi
        rw [hrem]
        exact GrBasicExpr.ident
    · -- literal
      cases hpl : parseBasicLiteral fuel st with
      | error e => rw [hpl] at h; contradiction
      | ok val =>
        obtain ⟨l, st₁⟩ := val
        rw [hpl] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseBasicLiteral_sound hpl
        exact GrBasicExpr.lit hgr

/- Soundness of the basic-expression list parsers. -/
mutual
theorem parseBasicExprList_sound {fuel st elems st'} :
    parseBasicExprList fuel st = .ok (elems, st') →
    GrSepList GrBasicExpr st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicExprList at h
    simp only at h
    split at h
    · -- rBrack: empty
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
    · -- an element
      cases hpe : parseBasicExpr fuel st with
      | error e => rw [hpe] at h; contradiction
      | ok val =>
        obtain ⟨e, st₁⟩ := val
        rw [hpe] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parseBasicExprListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := parseBasicExpr_sound hpe
          have hgrtail := parseBasicExprListTail_sound hpt
          exact GrSepList.cons hgr hgrtail
theorem parseBasicExprListTail_sound {fuel st elems st'} :
    parseBasicExprListTail fuel st = .ok (elems, st') →
    GrSepListTail GrBasicExpr st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicExprListTail at h
    simp only at h
    split at h
    · -- comma
      rename_i hpk
      cases hc : expectTok .comma "','" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpe : parseBasicExpr fuel st₁ with
        | error e => rw [hpe] at h; contradiction
        | ok val =>
          obtain ⟨e, st₂⟩ := val
          rw [hpe] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseBasicExprListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parseBasicExpr_sound hpe
            have hgrtail := parseBasicExprListTail_sound hpt
            rw [hremc]
            exact GrSepListTail.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
end

/-- Soundness of the array-literal parser. -/
theorem parseArrayLiteral_sound {fuel st elems st'} :
    parseArrayLiteral fuel st = .ok (elems, st') →
    ∃ mid, st.remaining = .lBrack :: mid ∧
      GrSepList GrBasicExpr mid elems (.rBrack :: st'.remaining) := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseArrayLiteral at h
    simp only at h
    cases hl : expectTok .lBrack "'['" st with
    | error e => rw [hl] at h; contradiction
    | ok st₁ =>
      rw [hl] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpl : parseBasicExprList fuel st₁ with
      | error e => rw [hpl] at h; contradiction
      | ok val =>
        obtain ⟨elems', st₂⟩ := val
        rw [hpl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hr : expectTok .rBrack "']'" st₂ with
        | error e => rw [hr] at h; contradiction
        | ok st₃ =>
          rw [hr] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ⟨hrem1, _⟩ := expectTok_remaining hl
          have hgr := parseBasicExprList_sound hpl
          have ⟨hrem2, _⟩ := expectTok_remaining hr
          rw [hrem2] at hgr
          exact ⟨st₁.remaining, hrem1, hgr⟩

/-- Soundness of the expression parser. -/
theorem parseExpr_sound {fuel st e st'} :
    parseExpr fuel st = .ok (e, st') →
    GrExpr st.remaining e st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseExpr at h
    simp only at h
    split at h
    · -- lBrack: array
      rename_i hpk
      cases hpa : parseArrayLiteral fuel st with
      | error e => rw [hpa] at h; contradiction
      | ok val =>
        obtain ⟨elems, st₁⟩ := val
        rw [hpa] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ⟨mid, hmid, hgr⟩ := parseArrayLiteral_sound hpa
        rw [hmid]
        exact GrExpr.array hgr
    · -- basic
      cases hpb : parseBasicExpr fuel st with
      | error e => rw [hpb] at h; contradiction
      | ok val =>
        obtain ⟨b, st₁⟩ := val
        rw [hpb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseBasicExpr_sound hpb
        exact GrExpr.basic hgr

/-- Annotation-argument parsing can only return a non-empty list. -/
theorem parseAnnExprList_ne_nil {fuel st args st'}
    (h : parseAnnExprList fuel st = .ok (args, st')) : args ≠ [] := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnExprList at h
    simp only at h
    cases hpa : parseAnnExpr fuel st with
    | error e => rw [hpa] at h; contradiction
    | ok val =>
      obtain ⟨a, st₁⟩ := val
      rw [hpa] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpt : parseAnnExprListTail fuel st₁ with
      | error e => rw [hpt] at h; contradiction
      | ok val2 =>
        obtain ⟨rest, st₂⟩ := val2
        rw [hpt] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp

/- Soundness of the annotation parsers (mutually recursive). -/
mutual
theorem parseAnnotation_sound {fuel st a st'} :
    parseAnnotation fuel st = .ok (a, st') →
    GrAnnotation st.remaining a st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnotation at h
    simp only at h
    cases hpi : parsePredIdent st with
    | error e => rw [hpi] at h; contradiction
    | ok val =>
      obtain ⟨x, st₁⟩ := val
      rw [hpi] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      split at h
      · -- lParen: call
        rename_i hpk
        cases hl : expectTok .lParen "'('" st₁ with
        | error e => rw [hl] at h; contradiction
        | ok st₂ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpa : parseAnnExprList fuel st₂ with
          | error e => rw [hpa] at h; contradiction
          | ok val2 =>
            obtain ⟨args, st₃⟩ := val2
            rw [hpa] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rParen "')'" st₃ with
            | error e => rw [hr] at h; contradiction
            | ok st₄ =>
              rw [hr] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hremi := parsePredIdent_remaining hpi
              have hid := parsePredIdent_isPredIdent hpi
              have hne := parseAnnExprList_ne_nil hpa
              have ⟨hreml, _⟩ := expectTok_remaining hl
              have hgr := parseAnnExprList_sound hpa
              have ⟨hremr, _⟩ := expectTok_remaining hr
              rw [hremr] at hgr
              rw [hremi, hreml]
              exact GrAnnotation.call hid hne hgr
      · -- plain ident
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrem := parsePredIdent_remaining hpi
        have hid := parsePredIdent_isPredIdent hpi
        rw [hrem]
        exact GrAnnotation.ident hid
theorem parseAnnExprList_sound {fuel st args st'} :
    parseAnnExprList fuel st = .ok (args, st') →
    GrSepList GrAnnExpr st.remaining args st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnExprList at h
    simp only at h
    cases hpa : parseAnnExpr fuel st with
    | error e => rw [hpa] at h; contradiction
    | ok val =>
      obtain ⟨a, st₁⟩ := val
      rw [hpa] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpt : parseAnnExprListTail fuel st₁ with
      | error e => rw [hpt] at h; contradiction
      | ok val2 =>
        obtain ⟨rest, st₂⟩ := val2
        rw [hpt] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseAnnExpr_sound hpa
        have hgrtail := parseAnnExprListTail_sound hpt
        exact GrSepList.cons hgr hgrtail
theorem parseAnnExprListTail_sound {fuel st args st'} :
    parseAnnExprListTail fuel st = .ok (args, st') →
    GrSepListTail GrAnnExpr st.remaining args st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnExprListTail at h
    simp only at h
    split at h
    · -- comma
      rename_i hpk
      cases hc : expectTok .comma "','" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpa : parseAnnExpr fuel st₁ with
        | error e => rw [hpa] at h; contradiction
        | ok val =>
          obtain ⟨a, st₂⟩ := val
          rw [hpa] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseAnnExprListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parseAnnExpr_sound hpa
            have hgrtail := parseAnnExprListTail_sound hpt
            rw [hremc]
            exact GrSepListTail.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
theorem parseAnnExpr_sound {fuel st a st'} :
    parseAnnExpr fuel st = .ok (a, st') →
    GrAnnExpr st.remaining a st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnExpr at h
    simp only at h
    split at h
    · -- stringLit
      rename_i s hpk
      cases hps : parseStringLit st with
      | error e => rw [hps] at h; contradiction
      | ok val =>
        obtain ⟨s', st₁⟩ := val
        rw [hps] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrem := parseStringLit_remaining hps
        rw [hrem]
        exact GrAnnExpr.string
    · -- lBrack: array
      rename_i hpk
      cases hl : expectTok .lBrack "'['" st with
      | error e => rw [hl] at h; contradiction
      | ok st₁ =>
        rw [hl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpa : parseAnnExprArrayContents fuel st₁ with
        | error e => rw [hpa] at h; contradiction
        | ok val =>
          obtain ⟨elems, st₂⟩ := val
          rw [hpa] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hr : expectTok .rBrack "']'" st₂ with
          | error e => rw [hr] at h; contradiction
          | ok st₃ =>
            rw [hr] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hreml, _⟩ := expectTok_remaining hl
            have hgr := parseAnnExprArrayContents_sound hpa
            have ⟨hremr, _⟩ := expectTok_remaining hr
            rw [hremr] at hgr
            rw [hreml]
            exact GrAnnExpr.array hgr
    · -- ident: plain or nested annotation
      rename_i x hpk
      cases hpi : parseIdent st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨x', st₁⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        split at h
        · -- lParen: nested annotation call
          rename_i hpk2
          split at h
          · contradiction
          · rename_i hid
            cases hl : expectTok .lParen "'('" st₁ with
            | error e => rw [hl] at h; contradiction
            | ok st₂ =>
              rw [hl] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hpa : parseAnnExprList fuel st₂ with
              | error e => rw [hpa] at h; contradiction
              | ok val2 =>
                obtain ⟨args, st₃⟩ := val2
                rw [hpa] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hr : expectTok .rParen "')'" st₃ with
                | error e => rw [hr] at h; contradiction
                | ok st₄ =>
                  rw [hr] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hremi := parseIdent_remaining hpi
                  have ⟨hreml, _⟩ := expectTok_remaining hl
                  have hgr := parseAnnExprList_sound hpa
                  have hne := parseAnnExprList_ne_nil hpa
                  have ⟨hremr, _⟩ := expectTok_remaining hr
                  rw [hremr] at hgr
                  rw [hremi, hreml]
                  have hpred : IsPredIdent x'.name := by
                    cases hb : x'.name.startsWith "_" with
                    | false => exact hb
                    | true => exact False.elim (hid hb)
                  exact GrAnnExpr.annCall hpred hne hgr
        · -- plain ident
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hrem := parseIdent_remaining hpi
          rw [hrem]
          exact GrAnnExpr.ident
    · -- literal
      cases hpl : parseBasicLiteral fuel st with
      | error e => rw [hpl] at h; contradiction
      | ok val =>
        obtain ⟨l, st₁⟩ := val
        rw [hpl] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseBasicLiteral_sound hpl
        exact GrAnnExpr.lit hgr
theorem parseAnnExprArrayContents_sound {fuel st elems st'} :
    parseAnnExprArrayContents fuel st = .ok (elems, st') →
    GrSepList GrAnnExpr st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnExprArrayContents at h
    simp only at h
    split at h
    · -- rBrack: empty
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
    · -- an element
      cases hpa : parseAnnExpr fuel st with
      | error e => rw [hpa] at h; contradiction
      | ok val =>
        obtain ⟨a, st₁⟩ := val
        rw [hpa] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parseAnnExprListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := parseAnnExpr_sound hpa
          have hgrtail := parseAnnExprListTail_sound hpt
          exact GrSepList.cons hgr hgrtail
end

/-- Soundness of the annotations parser. -/
theorem parseAnnotations_sound {fuel st anns st'} :
    parseAnnotations fuel st = .ok (anns, st') →
    GrAnnotations st.remaining anns st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseAnnotations at h
    simp only at h
    split at h
    · -- colonColon
      rename_i hpk
      cases hc : expectTok .colonColon "'::'" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpa : parseAnnotation fuel st₁ with
        | error e => rw [hpa] at h; contradiction
        | ok val =>
          obtain ⟨a, st₂⟩ := val
          rw [hpa] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseAnnotations fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parseAnnotation_sound hpa
            have hgrtail := parseAnnotations_sound hpt
            rw [hremc]
            exact GrAnnotations.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrAnnotations.nil

/-- Soundness of the basic-par-type parser. -/
theorem parseBasicParType_sound {fuel st t st'} :
    parseBasicParType fuel st = .ok (t, st') →
    GrBasicParType st.remaining t st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicParType at h
    simp only at h
    split at h
    · -- bool
      rename_i hpk
      cases hb : expectTok .kwBool "'bool'" st with
      | error e => rw [hb] at h; contradiction
      | ok st₁ =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ⟨hrem, _⟩ := expectTok_remaining hb
        rw [hrem]
        exact GrBasicParType.bool
    · -- int
      rename_i hpk
      cases hb : expectTok .kwInt "'int'" st with
      | error e => rw [hb] at h; contradiction
      | ok st₁ =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ⟨hrem, _⟩ := expectTok_remaining hb
        rw [hrem]
        exact GrBasicParType.int
    · -- set of int
      rename_i hpk
      cases hb : expectTok .kwSet "'set'" st with
      | error e => rw [hb] at h; contradiction
      | ok st₁ =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases ho : expectTok .kwOf "'of'" st₁ with
        | error e => rw [ho] at h; contradiction
        | ok st₂ =>
          rw [ho] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hi : expectTok .kwInt "'int'" st₂ with
          | error e => rw [hi] at h; contradiction
          | ok st₃ =>
            rw [hi] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hrem1, _⟩ := expectTok_remaining hb
            have ⟨hrem2, _⟩ := expectTok_remaining ho
            have ⟨hrem3, _⟩ := expectTok_remaining hi
            rw [hrem1, hrem2, hrem3]
            exact GrBasicParType.setOfInt
    · contradiction

/-- Soundness of the index-set parser. -/
theorem parseIndexSet_sound {st i st'} :
    parseIndexSet st = .ok (i, st') →
    GrIndexSet st.remaining i st'.remaining := by
  intro h
  unfold parseIndexSet at h
  simp only at h
  cases hpi : parseIntLit st with
  | error e => rw [hpi] at h; contradiction
  | ok val =>
    obtain ⟨lo, st₁⟩ := val
    rw [hpi] at h
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    split at h
    · contradiction
    · rename_i hne
      -- hne : ¬(lo != 1) = true, so lo = 1
      have hlo : lo = 1 := by
        simp only [Bool.not_eq_true] at hne
        have h2 : (lo == 1) = true := by
          cases h1 : (lo == 1) <;> simp_all [BEq.beq]
        exact eq_of_beq h2
      cases hd : expectTok .dotDot "'..'" st₁ with
      | error e => rw [hd] at h; contradiction
      | ok st₂ =>
        rw [hd] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpi2 : parseIntLit st₂ with
        | error e => rw [hpi2] at h; contradiction
        | ok val2 =>
          obtain ⟨hi, st₃⟩ := val2
          rw [hpi2] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hrem1 := parseIntLit_remaining hpi
          have ⟨hrem2, _⟩ := expectTok_remaining hd
          have hrem3 := parseIntLit_remaining hpi2
          rw [hrem1, hrem2, hrem3]
          subst hlo
          exact GrIndexSet.mk

/-- Soundness of the basic-var-type parser. -/
theorem parseBasicVarType_sound {fuel st t st'} :
    parseBasicVarType fuel st = .ok (t, st') →
    GrBasicVarType st.remaining t st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicVarType at h
    simp only at h
    cases hv : expectTok .kwVar "'var'" st with
    | error e => rw [hv] at h; contradiction
    | ok st₁ =>
      rw [hv] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      have ⟨hremv, _⟩ := expectTok_remaining hv
      split at h
      · -- var bool
        rename_i hpk
        cases hb : expectTok .kwBool "'bool'" st₁ with
        | error e => rw [hb] at h; contradiction
        | ok st₂ =>
          rw [hb] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ⟨hrem, _⟩ := expectTok_remaining hb
          rw [hremv, hrem]
          exact GrBasicVarType.parBool
      · -- var int
        rename_i hpk
        cases hb : expectTok .kwInt "'int'" st₁ with
        | error e => rw [hb] at h; contradiction
        | ok st₂ =>
          rw [hb] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ⟨hrem, _⟩ := expectTok_remaining hb
          rw [hremv, hrem]
          exact GrBasicVarType.parInt
      · -- var set of ...
        rename_i hpk
        cases hs : expectTok .kwSet "'set'" st₁ with
        | error e => rw [hs] at h; contradiction
        | ok st₂ =>
          rw [hs] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases ho : expectTok .kwOf "'of'" st₂ with
          | error e => rw [ho] at h; contradiction
          | ok st₃ =>
            rw [ho] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            have ⟨hrems, _⟩ := expectTok_remaining hs
            have ⟨hremo, _⟩ := expectTok_remaining ho
            split at h
            · -- var set of int
              rename_i hpk2
              cases hi : expectTok .kwInt "'int'" st₃ with
              | error e => rw [hi] at h; contradiction
              | ok st₄ =>
                rw [hi] at h
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have ⟨hremi, _⟩ := expectTok_remaining hi
                rw [hremv, hrems, hremo, hremi]
                exact GrBasicVarType.parSetOfInt
            · -- var set of lo..hi
              rename_i lo hpk2
              cases hpi : parseIntLit st₃ with
              | error e => rw [hpi] at h; contradiction
              | ok val =>
                obtain ⟨lo', st₄⟩ := val
                rw [hpi] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hd : expectTok .dotDot "'..'" st₄ with
                | error e => rw [hd] at h; contradiction
                | ok st₅ =>
                  rw [hd] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases hpi2 : parseIntLit st₅ with
                  | error e => rw [hpi2] at h; contradiction
                  | ok val2 =>
                    obtain ⟨hi', st₆⟩ := val2
                    rw [hpi2] at h
                    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hrem1 := parseIntLit_remaining hpi
                    have ⟨hremd, _⟩ := expectTok_remaining hd
                    have hrem2 := parseIntLit_remaining hpi2
                    rw [hremv, hrems, hremo, hrem1, hremd, hrem2]
                    exact GrBasicVarType.setOfIntRange
            · -- var set of { ... }
              rename_i hpk2
              cases hl : expectTok .lBrace "'{'" st₃ with
              | error e => rw [hl] at h; contradiction
              | ok st₄ =>
                rw [hl] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hpl : parseIntList fuel st₄ with
                | error e => rw [hpl] at h; contradiction
                | ok val =>
                  obtain ⟨elems, st₅⟩ := val
                  rw [hpl] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases hr : expectTok .rBrace "'}'" st₅ with
                  | error e => rw [hr] at h; contradiction
                  | ok st₆ =>
                    rw [hr] at h
                    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have ⟨hreml, _⟩ := expectTok_remaining hl
                    have hgr := parseIntList_sound hpl
                    have ⟨hremr, _⟩ := expectTok_remaining hr
                    rw [hremr] at hgr
                    rw [hremv, hrems, hremo, hreml]
                    exact GrBasicVarType.setOfIntSet hgr
            · contradiction
      · -- var lo..hi
        rename_i lo hpk
        cases hpi : parseIntLit st₁ with
        | error e => rw [hpi] at h; contradiction
        | ok val =>
          obtain ⟨lo', st₂⟩ := val
          rw [hpi] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hd : expectTok .dotDot "'..'" st₂ with
          | error e => rw [hd] at h; contradiction
          | ok st₃ =>
            rw [hd] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hpi2 : parseIntLit st₃ with
            | error e => rw [hpi2] at h; contradiction
            | ok val2 =>
              obtain ⟨hi', st₄⟩ := val2
              rw [hpi2] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrem1 := parseIntLit_remaining hpi
              have ⟨hremd, _⟩ := expectTok_remaining hd
              have hrem2 := parseIntLit_remaining hpi2
              rw [hremv, hrem1, hremd, hrem2]
              exact GrBasicVarType.intRange
      · -- var { ... }
        rename_i hpk
        cases hl : expectTok .lBrace "'{'" st₁ with
        | error e => rw [hl] at h; contradiction
        | ok st₂ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpl : parseNonemptyIntList fuel st₂ with
          | error e => rw [hpl] at h; contradiction
          | ok val =>
            obtain ⟨elems, st₃⟩ := val
            rw [hpl] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rBrace "'}'" st₃ with
            | error e => rw [hr] at h; contradiction
            | ok st₄ =>
              rw [hr] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ⟨hreml, _⟩ := expectTok_remaining hl
              have ⟨hne, hgr⟩ := parseNonemptyIntList_sound hpl
              have ⟨hremr, _⟩ := expectTok_remaining hr
              rw [hremr] at hgr
              rw [hremv, hreml]
              exact GrBasicVarType.intSet hne hgr
      · contradiction

/- Soundness of the basic-literal list parsers. -/
mutual
theorem parseBasicLiteralList_sound {fuel st elems st'} :
    parseBasicLiteralList fuel st = .ok (elems, st') →
    GrSepList GrBasicLiteral st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicLiteralList at h
    simp only at h
    split at h
    · -- rBrack: empty
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
    · -- an element
      cases hpl : parseBasicLiteral fuel st with
      | error e => rw [hpl] at h; contradiction
      | ok val =>
        obtain ⟨l, st₁⟩ := val
        rw [hpl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parseBasicLiteralListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := parseBasicLiteral_sound hpl
          have hgrtail := parseBasicLiteralListTail_sound hpt
          exact GrSepList.cons hgr hgrtail
theorem parseBasicLiteralListTail_sound {fuel st elems st'} :
    parseBasicLiteralListTail fuel st = .ok (elems, st') →
    GrSepListTail GrBasicLiteral st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicLiteralListTail at h
    simp only at h
    split at h
    · -- comma
      rename_i hpk
      cases hc : expectTok .comma "','" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpl : parseBasicLiteral fuel st₁ with
        | error e => rw [hpl] at h; contradiction
        | ok val =>
          obtain ⟨l, st₂⟩ := val
          rw [hpl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseBasicLiteralListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parseBasicLiteral_sound hpl
            have hgrtail := parseBasicLiteralListTail_sound hpt
            rw [hremc]
            exact GrSepListTail.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
end

/-- Soundness of the par-array-literal parser. -/
theorem parseParArrayLiteral_sound {fuel st elems st'} :
    parseParArrayLiteral fuel st = .ok (elems, st') →
    GrParArrayLiteral st.remaining elems st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseParArrayLiteral at h
    simp only at h
    cases hl : expectTok .lBrack "'['" st with
    | error e => rw [hl] at h; contradiction
    | ok st₁ =>
      rw [hl] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpl : parseBasicLiteralList fuel st₁ with
      | error e => rw [hpl] at h; contradiction
      | ok val =>
        obtain ⟨elems', st₂⟩ := val
        rw [hpl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hr : expectTok .rBrack "']'" st₂ with
        | error e => rw [hr] at h; contradiction
        | ok st₃ =>
          rw [hr] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ⟨hrem1, _⟩ := expectTok_remaining hl
          have hgr := parseBasicLiteralList_sound hpl
          have ⟨hrem2, _⟩ := expectTok_remaining hr
          rw [hrem2] at hgr
          rw [hrem1]
          exact GrParArrayLiteral.mk hgr

/-- Soundness of the basic-pred-param-type parser. -/
theorem parseBasicPredParamType_sound {fuel st t st'} :
    parseBasicPredParamType fuel st = .ok (t, st') →
    GrBasicPredParamType st.remaining t st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseBasicPredParamType at h
    simp only at h
    split at h
    · -- var ...
      rename_i hpk
      cases hpv : parseBasicVarType fuel st with
      | error e => rw [hpv] at h; contradiction
      | ok val =>
        obtain ⟨vt, st₁⟩ := val
        rw [hpv] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseBasicVarType_sound hpv
        exact GrBasicPredParamType.var hgr
    · -- set of ...
      rename_i hpk
      cases hs : expectTok .kwSet "'set'" st with
      | error e => rw [hs] at h; contradiction
      | ok st₁ =>
        rw [hs] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases ho : expectTok .kwOf "'of'" st₁ with
        | error e => rw [ho] at h; contradiction
        | ok st₂ =>
          rw [ho] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          have ⟨hrems, _⟩ := expectTok_remaining hs
          have ⟨hremo, _⟩ := expectTok_remaining ho
          split at h
          · -- set of int
            rename_i hpk2
            cases hi : expectTok .kwInt "'int'" st₂ with
            | error e => rw [hi] at h; contradiction
            | ok st₃ =>
              rw [hi] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ⟨hremi, _⟩ := expectTok_remaining hi
              rw [hrems, hremo, hremi]
              exact GrBasicPredParamType.par GrBasicParType.setOfInt
          · -- set of lo..hi
            rename_i lo hpk2
            cases hpi : parseIntLit st₂ with
            | error e => rw [hpi] at h; contradiction
            | ok val =>
              obtain ⟨lo', st₃⟩ := val
              rw [hpi] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hd : expectTok .dotDot "'..'" st₃ with
              | error e => rw [hd] at h; contradiction
              | ok st₄ =>
                rw [hd] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hpi2 : parseIntLit st₄ with
                | error e => rw [hpi2] at h; contradiction
                | ok val2 =>
                  obtain ⟨hi', st₅⟩ := val2
                  rw [hpi2] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hrem1 := parseIntLit_remaining hpi
                  have ⟨hremd, _⟩ := expectTok_remaining hd
                  have hrem2 := parseIntLit_remaining hpi2
                  rw [hrems, hremo, hrem1, hremd, hrem2]
                  exact GrBasicPredParamType.setOfIntRange
          · -- set of { ... }
            rename_i hpk2
            cases hl : expectTok .lBrace "'{'" st₂ with
            | error e => rw [hl] at h; contradiction
            | ok st₃ =>
              rw [hl] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hpl : parseIntList fuel st₃ with
              | error e => rw [hpl] at h; contradiction
              | ok val =>
                obtain ⟨elems, st₄⟩ := val
                rw [hpl] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hr : expectTok .rBrace "'}'" st₄ with
                | error e => rw [hr] at h; contradiction
                | ok st₅ =>
                  rw [hr] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have ⟨hreml, _⟩ := expectTok_remaining hl
                  have hgr := parseIntList_sound hpl
                  have ⟨hremr, _⟩ := expectTok_remaining hr
                  rw [hremr] at hgr
                  rw [hrems, hremo, hreml]
                  exact GrBasicPredParamType.setOfIntSet hgr
          · contradiction
    · -- bool
      rename_i hpk
      cases hb : expectTok .kwBool "'bool'" st with
      | error e => rw [hb] at h; contradiction
      | ok st₁ =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ⟨hrem, _⟩ := expectTok_remaining hb
        rw [hrem]
        exact GrBasicPredParamType.par GrBasicParType.bool
    · -- int
      rename_i hpk
      cases hb : expectTok .kwInt "'int'" st with
      | error e => rw [hb] at h; contradiction
      | ok st₁ =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ⟨hrem, _⟩ := expectTok_remaining hb
        rw [hrem]
        exact GrBasicPredParamType.par GrBasicParType.int
    · -- lo..hi
      rename_i lo hpk
      cases hpi : parseIntLit st with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨lo', st₁⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hd : expectTok .dotDot "'..'" st₁ with
        | error e => rw [hd] at h; contradiction
        | ok st₂ =>
          rw [hd] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi2 : parseIntLit st₂ with
          | error e => rw [hpi2] at h; contradiction
          | ok val2 =>
            obtain ⟨hi', st₃⟩ := val2
            rw [hpi2] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hrem1 := parseIntLit_remaining hpi
            have ⟨hremd, _⟩ := expectTok_remaining hd
            have hrem2 := parseIntLit_remaining hpi2
            rw [hrem1, hremd, hrem2]
            exact GrBasicPredParamType.intRange
    · -- { ... }
      rename_i hpk
      cases hl : expectTok .lBrace "'{'" st with
      | error e => rw [hl] at h; contradiction
      | ok st₁ =>
        rw [hl] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpl : parseNonemptyIntList fuel st₁ with
        | error e => rw [hpl] at h; contradiction
        | ok val =>
          obtain ⟨elems, st₂⟩ := val
          rw [hpl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hr : expectTok .rBrace "'}'" st₂ with
          | error e => rw [hr] at h; contradiction
          | ok st₃ =>
            rw [hr] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hreml, _⟩ := expectTok_remaining hl
            have ⟨hne, hgr⟩ := parseNonemptyIntList_sound hpl
            have ⟨hremr, _⟩ := expectTok_remaining hr
            rw [hremr] at hgr
            rw [hreml]
            exact GrBasicPredParamType.intSet hne hgr
    · contradiction

/-- Soundness of the pred-index-set parser. -/
theorem parsePredIndexSet_sound {st i st'} :
    parsePredIndexSet st = .ok (i, st') →
    GrPredIndexSet st.remaining i st'.remaining := by
  intro h
  unfold parsePredIndexSet at h
  simp only at h
  split at h
  · -- int
    rename_i hpk
    cases hi : expectTok .kwInt "'int'" st with
    | error e => rw [hi] at h; contradiction
    | ok st₁ =>
      rw [hi] at h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ⟨hrem, _⟩ := expectTok_remaining hi
      rw [hrem]
      exact GrPredIndexSet.int
  · -- index set
    cases hpi : parseIndexSet st with
    | error e => rw [hpi] at h; contradiction
    | ok val =>
      obtain ⟨i', st₁⟩ := val
      rw [hpi] at h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hgr := parseIndexSet_sound hpi
      exact GrPredIndexSet.range hgr

/-- Soundness of the pred-param-type parser. -/
theorem parsePredParamType_sound {fuel st t st'} :
    parsePredParamType fuel st = .ok (t, st') →
    GrPredParamType st.remaining t st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parsePredParamType at h
    simp only at h
    split at h
    · -- array
      rename_i hpk
      cases ha : expectTok .kwArray "'array'" st with
      | error e => rw [ha] at h; contradiction
      | ok st₁ =>
        rw [ha] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hl : expectTok .lBrack "'['" st₁ with
        | error e => rw [hl] at h; contradiction
        | ok st₂ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi : parsePredIndexSet st₂ with
          | error e => rw [hpi] at h; contradiction
          | ok val =>
            obtain ⟨idx, st₃⟩ := val
            rw [hpi] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rBrack "']'" st₃ with
            | error e => rw [hr] at h; contradiction
            | ok st₄ =>
              rw [hr] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases ho : expectTok .kwOf "'of'" st₄ with
              | error e => rw [ho] at h; contradiction
              | ok st₅ =>
                rw [ho] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hpe : parseBasicPredParamType fuel st₅ with
                | error e => rw [hpe] at h; contradiction
                | ok val2 =>
                  obtain ⟨elem, st₆⟩ := val2
                  rw [hpe] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have ⟨hrema, _⟩ := expectTok_remaining ha
                  have ⟨hreml, _⟩ := expectTok_remaining hl
                  have hgridx := parsePredIndexSet_sound hpi
                  have ⟨hremr, _⟩ := expectTok_remaining hr
                  have ⟨hremo, _⟩ := expectTok_remaining ho
                  have hgrelem := parseBasicPredParamType_sound hpe
                  rw [hremr, hremo] at hgridx
                  rw [hrema, hreml]
                  exact GrPredParamType.array hgridx hgrelem
    · -- basic
      cases hpb : parseBasicPredParamType fuel st with
      | error e => rw [hpb] at h; contradiction
      | ok val =>
        obtain ⟨t', st₁⟩ := val
        rw [hpb] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgr := parseBasicPredParamType_sound hpb
        exact GrPredParamType.basic hgr

/-- Soundness of the pred-param parser. -/
theorem parsePredParam_sound {fuel st p st'} :
    parsePredParam fuel st = .ok (p, st') →
    GrPredParam st.remaining p st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parsePredParam at h
    simp only at h
    cases hpt : parsePredParamType fuel st with
    | error e => rw [hpt] at h; contradiction
    | ok val =>
      obtain ⟨t, st₁⟩ := val
      rw [hpt] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hc : expectTok .colon "':'" st₁ with
      | error e => rw [hc] at h; contradiction
      | ok st₂ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpi : parsePredIdent st₂ with
        | error e => rw [hpi] at h; contradiction
        | ok val2 =>
          obtain ⟨x, st₃⟩ := val2
          rw [hpi] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgrt := parsePredParamType_sound hpt
          have ⟨hremc, _⟩ := expectTok_remaining hc
          have hremi := parsePredIdent_remaining hpi
          have hid := parsePredIdent_isPredIdent hpi
          rw [hremc] at hgrt
          rw [hremi] at hgrt
          exact GrPredParam.mk hid hgrt

/- Soundness of the pred-param list parsers. -/
mutual
theorem parsePredParamList_sound {fuel st ps st'} :
    parsePredParamList fuel st = .ok (ps, st') →
    GrSepList GrPredParam st.remaining ps st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parsePredParamList at h
    simp only at h
    split at h
    · -- rParen: empty
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
    · -- an element
      cases hpp : parsePredParam fuel st with
      | error e => rw [hpp] at h; contradiction
      | ok val =>
        obtain ⟨p, st₁⟩ := val
        rw [hpp] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parsePredParamListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := parsePredParam_sound hpp
          have hgrtail := parsePredParamListTail_sound hpt
          exact GrSepList.cons hgr hgrtail
theorem parsePredParamListTail_sound {fuel st ps st'} :
    parsePredParamListTail fuel st = .ok (ps, st') →
    GrSepListTail GrPredParam st.remaining ps st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parsePredParamListTail at h
    simp only at h
    split at h
    · -- comma
      rename_i hpk
      cases hc : expectTok .comma "','" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpp : parsePredParam fuel st₁ with
        | error e => rw [hpp] at h; contradiction
        | ok val =>
          obtain ⟨p, st₂⟩ := val
          rw [hpp] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parsePredParamListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parsePredParam_sound hpp
            have hgrtail := parsePredParamListTail_sound hpt
            rw [hremc]
            exact GrSepListTail.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
end

/-- Soundness of the predicate-item parser. -/
theorem parsePredicateItem_sound {fuel st p st'} :
    parsePredicateItem fuel st = .ok (p, st') →
    GrPredicateItem st.remaining p st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parsePredicateItem at h
    simp only at h
    cases hp : expectTok .kwPredicate "'predicate'" st with
    | error e => rw [hp] at h; contradiction
    | ok st₁ =>
      rw [hp] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpi : parsePredIdent st₁ with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨x, st₂⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hl : expectTok .lParen "'('" st₂ with
        | error e => rw [hl] at h; contradiction
        | ok st₃ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpp : parsePredParamList fuel st₃ with
          | error e => rw [hpp] at h; contradiction
          | ok val2 =>
            obtain ⟨params, st₄⟩ := val2
            rw [hpp] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rParen "')'" st₄ with
            | error e => rw [hr] at h; contradiction
            | ok st₅ =>
              rw [hr] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hs : expectTok .semi "';'" st₅ with
              | error e => rw [hs] at h; contradiction
              | ok st₆ =>
                rw [hs] at h
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have ⟨hremp, _⟩ := expectTok_remaining hp
                have hremi := parsePredIdent_remaining hpi
                have hid := parsePredIdent_isPredIdent hpi
                have ⟨hreml, _⟩ := expectTok_remaining hl
                have hgr := parsePredParamList_sound hpp
                have ⟨hremr, _⟩ := expectTok_remaining hr
                have ⟨hrems, _⟩ := expectTok_remaining hs
                rw [hremr, hrems] at hgr
                rw [hremp, hremi, hreml]
                exact GrPredicateItem.mk hid hgr

/-- Soundness of the par-decl-item parser. -/
theorem parseParDeclItem_sound {fuel st d st'} :
    parseParDeclItem fuel st = .ok (d, st') →
    GrParDeclItem st.remaining d st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseParDeclItem at h
    simp only at h
    split at h
    · -- array
      rename_i hpk
      cases ha : expectTok .kwArray "'array'" st with
      | error e => rw [ha] at h; contradiction
      | ok st₁ =>
        rw [ha] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hl : expectTok .lBrack "'['" st₁ with
        | error e => rw [hl] at h; contradiction
        | ok st₂ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi : parseIndexSet st₂ with
          | error e => rw [hpi] at h; contradiction
          | ok val =>
            obtain ⟨idx, st₃⟩ := val
            rw [hpi] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rBrack "']'" st₃ with
            | error e => rw [hr] at h; contradiction
            | ok st₄ =>
              rw [hr] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases ho : expectTok .kwOf "'of'" st₄ with
              | error e => rw [ho] at h; contradiction
              | ok st₅ =>
                rw [ho] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hpt : parseBasicParType fuel st₅ with
                | error e => rw [hpt] at h; contradiction
                | ok val2 =>
                  obtain ⟨t, st₆⟩ := val2
                  rw [hpt] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases hc : expectTok .colon "':'" st₆ with
                  | error e => rw [hc] at h; contradiction
                  | ok st₇ =>
                    rw [hc] at h
                    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                    cases hpi2 : parseIdent st₇ with
                    | error e => rw [hpi2] at h; contradiction
                    | ok val3 =>
                      obtain ⟨x, st₈⟩ := val3
                      rw [hpi2] at h
                      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                      cases he : expectTok .eq "'='" st₈ with
                      | error e => rw [he] at h; contradiction
                      | ok st₉ =>
                        rw [he] at h
                        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                        cases hpv : parseParArrayLiteral fuel st₉ with
                        | error e => rw [hpv] at h; contradiction
                        | ok val4 =>
                          obtain ⟨v, st₁₀⟩ := val4
                          rw [hpv] at h
                          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                          cases hs : expectTok .semi "';'" st₁₀ with
                          | error e => rw [hs] at h; contradiction
                          | ok st₁₁ =>
                            rw [hs] at h
                            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                            obtain ⟨rfl, rfl⟩ := h
                            have ⟨hrema, _⟩ := expectTok_remaining ha
                            have ⟨hreml, _⟩ := expectTok_remaining hl
                            have hgridx := parseIndexSet_sound hpi
                            have ⟨hremr, _⟩ := expectTok_remaining hr
                            have ⟨hremo, _⟩ := expectTok_remaining ho
                            have hgrt := parseBasicParType_sound hpt
                            have ⟨hremc, _⟩ := expectTok_remaining hc
                            have hremi := parseIdent_remaining hpi2
                            have ⟨hreme, _⟩ := expectTok_remaining he
                            have hgrv := parseParArrayLiteral_sound hpv
                            have ⟨hrems, _⟩ := expectTok_remaining hs
                            rw [hremr, hremo] at hgridx
                            rw [hremc, hremi, hreme] at hgrt
                            rw [hrems] at hgrv
                            rw [hrema, hreml]
                            exact GrParDeclItem.array hgridx hgrt hgrv
    · -- basic
      cases hpt : parseBasicParType fuel st with
      | error e => rw [hpt] at h; contradiction
      | ok val =>
        obtain ⟨t, st₁⟩ := val
        rw [hpt] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hc : expectTok .colon "':'" st₁ with
        | error e => rw [hc] at h; contradiction
        | ok st₂ =>
          rw [hc] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi : parseIdent st₂ with
          | error e => rw [hpi] at h; contradiction
          | ok val2 =>
            obtain ⟨x, st₃⟩ := val2
            rw [hpi] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases he : expectTok .eq "'='" st₃ with
            | error e => rw [he] at h; contradiction
            | ok st₄ =>
              rw [he] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hpv : parseBasicLiteral fuel st₄ with
              | error e => rw [hpv] at h; contradiction
              | ok val3 =>
                obtain ⟨v, st₅⟩ := val3
                rw [hpv] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hs : expectTok .semi "';'" st₅ with
                | error e => rw [hs] at h; contradiction
                | ok st₆ =>
                  rw [hs] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hgrt := parseBasicParType_sound hpt
                  have ⟨hremc, _⟩ := expectTok_remaining hc
                  have hremi := parseIdent_remaining hpi
                  have ⟨hreme, _⟩ := expectTok_remaining he
                  have hgrv := parseBasicLiteral_sound hpv
                  have ⟨hrems, _⟩ := expectTok_remaining hs
                  rw [hremc] at hgrt
                  rw [hreme] at hremi
                  rw [hrems] at hgrv
                  rw [hremi] at hgrt
                  exact GrParDeclItem.basic hgrt hgrv

/-- Soundness of the var-decl-item parser. -/
theorem parseVarDeclItem_sound {fuel st d st'} :
    parseVarDeclItem fuel st = .ok (d, st') →
    GrVarDeclItem st.remaining d st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseVarDeclItem at h
    simp only at h
    split at h
    · -- array
      rename_i hpk
      cases ha : expectTok .kwArray "'array'" st with
      | error e => rw [ha] at h; contradiction
      | ok st₁ =>
        rw [ha] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hl : expectTok .lBrack "'['" st₁ with
        | error e => rw [hl] at h; contradiction
        | ok st₂ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi : parseIndexSet st₂ with
          | error e => rw [hpi] at h; contradiction
          | ok val =>
            obtain ⟨idx, st₃⟩ := val
            rw [hpi] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rBrack "']'" st₃ with
            | error e => rw [hr] at h; contradiction
            | ok st₄ =>
              rw [hr] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases ho : expectTok .kwOf "'of'" st₄ with
              | error e => rw [ho] at h; contradiction
              | ok st₅ =>
                rw [ho] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hpt : parseBasicVarType fuel st₅ with
                | error e => rw [hpt] at h; contradiction
                | ok val2 =>
                  obtain ⟨t, st₆⟩ := val2
                  rw [hpt] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases hc : expectTok .colon "':'" st₆ with
                  | error e => rw [hc] at h; contradiction
                  | ok st₇ =>
                    rw [hc] at h
                    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                    cases hpi2 : parseIdent st₇ with
                    | error e => rw [hpi2] at h; contradiction
                    | ok val3 =>
                      obtain ⟨x, st₈⟩ := val3
                      rw [hpi2] at h
                      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                      cases hpa : parseAnnotations fuel st₈ with
                      | error e => rw [hpa] at h; contradiction
                      | ok val4 =>
                        obtain ⟨anns, st₉⟩ := val4
                        rw [hpa] at h
                        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                        cases he : expectTok .eq "'='" st₉ with
                        | error e => rw [he] at h; contradiction
                        | ok st₁₀ =>
                          rw [he] at h
                          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                          cases hpv : parseArrayLiteral fuel st₁₀ with
                          | error e => rw [hpv] at h; contradiction
                          | ok val5 =>
                            obtain ⟨elems, st₁₁⟩ := val5
                            rw [hpv] at h
                            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                            cases hs : expectTok .semi "';'" st₁₁ with
                            | error e => rw [hs] at h; contradiction
                            | ok st₁₂ =>
                              rw [hs] at h
                              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                              obtain ⟨rfl, rfl⟩ := h
                              have ⟨hrema, _⟩ := expectTok_remaining ha
                              have ⟨hreml, _⟩ := expectTok_remaining hl
                              have hgridx := parseIndexSet_sound hpi
                              have ⟨hremr, _⟩ := expectTok_remaining hr
                              have ⟨hremo, _⟩ := expectTok_remaining ho
                              have hgrt := parseBasicVarType_sound hpt
                              have ⟨hremc, _⟩ := expectTok_remaining hc
                              have hremi := parseIdent_remaining hpi2
                              have hgra := parseAnnotations_sound hpa
                              have ⟨hreme, _⟩ := expectTok_remaining he
                              have ⟨mid, hmid, hgrv⟩ := parseArrayLiteral_sound hpv
                              have ⟨hrems, _⟩ := expectTok_remaining hs
                              rw [hremr, hremo] at hgridx
                              rw [hremc, hremi] at hgrt
                              rw [hreme, hmid] at hgra
                              rw [hrems] at hgrv
                              rw [hrema, hreml]
                              exact GrVarDeclItem.array hgridx hgrt hgra hgrv
    · -- basic
      cases hpt : parseBasicVarType fuel st with
      | error e => rw [hpt] at h; contradiction
      | ok val =>
        obtain ⟨t, st₁⟩ := val
        rw [hpt] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hc : expectTok .colon "':'" st₁ with
        | error e => rw [hc] at h; contradiction
        | ok st₂ =>
          rw [hc] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpi : parseIdent st₂ with
          | error e => rw [hpi] at h; contradiction
          | ok val2 =>
            obtain ⟨x, st₃⟩ := val2
            rw [hpi] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hpa : parseAnnotations fuel st₃ with
            | error e => rw [hpa] at h; contradiction
            | ok val3 =>
              obtain ⟨anns, st₄⟩ := val3
              rw [hpa] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              split at h
              · -- with assignment
                rename_i hpk2
                cases he : expectTok .eq "'='" st₄ with
                | error e => rw [he] at h; contradiction
                | ok st₅ =>
                  rw [he] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases hpv : parseBasicExpr fuel st₅ with
                  | error e => rw [hpv] at h; contradiction
                  | ok val4 =>
                    obtain ⟨v, st₆⟩ := val4
                    rw [hpv] at h
                    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                    cases hs : expectTok .semi "';'" st₆ with
                    | error e => rw [hs] at h; contradiction
                    | ok st₇ =>
                      rw [hs] at h
                      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hgrt := parseBasicVarType_sound hpt
                      have ⟨hremc, _⟩ := expectTok_remaining hc
                      have hremi := parseIdent_remaining hpi
                      have hgra := parseAnnotations_sound hpa
                      have ⟨hreme, _⟩ := expectTok_remaining he
                      have hgrv := parseBasicExpr_sound hpv
                      have ⟨hrems, _⟩ := expectTok_remaining hs
                      rw [hremc, hremi] at hgrt
                      rw [hreme] at hgra
                      rw [hrems] at hgrv
                      exact GrVarDeclItem.basicAssign hgrt hgra hgrv
              · -- no assignment
                rename_i hpk2
                cases hs : expectTok .semi "';'" st₄ with
                | error e => rw [hs] at h; contradiction
                | ok st₅ =>
                  rw [hs] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hgrt := parseBasicVarType_sound hpt
                  have ⟨hremc, _⟩ := expectTok_remaining hc
                  have hremi := parseIdent_remaining hpi
                  have hgra := parseAnnotations_sound hpa
                  have ⟨hrems, _⟩ := expectTok_remaining hs
                  rw [hremc, hremi] at hgrt
                  rw [hrems] at hgra
                  exact GrVarDeclItem.basicNoAssign hgrt hgra

/- Soundness of the expression-list parsers (for constraint arguments). -/
mutual
theorem parseExprList_sound {fuel st es st'} :
    parseExprList fuel st = .ok (es, st') →
    GrSepList GrExpr st.remaining es st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseExprList at h
    simp only at h
    split at h
    · -- rParen: empty
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepList.nil
    · -- an element
      cases hpe : parseExpr fuel st with
      | error e => rw [hpe] at h; contradiction
      | ok val =>
        obtain ⟨e, st₁⟩ := val
        rw [hpe] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpt : parseExprListTail fuel st₁ with
        | error e => rw [hpt] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpt] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := parseExpr_sound hpe
          have hgrtail := parseExprListTail_sound hpt
          exact GrSepList.cons hgr hgrtail
theorem parseExprListTail_sound {fuel st es st'} :
    parseExprListTail fuel st = .ok (es, st') →
    GrSepListTail GrExpr st.remaining es st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseExprListTail at h
    simp only at h
    split at h
    · -- comma
      rename_i hpk
      cases hc : expectTok .comma "','" st with
      | error e => rw [hc] at h; contradiction
      | ok st₁ =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpe : parseExpr fuel st₁ with
        | error e => rw [hpe] at h; contradiction
        | ok val =>
          obtain ⟨e, st₂⟩ := val
          rw [hpe] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpt : parseExprListTail fuel st₂ with
          | error e => rw [hpt] at h; contradiction
          | ok val2 =>
            obtain ⟨rest, st₃⟩ := val2
            rw [hpt] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ⟨hremc, _⟩ := expectTok_remaining hc
            have hgr := parseExpr_sound hpe
            have hgrtail := parseExprListTail_sound hpt
            rw [hremc]
            exact GrSepListTail.cons hgr hgrtail
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrSepListTail.nil
end

/-- Soundness of the constraint-item parser. -/
theorem parseConstraintItem_sound {fuel st c st'} :
    parseConstraintItem fuel st = .ok (c, st') →
    GrConstraintItem st.remaining c st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseConstraintItem at h
    simp only at h
    cases hc : expectTok .kwConstraint "'constraint'" st with
    | error e => rw [hc] at h; contradiction
    | ok st₁ =>
      rw [hc] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpi : parsePredIdent st₁ with
      | error e => rw [hpi] at h; contradiction
      | ok val =>
        obtain ⟨x, st₂⟩ := val
        rw [hpi] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hl : expectTok .lParen "'('" st₂ with
        | error e => rw [hl] at h; contradiction
        | ok st₃ =>
          rw [hl] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hpe : parseExprList fuel st₃ with
          | error e => rw [hpe] at h; contradiction
          | ok val2 =>
            obtain ⟨args, st₄⟩ := val2
            rw [hpe] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hr : expectTok .rParen "')'" st₄ with
            | error e => rw [hr] at h; contradiction
            | ok st₅ =>
              rw [hr] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hpa : parseAnnotations fuel st₅ with
              | error e => rw [hpa] at h; contradiction
              | ok val3 =>
                obtain ⟨anns, st₆⟩ := val3
                rw [hpa] at h
                simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hs : expectTok .semi "';'" st₆ with
                | error e => rw [hs] at h; contradiction
                | ok st₇ =>
                  rw [hs] at h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have ⟨hremc, _⟩ := expectTok_remaining hc
                  have hremi := parsePredIdent_remaining hpi
                  have hid := parsePredIdent_isPredIdent hpi
                  have ⟨hreml, _⟩ := expectTok_remaining hl
                  have hgr := parseExprList_sound hpe
                  have ⟨hremr, _⟩ := expectTok_remaining hr
                  have hgra := parseAnnotations_sound hpa
                  have ⟨hrems, _⟩ := expectTok_remaining hs
                  rw [hremr] at hgr
                  rw [hrems] at hgra
                  rw [hremc, hremi, hreml]
                  exact GrConstraintItem.mk hid hgr hgra

/-- Soundness of the solve-item parser. -/
theorem parseSolveItem_sound {fuel st si st'} :
    parseSolveItem fuel st = .ok (si, st') →
    GrSolveItem st.remaining si st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseSolveItem at h
    simp only at h
    cases hs : expectTok .kwSolve "'solve'" st with
    | error e => rw [hs] at h; contradiction
    | ok st₁ =>
      rw [hs] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpa : parseAnnotations fuel st₁ with
      | error e => rw [hpa] at h; contradiction
      | ok val =>
        obtain ⟨anns, st₂⟩ := val
        rw [hpa] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        have ⟨hrems, _⟩ := expectTok_remaining hs
        have hgra := parseAnnotations_sound hpa
        split at h
        · -- satisfy
          rename_i hpk
          cases hsat : expectTok .kwSatisfy "'satisfy'" st₂ with
          | error e => rw [hsat] at h; contradiction
          | ok st₃ =>
            rw [hsat] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hsemi : expectTok .semi "';'" st₃ with
            | error e => rw [hsemi] at h; contradiction
            | ok st₄ =>
              rw [hsemi] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ⟨hrem1, _⟩ := expectTok_remaining hsat
              have ⟨hrem2, _⟩ := expectTok_remaining hsemi
              rw [hrem1, hrem2] at hgra
              rw [hrems]
              exact GrSolveItem.satisfy hgra
        · -- minimize
          rename_i hpk
          cases hm : expectTok .kwMinimize "'minimize'" st₂ with
          | error e => rw [hm] at h; contradiction
          | ok st₃ =>
            rw [hm] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hpe : parseBasicExpr fuel st₃ with
            | error e => rw [hpe] at h; contradiction
            | ok val2 =>
              obtain ⟨e, st₄⟩ := val2
              rw [hpe] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hsemi : expectTok .semi "';'" st₄ with
              | error e => rw [hsemi] at h; contradiction
              | ok st₅ =>
                rw [hsemi] at h
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have ⟨hrem1, _⟩ := expectTok_remaining hm
                have hgre := parseBasicExpr_sound hpe
                have ⟨hrem2, _⟩ := expectTok_remaining hsemi
                rw [hrem1] at hgra
                rw [hrem2] at hgre
                rw [hrems]
                exact GrSolveItem.minimize hgra hgre
        · -- maximize
          rename_i hpk
          cases hm : expectTok .kwMaximize "'maximize'" st₂ with
          | error e => rw [hm] at h; contradiction
          | ok st₃ =>
            rw [hm] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hpe : parseBasicExpr fuel st₃ with
            | error e => rw [hpe] at h; contradiction
            | ok val2 =>
              obtain ⟨e, st₄⟩ := val2
              rw [hpe] at h
              simp only [Bind.bind, Except.bind, pure, Except.pure] at h
              cases hsemi : expectTok .semi "';'" st₄ with
              | error e => rw [hsemi] at h; contradiction
              | ok st₅ =>
                rw [hsemi] at h
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have ⟨hrem1, _⟩ := expectTok_remaining hm
                have hgre := parseBasicExpr_sound hpe
                have ⟨hrem2, _⟩ := expectTok_remaining hsemi
                rw [hrem1] at hgra
                rw [hrem2] at hgre
                rw [hrems]
                exact GrSolveItem.maximize hgra hgre
        · contradiction

/-- Soundness of `parseMany`: a run of items parses to a `GrItemList`. -/
theorem parseMany_sound {start : State → Bool}
    {parseOne : Nat → State → Except String (α × State)}
    {gr : List Token → α → List Token → Prop}
    (sound : ∀ {fuel st x st'}, parseOne fuel st = .ok (x, st') →
      gr st.remaining x st'.remaining)
    {fuel st xs st'} :
    parseMany start parseOne fuel st = .ok (xs, st') →
    GrItemList gr st.remaining xs st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseMany at h
    simp only at h
    split at h
    · -- start holds: parse one item, then the rest
      rename_i hstart
      cases hpo : parseOne fuel st with
      | error e => rw [hpo] at h; contradiction
      | ok val =>
        obtain ⟨x, st₁⟩ := val
        rw [hpo] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hpm : parseMany start parseOne fuel st₁ with
        | error e => rw [hpm] at h; contradiction
        | ok val2 =>
          obtain ⟨rest, st₂⟩ := val2
          rw [hpm] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hgr := sound hpo
          have hgrtail := parseMany_sound sound hpm
          exact GrItemList.cons hgr hgrtail
    · -- start fails: empty list
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GrItemList.nil

/-- Soundness of the model parser. -/
theorem parseModelAux_sound {fuel st m st'} :
    parseModelAux fuel st = .ok (m, st') →
    GrModel st.remaining m st'.remaining := by
  intro h
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold parseModelAux at h
    simp only at h
    cases hpp : parseMany atPredicate parsePredicateItem fuel st with
    | error e => rw [hpp] at h; contradiction
    | ok val =>
      obtain ⟨preds, st₁⟩ := val
      rw [hpp] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      cases hpar : parseMany atParDecl parseParDeclItem fuel st₁ with
      | error e => rw [hpar] at h; contradiction
      | ok val2 =>
        obtain ⟨params, st₂⟩ := val2
        rw [hpar] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        cases hvar : parseMany atVarDecl parseVarDeclItem fuel st₂ with
        | error e => rw [hvar] at h; contradiction
        | ok val3 =>
          obtain ⟨vars, st₃⟩ := val3
          rw [hvar] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure] at h
          cases hcon : parseMany atConstraint parseConstraintItem fuel st₃ with
          | error e => rw [hcon] at h; contradiction
          | ok val4 =>
            obtain ⟨cons, st₄⟩ := val4
            rw [hcon] at h
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hsol : parseSolveItem fuel st₄ with
            | error e => rw [hsol] at h; contradiction
            | ok val5 =>
              obtain ⟨solve, st₅⟩ := val5
              rw [hsol] at h
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hgr1 := parseMany_sound (fun h => parsePredicateItem_sound h) hpp
              have hgr2 := parseMany_sound (fun h => parseParDeclItem_sound h) hpar
              have hgr3 := parseMany_sound (fun h => parseVarDeclItem_sound h) hvar
              have hgr4 := parseMany_sound (fun h => parseConstraintItem_sound h) hcon
              have hgr5 := parseSolveItem_sound hsol
              exact GrModel.mk hgr1 hgr2 hgr3 hgr4 hgr5

/-! ## Top-level correctness theorem -/

/-- **Soundness**: if the parser succeeds on a string, the string derives the
    produced model according to the grammar. -/
theorem parseModel_sound {s : String} {m : Model}
    (h : parseModel s = .ok m) : Grammar s m := by
  unfold parseModel parseModelTokens at h
  split at h
  · contradiction
  · rename_i toks htok
    split at h
    · rename_i m' st haux
      split at h
      · rename_i hfull
        simp only [Except.ok.injEq] at h
        subst h
        have hgr := parseModelAux_sound haux
        have hrem : st.remaining = [] := by
          simpa only [List.isEmpty_iff] using hfull
        rw [hrem] at hgr
        have hinit : (⟨toks, 0⟩ : State).remaining = toks.toList := by
          unfold State.remaining
          simp
        rw [hinit] at hgr
        exact ⟨toks, htok, hgr⟩
      · contradiction
    · contradiction

/-- The proved direction of the recognition theorem: parser success implies
    syntactic validity. -/
theorem parseModel_ok_implies_valid (s : String) :
    (∃ m, parseModel s = .ok m) → ValidFlatZinc s := by
  rintro ⟨m, hm⟩
  obtain ⟨toks, htok, hgr⟩ := parseModel_sound hm
  exact ⟨toks, m, htok, hgr⟩

end LeanFzn

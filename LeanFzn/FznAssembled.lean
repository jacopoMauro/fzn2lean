import LeanFzn.FznParser
import LeanFzn.FznGrammar
import LeanFzn.FznSuffix
import LeanFzn.FznCompleteness

/-
# Parser Completeness, Assembled

This module assembles the component completeness lemmas of
`FznCompleteness.lean` into the top-level recognition theorems.

## Fuel adequacy

Every component lemma has the shape

```
GrX st.remaining ast rest → 2 * st.remaining.length + K ≤ fuel →
  ∃ st', parseX fuel st = .ok (ast, st') ∧ st'.remaining = rest
```

with a per-parser constant `K` (at most 7, from `parseVarDeclItem`).  The
generic item-list parser `parseMany` needs one extra unit of fuel per item,
and `parseModelAux` itself consumes one unit before descending, giving the
model-level invariant `2 * st.remaining.length + 9 ≤ fuel`.  The top-level
fuel `parseFuel toks = 8 * (toks.size + 1)` satisfies `2 * n + 9 ≤ 8 * (n + 1)`
for every non-empty `n`; non-emptiness holds because every model derivation
consumes at least the `solve` keyword (`GrModel.length_pos`).
-/

namespace LeanFzn

open LeanFzn.Lexer LeanFzn.Parser

/-! ## Head-token lemmas for the item relations -/

/-- A predicate-item derivation starts with the `predicate` keyword. -/
theorem GrPredicateItem.head {toks : List Token} {p : PredicateItem}
    {rest : List Token} (h : GrPredicateItem toks p rest) :
    ∃ ts, toks = .kwPredicate :: ts := by
  cases h with
  | @mk x ts ps r _ _ => exact ⟨_, rfl⟩

/-- A par-decl-item derivation starts with a basic-par-type keyword or
    `array`. -/
theorem GrParDeclItem.head {toks : List Token} {d : ParDeclItem}
    {rest : List Token} (h : GrParDeclItem toks d rest) :
    (∃ ts, toks = .kwBool :: ts) ∨ (∃ ts, toks = .kwInt :: ts) ∨
      (∃ ts, toks = .kwSet :: ts) ∨ (∃ ts, toks = .kwArray :: ts) := by
  cases h with
  | @basic ts₁ t x ts₂ v r ht _ =>
    cases ht with
    | bool => exact Or.inl ⟨_, rfl⟩
    | int => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | setOfInt => exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  | array hi _ _ => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

/-- A var-decl-item derivation starts with `var` or `array`. -/
theorem GrVarDeclItem.head {toks : List Token} {d : VarDeclItem}
    {rest : List Token} (h : GrVarDeclItem toks d rest) :
    (∃ ts, toks = .kwVar :: ts) ∨ (∃ ts, toks = .kwArray :: ts) := by
  cases h with
  | basicNoAssign ht _ =>
    cases ht with
    | parBool => exact Or.inl ⟨_, rfl⟩
    | parInt => exact Or.inl ⟨_, rfl⟩
    | parSetOfInt => exact Or.inl ⟨_, rfl⟩
    | intRange => exact Or.inl ⟨_, rfl⟩
    | intSet _ _ => exact Or.inl ⟨_, rfl⟩
    | setOfIntRange => exact Or.inl ⟨_, rfl⟩
    | setOfIntSet _ => exact Or.inl ⟨_, rfl⟩
  | basicAssign ht _ _ =>
    cases ht with
    | parBool => exact Or.inl ⟨_, rfl⟩
    | parInt => exact Or.inl ⟨_, rfl⟩
    | parSetOfInt => exact Or.inl ⟨_, rfl⟩
    | intRange => exact Or.inl ⟨_, rfl⟩
    | intSet _ _ => exact Or.inl ⟨_, rfl⟩
    | setOfIntRange => exact Or.inl ⟨_, rfl⟩
    | setOfIntSet _ => exact Or.inl ⟨_, rfl⟩
  | array _ _ _ _ => exact Or.inr ⟨.lBrack :: _, rfl⟩

/-- A constraint-item derivation starts with the `constraint` keyword. -/
theorem GrConstraintItem.head {toks : List Token} {c : ConstraintItem}
    {rest : List Token} (h : GrConstraintItem toks c rest) :
    ∃ ts, toks = .kwConstraint :: ts := by
  cases h with
  | mk _ _ _ => exact ⟨_, rfl⟩

/-! ## Start-token predicates on token lists -/

/-- The `k`-th token of a list, if present.  (A named helper so that
    `match` patterns elaborate against `Option Token`.) -/
def tokAt (toks : List Token) (k : Nat) : Option Token := toks[k]?

/-- Look ahead past `array [ <int-lit> .. <int-lit> ] of` in a token
    list, mirroring `arrayElemToken`. -/
def arrayElemTokenToks (toks : List Token) : Option Token :=
  match tokAt toks 0, tokAt toks 1, tokAt toks 2, tokAt toks 3,
        tokAt toks 4, tokAt toks 5, tokAt toks 6 with
  | some .kwArray, some .lBrack, some (.intLit _), some .dotDot,
    some (.intLit _), some .rBrack, some .kwOf => tokAt toks 7
  | _, _, _, _, _, _, _ => none

/-- The token lists that `atPredicate` accepts, as a predicate on the
    remaining token list. -/
def startPredicateToks (toks : List Token) : Bool :=
  match toks.head? with
  | some .kwPredicate => true
  | _ => false

/-- The token lists that `atParDecl` accepts, as a predicate on the
    remaining token list. -/
def startParDeclToks (toks : List Token) : Bool :=
  match toks.head? with
  | some .kwBool | some .kwInt | some .kwSet => true
  | some .kwArray =>
    match arrayElemTokenToks toks with
    | some .kwBool | some .kwInt | some .kwSet => true
    | _ => false
  | _ => false

/-- The token lists that `atVarDecl` accepts, as a predicate on the
    remaining token list. -/
def startVarDeclToks (toks : List Token) : Bool :=
  match toks.head? with
  | some .kwVar => true
  | some .kwArray =>
    match arrayElemTokenToks toks with
    | some .kwVar => true
    | _ => false
  | _ => false

/-- The token lists that `atConstraint` accepts, as a predicate on the
    remaining token list. -/
def startConstraintToks (toks : List Token) : Bool :=
  match toks.head? with
  | some .kwConstraint => true
  | _ => false

/-! ## Bridging `peek?` and `remaining` -/

/-! ## The section predicates agree with the parser's lookahead -/

/-- The `k`-th remaining token is the `pos + k`-th token of the array. -/
theorem remaining_getElem? (st : State) (k : Nat) :
    st.remaining[k]? = st.toks[st.pos + k]? := by
  unfold State.remaining
  rw [List.getElem?_drop, Array.getElem?_toList]

/-- `arrayElemToken` inspects the remaining tokens. -/
theorem arrayElemToken_eq (st : State) :
    arrayElemToken st = arrayElemTokenToks st.remaining := by
  unfold arrayElemToken arrayElemTokenToks tokAt
  rw [remaining_getElem? st 0, remaining_getElem? st 1, remaining_getElem? st 2,
    remaining_getElem? st 3, remaining_getElem? st 4, remaining_getElem? st 5,
    remaining_getElem? st 6, remaining_getElem? st 7]
  simp only [Nat.add_zero]
  rfl

/-- `peek?` is the head of the remaining tokens. -/
theorem peek?_eq_head? (st : State) : st.peek? = st.remaining.head? := by
  cases hcc : st.remaining with
  | nil =>
    have hnone : st.peek? = none := by
      unfold State.peek?
      have hlen : st.remaining.length = 0 := by rw [hcc]; simp
      unfold State.remaining at hlen
      simp only [Array.length_toList, List.length_drop] at hlen
      rw [dif_neg (by omega)]
    rw [hnone]
    rfl
  | cons t r =>
    have hpeek : st.peek? = some t := peek?_eq_of_remaining_cons hcc
    rw [hpeek]
    rfl

theorem atPredicate_iff (st : State) :
    atPredicate st = startPredicateToks st.remaining := by
  unfold atPredicate startPredicateToks
  rw [peek?_eq_head?]
  cases st.remaining with
  | nil => rfl
  | cons t r =>
    cases t <;> rfl

theorem atParDecl_iff (st : State) :
    atParDecl st = startParDeclToks st.remaining := by
  unfold atParDecl startParDeclToks
  rw [peek?_eq_head?, arrayElemToken_eq st]
  cases st.remaining with
  | nil => rfl
  | cons t r =>
    cases t <;> rfl

theorem atVarDecl_iff (st : State) :
    atVarDecl st = startVarDeclToks st.remaining := by
  unfold atVarDecl startVarDeclToks
  rw [peek?_eq_head?, arrayElemToken_eq st]
  cases st.remaining with
  | nil => rfl
  | cons t r =>
    cases t <;> rfl

theorem atConstraint_iff (st : State) :
    atConstraint st = startConstraintToks st.remaining := by
  unfold atConstraint startConstraintToks
  rw [peek?_eq_head?]
  cases st.remaining with
  | nil => rfl
  | cons t r =>
    cases t <;> rfl

/-! ## Completeness of the item-list parser -/

/-- Every par-decl-item derivation starts a par-decl section. -/
theorem GrParDeclItem.starts {toks : List Token} {d : ParDeclItem}
    {rest : List Token} (h : GrParDeclItem toks d rest) :
    startParDeclToks toks = true := by
  cases h with
  | @basic ts₁ t x ts₂ v r ht hv =>
    cases ht with
    | bool => rfl
    | int => rfl
    | setOfInt => rfl
  | @array ts₁ idx ts₂ t x ts₃ v r hi ht hv =>
    cases hi with
    | mk =>
      cases ht with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl

/-- Every var-decl-item derivation starts a var-decl section. -/
theorem GrVarDeclItem.starts {toks : List Token} {d : VarDeclItem}
    {rest : List Token} (h : GrVarDeclItem toks d rest) :
    startVarDeclToks toks = true := by
  cases h with
  | @basicNoAssign ts t x ts₂ a r ht ha =>
    cases ht with
    | parBool => rfl
    | parInt => rfl
    | parSetOfInt => rfl
    | intRange => rfl
    | intSet _ _ => rfl
    | setOfIntRange => rfl
    | setOfIntSet _ => rfl
  | @basicAssign ts t x ts₂ a ts₃ v r ht ha hv =>
    cases ht with
    | parBool => rfl
    | parInt => rfl
    | parSetOfInt => rfl
    | intRange => rfl
    | intSet _ _ => rfl
    | setOfIntRange => rfl
    | setOfIntSet _ => rfl
  | @array ts₁ idx ts₂ t x ts₃ a ts₄ es r hi ht ha hl =>
    cases hi with
    | mk =>
      cases ht with
      | parBool => rfl
      | parInt => rfl
      | parSetOfInt => rfl
      | intRange => rfl
      | intSet _ _ => rfl
      | setOfIntRange => rfl
      | setOfIntSet _ => rfl

/-- **Completeness of `parseMany`**: if the token list derives a list of
    items, each item parser is complete, and the lookahead predicate `start`
    agrees with `startToks` on the remaining tokens, then `parseMany`
    succeeds and leaves exactly `rest`.  Each item consumes at least one
    token, so the recursion terminates and one extra unit of fuel suffices. -/
theorem parseMany_complete {start : State → Bool}
    {parseOne : Nat → State → Except String (α × State)}
    {gr : List Token → α → List Token → Prop}
    {startToks : List Token → Bool} {K : Nat}
    (hstart : ∀ st, start st = startToks st.remaining)
    (hconsumes : ∀ {toks x rest}, gr toks x rest → 1 ≤ toks.length - rest.length)
    (complete : ∀ {fuel st x rest}, gr st.remaining x rest →
      2 * st.remaining.length + K ≤ fuel →
      ∃ st', parseOne fuel st = .ok (x, st') ∧ st'.remaining = rest)
    (hcons : ∀ {toks x rest}, gr toks x rest → startToks toks = true)
    {toks xs rest}
    (h : GrItemList gr toks xs rest)
    (hstop : startToks rest = false) :
    ∀ (fuel : Nat) (st : State), st.remaining = toks →
      2 * st.remaining.length + K + 1 ≤ fuel →
      ∃ st', parseMany start parseOne fuel st = .ok (xs, st') ∧ st'.remaining = rest := by
  induction h with
  | nil =>
    intro fuel st heq hfuel
    refine ⟨st, ?_, heq⟩
    unfold parseMany
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [hstart st, heq]
      simp only [hstop, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  | @cons toks₁ x toks₂ xs toks₃ h₁ h₂ ih =>
    intro fuel st heq hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstart' : start st = true := by
        rw [hstart st, heq]; exact hcons h₁
      have hfuel' : 2 * st.remaining.length + K ≤ fuel := by omega
      have h₁' : gr st.remaining x toks₂ := by rw [heq]; exact h₁
      obtain ⟨st₁, hparse, hrem₁⟩ := complete h₁' hfuel'
      have hfuel'' : 2 * st₁.remaining.length + K + 1 ≤ fuel := by
        have hge := hconsumes h₁
        have hlen : st.remaining.length = toks₁.length := by rw [heq]
        have hlen2 : st₁.remaining.length = toks₂.length := by rw [hrem₁]
        omega
      obtain ⟨st₂, hparse₂, hrem₂⟩ := ih hstop fuel st₁ hrem₁ hfuel''
      refine ⟨st₂, ?_, hrem₂⟩
      unfold parseMany
      simp only [hstart', ↓reduceIte, hparse, hparse₂, Bind.bind, Except.bind,
        pure, Except.pure]

/-! ## Instantiations for the four item kinds -/

/-- Completeness of the predicate-item list parser. -/
theorem parsePredicateItems_complete {fuel st xs rest}
    (h : GrItemList GrPredicateItem st.remaining xs rest)
    (hstop : startPredicateToks rest = false)
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel) :
    ∃ st', parseMany atPredicate parsePredicateItem fuel st = .ok (xs, st') ∧
      st'.remaining = rest :=
  parseMany_complete (startToks := startPredicateToks) (K := 1)
    (fun st => atPredicate_iff st) GrPredicateItem.consumes_pos
    (fun h hfuel => parsePredicateItem_complete h hfuel)
    (fun h => by
      obtain ⟨ts, hts⟩ := h.head
      rw [hts]; rfl)
    h hstop fuel st rfl (by omega)

/-- Completeness of the par-decl-item list parser. -/
theorem parseParDeclItems_complete {fuel st xs rest}
    (h : GrItemList GrParDeclItem st.remaining xs rest)
    (hstop : startParDeclToks rest = false)
    (hfuel : 2 * st.remaining.length + 4 ≤ fuel) :
    ∃ st', parseMany atParDecl parseParDeclItem fuel st = .ok (xs, st') ∧
      st'.remaining = rest :=
  parseMany_complete (startToks := startParDeclToks) (K := 3)
    (fun st => atParDecl_iff st) GrParDeclItem.consumes_pos
    (fun h hfuel => parseParDeclItem_complete h hfuel)
    (fun h => h.starts)
    h hstop fuel st rfl (by omega)

/-- Completeness of the var-decl-item list parser. -/
theorem parseVarDeclItems_complete {fuel st xs rest}
    (h : GrItemList GrVarDeclItem st.remaining xs rest)
    (hstop : startVarDeclToks rest = false)
    (hfuel : 2 * st.remaining.length + 8 ≤ fuel) :
    ∃ st', parseMany atVarDecl parseVarDeclItem fuel st = .ok (xs, st') ∧
      st'.remaining = rest :=
  parseMany_complete (startToks := startVarDeclToks) (K := 7)
    (fun st => atVarDecl_iff st) GrVarDeclItem.consumes_pos
    (fun h hfuel => parseVarDeclItem_complete h hfuel)
    (fun h => h.starts)
    h hstop fuel st rfl (by omega)

/-- Completeness of the constraint-item list parser. -/
theorem parseConstraintItems_complete {fuel st xs rest}
    (h : GrItemList GrConstraintItem st.remaining xs rest)
    (hstop : startConstraintToks rest = false)
    (hfuel : 2 * st.remaining.length + 2 ≤ fuel) :
    ∃ st', parseMany atConstraint parseConstraintItem fuel st = .ok (xs, st') ∧
      st'.remaining = rest :=
  parseMany_complete (startToks := startConstraintToks) (K := 1)
    (fun st => atConstraint_iff st) GrConstraintItem.consumes_pos
    (fun h hfuel => parseConstraintItem_complete h hfuel)
    (fun h => by
      obtain ⟨ts, hts⟩ := h.head
      rw [hts]; rfl)
    h hstop fuel st rfl (by omega)

/-! ## Completeness of the model parser -/

/-- A solve-item derivation starts with the `solve` keyword. -/
theorem GrSolveItem.head {toks : List Token} {si : SolveItem}
    {rest : List Token} (h : GrSolveItem toks si rest) :
    ∃ ts, toks = .kwSolve :: ts := by
  cases h with
  | @satisfy ts a r ha => exact ⟨_, rfl⟩
  | @minimize ts₁ a ts₂ e r ha he => exact ⟨_, rfl⟩
  | @maximize ts₁ a ts₂ e r ha he => exact ⟨_, rfl⟩

/-! ### Length bounds for the fuel invariant -/

/-- An item-list derivation leaves no more tokens than it started with,
    given that each item leaves a suffix. -/
theorem GrItemList.length_le {α : Type}
    {item : List Token → α → List Token → Prop}
    (hsuf : ∀ {t x r}, item t x r → ∃ pre, t = pre ++ r)
    {toks xs rest} (h : GrItemList item toks xs rest) :
    rest.length ≤ toks.length := by
  obtain ⟨pre, hpre⟩ := h.suffix hsuf
  rw [hpre, List.length_append]
  omega

/-- A model derivation consumes at least the `solve` keyword, so its token
    list is non-empty.  This is what makes the top-level fuel
    `8 * (toks.size + 1)` sufficient: `2 * n + 9 ≤ 8 * (n + 1)` holds
    exactly when `1 ≤ n`. -/
theorem GrModel.length_pos {toks : List Token} {m : Model} {rest : List Token}
    (h : GrModel toks m rest) : 1 ≤ toks.length := by
  cases h with
  | @mk preds ts₂ params ts₃ vars ts₄ cons ts₅ solve ts₆
      hp hpar hvar hcon hsol =>
    obtain ⟨pre₄, hpre₄⟩ := hcon.suffix (fun h => h.suffix)
    obtain ⟨pre₃, hpre₃⟩ := hvar.suffix (fun h => h.suffix)
    obtain ⟨pre₂, hpre₂⟩ := hpar.suffix (fun h => h.suffix)
    obtain ⟨pre₁, hpre₁⟩ := hp.suffix (fun h => h.suffix)
    obtain ⟨ts, hts⟩ := hsol.head
    rw [hpre₁, hpre₂, hpre₃, hpre₄, hts]
    simp only [List.length_append, List.length_cons]
    omega

/-- **Completeness of `parseModelAux`**: a model derivation makes the model
    parser succeed, leaving exactly `rest`.  The section boundaries follow
    from the head-token lemmas: after each item section the next section
    starts with a different keyword, and the final section starts with
    `solve`.  `parseModelAux` consumes one unit of fuel itself, so the
    invariant is `2 * len + 9 ≤ fuel`. -/
theorem parseModelAux_complete {fuel st m rest}
    (h : GrModel st.remaining m rest)
    (hfuel : 2 * st.remaining.length + 9 ≤ fuel) :
    ∃ st', parseModelAux fuel st = .ok (m, st') ∧ st'.remaining = rest := by
  cases h with
  | @mk preds ts₂ params ts₃ vars ts₄ cons ts₅ solve ts₆
      hp hpar hvar hcon hsol =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      -- Section boundaries: the head of the next section rules out the
      -- previous section's start tokens (all sections start with distinct
      -- keywords, and the final section starts with `solve`).
      have hstopP : startPredicateToks ts₂ = false := by
        cases hpar with
        | nil =>
          cases hvar with
          | nil =>
            cases hcon with
            | nil =>
              obtain ⟨ts, hts⟩ := hsol.head
              rw [hts]; rfl
            | cons hc _ =>
              obtain ⟨ts, hts⟩ := hc.head
              rw [hts]; rfl
          | cons hv _ =>
            obtain hts | hts := hv.head
            · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
            · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
        | cons hpd _ =>
          obtain hts | hts | hts | hts := hpd.head
          · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
          · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
          · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
          · obtain ⟨ts, hts⟩ := hts; rw [hts]; rfl
      have hstopPar : startParDeclToks ts₃ = false := by
        cases hvar with
        | nil =>
          cases hcon with
          | nil =>
            obtain ⟨ts, hts⟩ := hsol.head
            rw [hts]; rfl
          | cons hc _ =>
            obtain ⟨ts, hts⟩ := hc.head
            rw [hts]; rfl
        | cons hv _ =>
          cases hv with
          | basicNoAssign ht _ => cases ht <;> rfl
          | basicAssign ht _ _ => cases ht <;> rfl
          | array hi ht _ _ =>
            cases hi
            cases ht <;> rfl
      have hstopVar : startVarDeclToks ts₄ = false := by
        cases hcon with
        | nil =>
          obtain ⟨ts, hts⟩ := hsol.head
          rw [hts]; rfl
        | cons hc _ =>
          obtain ⟨ts, hts⟩ := hc.head
          rw [hts]; rfl
      have hstopCon : startConstraintToks ts₅ = false := by
        obtain ⟨ts, hts⟩ := hsol.head
        rw [hts]; rfl
      -- Length bounds for the fuel invariant
      have hlen₁ : ts₂.length ≤ st.remaining.length :=
        hp.length_le (fun h => h.suffix)
      have hlen₂ : ts₃.length ≤ st.remaining.length := by
        have h2 := hpar.length_le (fun h => h.suffix)
        omega
      have hlen₃ : ts₄.length ≤ st.remaining.length := by
        have h2 := hpar.length_le (fun h => h.suffix)
        have h3 := hvar.length_le (fun h => h.suffix)
        omega
      have hlen₄ : ts₅.length ≤ st.remaining.length := by
        have h2 := hpar.length_le (fun h => h.suffix)
        have h3 := hvar.length_le (fun h => h.suffix)
        have h4 := hcon.length_le (fun h => h.suffix)
        omega
      -- Run the four item sections and the solve item
      obtain ⟨st₁, hparse₁, hrem₁⟩ :=
        parsePredicateItems_complete (fuel := fuel) hp hstopP (by omega)
      have hpar₁ : GrItemList GrParDeclItem st₁.remaining params ts₃ := by
        rw [hrem₁]; exact hpar
      obtain ⟨st₂, hparse₂, hrem₂⟩ :=
        parseParDeclItems_complete (fuel := fuel) hpar₁ hstopPar
          (by rw [hrem₁]; omega)
      have hvar₁ : GrItemList GrVarDeclItem st₂.remaining vars ts₄ := by
        rw [hrem₂]; exact hvar
      obtain ⟨st₃, hparse₃, hrem₃⟩ :=
        parseVarDeclItems_complete (fuel := fuel) hvar₁ hstopVar
          (by rw [hrem₂]; omega)
      have hcon₁ : GrItemList GrConstraintItem st₃.remaining cons ts₅ := by
        rw [hrem₃]; exact hcon
      obtain ⟨st₄, hparse₄, hrem₄⟩ :=
        parseConstraintItems_complete (fuel := fuel) hcon₁ hstopCon
          (by rw [hrem₃]; omega)
      have hsol₁ : GrSolveItem st₄.remaining solve rest := by
        rw [hrem₄]; exact hsol
      obtain ⟨st₅, hparse₅, hrem₅⟩ :=
        parseSolveItem_complete (fuel := fuel) hsol₁ (by rw [hrem₄]; omega)
      refine ⟨st₅, ?_, hrem₅⟩
      unfold parseModelAux
      simp only
      simp only [hparse₁, hparse₂, hparse₃, hparse₄, hparse₅, Bind.bind,
        Except.bind, pure, Except.pure]

/-! ## The recognition theorem -/

/-- **Completeness of `parseModel`**: every grammatically valid string
    parses to exactly its derived model. -/
theorem parseModel_complete {s : String} {m : Model}
    (h : Grammar s m) : Parser.parseModel s = .ok m := by
  obtain ⟨toks, htok, hgr⟩ := h
  have hsize : toks.toList.length = toks.size := Array.length_toList
  have hpos : 1 ≤ toks.size := by
    rw [← hsize]
    exact GrModel.length_pos hgr
  have hfuel : 2 * toks.toList.length + 9 ≤ parseFuel toks := by
    unfold parseFuel
    rw [hsize]
    omega
  have hinit : (⟨toks, 0⟩ : State).remaining = toks.toList := by
    unfold State.remaining
    simp
  obtain ⟨st', haux, hrem⟩ := parseModelAux_complete (fuel := parseFuel toks)
    (st := ⟨toks, 0⟩) (m := m) (rest := []) (by rw [hinit]; exact hgr)
    (by rw [hinit]; exact hfuel)
  have hempty : st'.remaining = [] := hrem
  -- translate to the O(1) end check used by `parseModelTokens`
  have hend : ¬ (st'.pos < st'.toks.size) := by
    have hlen : st'.toks.toList.length = st'.toks.size :=
      (Array.size_eq_length_toList (xs := st'.toks)).symm
    have hle : st'.toks.toList.length ≤ st'.pos := by
      unfold State.remaining at hempty
      exact (List.drop_eq_nil_iff (l := st'.toks.toList) (i := st'.pos)).mp hempty
    omega
  unfold parseModel
  simp only [htok]
  unfold parseModelTokens
  simp only [haux, hend, ↓reduceIte]

/-- **Recognition theorem**: the parser succeeds on exactly the valid
    FlatZinc strings. -/
theorem parseModel_ok_iff_valid (s : String) :
    (∃ m, Parser.parseModel s = .ok m) ↔ ValidFlatZinc s := by
  constructor
  · exact parseModel_ok_implies_valid s
  · rintro ⟨toks, m, htok, hgr⟩
    exact ⟨m, parseModel_complete ⟨toks, htok, hgr⟩⟩

end LeanFzn

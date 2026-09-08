import LeanFzn.FznAST
import LeanFzn.FznLexer

/-
# FlatZinc Grammar as a Derivability Relation (integer/Boolean fragment)

An independent, declarative specification of the FlatZinc grammar as an
inductive family of relations between token lists and ASTs, mirroring the BNF
of `fzn-grammar.mzn`.  `Gr* toks ast rest` reads: "the prefix of the token
list `toks` derives `ast`, leaving the unconsumed suffix `rest`".

A whole model is derived by `GrModel toks m []` (all tokens consumed).

A string is valid FlatZinc iff its tokenization derives a model:

    ValidFlatZinc s ↔ ∃ toks m, tokenize s = .ok toks ∧ GrModel toks m []

This is the reference against which the parser is proved sound and complete
in `FznCorrectness.lean`.
-/

namespace LeanFzn

open LeanFzn.Lexer

/- Comma-separated lists with a trailing context.  `GrSepList elem toks xs rest`
   derives the list `xs` of `elem`s from a prefix of `toks`, leaving `rest`.
   Elements are separated by `.comma`.  Right-recursive: each element is
   followed by an optional `","` and the rest of the list. -/
mutual
inductive GrSepList (elem : List Token → α → List Token → Prop) :
    List Token → List α → List Token → Prop where
  | nil : GrSepList elem toks [] toks
  | cons : elem toks₁ x toks₂ → GrSepListTail elem toks₂ xs toks₃ →
      GrSepList elem toks₁ (x :: xs) toks₃

/-- The tail of a comma-separated list: either nothing, or `","` then more. -/
inductive GrSepListTail (elem : List Token → α → List Token → Prop) :
    List Token → List α → List Token → Prop where
  | nil : GrSepListTail elem toks [] toks
  | cons : elem toks₁ x toks₂ → GrSepListTail elem toks₂ xs rest →
      GrSepListTail elem (.comma :: toks₁) (x :: xs) rest
end

/- The grammar relations, one per non-terminal, in a single mutual block. -/
mutual

/-- `<basic-literal-expr>` (int fragment). -/
inductive GrBasicLiteral : List Token → BasicLiteral → List Token → Prop where
  | bool : GrBasicLiteral (.boolLit b :: rest) (.bool b) rest
  | int  : GrBasicLiteral (.intLit i :: rest) (.int i) rest
  | intRange : GrBasicLiteral (.intLit lo :: .dotDot :: .intLit hi :: rest)
      (.set (.intRange lo hi)) rest
  | intSet : GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrBasicLiteral (.lBrace :: toks) (.set (.intSet elems)) rest

/-- A single integer literal atom (element of an int set). -/
inductive GrIntAtom : List Token → Int → List Token → Prop where
  | mk : GrIntAtom (.intLit i :: rest) i rest

/-- `<set-literal>` (int fragment). -/
inductive GrSetLiteral : List Token → SetLiteral → List Token → Prop where
  | intRange : GrSetLiteral (.intLit lo :: .dotDot :: .intLit hi :: rest)
      (.intRange lo hi) rest
  | intSet : GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrSetLiteral (.lBrace :: toks) (.intSet elems) rest

/-- `<basic-expr>`. -/
inductive GrBasicExpr : List Token → BasicExpr → List Token → Prop where
  | lit : GrBasicLiteral toks l rest → GrBasicExpr toks (.lit l) rest
  | ident : GrBasicExpr (.ident x :: rest) (.ident ⟨x⟩) rest

/-- `<expr>`. -/
inductive GrExpr : List Token → Expr → List Token → Prop where
  | basic : GrBasicExpr toks b rest → GrExpr toks (.basic b) rest
  | array : GrSepList GrBasicExpr toks elems (.rBrack :: rest) →
      GrExpr (.lBrack :: toks) (.array elems) rest

/-- `<par-array-literal>`. -/
inductive GrParArrayLiteral : List Token → ParArrayLiteral → List Token → Prop where
  | mk : GrSepList GrBasicLiteral toks elems (.rBrack :: rest) →
      GrParArrayLiteral (.lBrack :: toks) elems rest

/-- `<annotation>`. -/
inductive GrAnnotation : List Token → Annotation → List Token → Prop where
  | ident : IsPredIdent x → GrAnnotation (.ident x :: rest) (.ident ⟨x⟩) rest
  | call : IsPredIdent x → args ≠ [] →
      GrSepList GrAnnExpr toks args (.rParen :: rest) →
      GrAnnotation (.ident x :: .lParen :: toks) (.call ⟨x⟩ args) rest

/-- `<ann-expr>`. -/
inductive GrAnnExpr : List Token → AnnExpr → List Token → Prop where
  | lit : GrBasicLiteral toks l rest → GrAnnExpr toks (.lit l) rest
  | ident : GrAnnExpr (.ident x :: rest) (.ident ⟨x⟩) rest
  | string : GrAnnExpr (.stringLit s :: rest) (.string s) rest
  | annCall : IsPredIdent x → args ≠ [] →
      GrSepList GrAnnExpr toks args (.rParen :: rest) →
      GrAnnExpr (.ident x :: .lParen :: toks) (.ann (.call ⟨x⟩ args)) rest
  | array : GrSepList GrAnnExpr toks elems (.rBrack :: rest) →
      GrAnnExpr (.lBrack :: toks) (.array elems) rest

/-- `<annotations>`: a sequence of `"::" <annotation>`. -/
inductive GrAnnotations : List Token → List Annotation → List Token → Prop where
  | nil : GrAnnotations toks [] toks
  | cons : GrAnnotation toks₁ a toks₂ → GrAnnotations toks₂ as toks₃ →
      GrAnnotations (.colonColon :: toks₁) (a :: as) toks₃

/-- `<basic-par-type>` (int fragment). -/
inductive GrBasicParType : List Token → BasicParType → List Token → Prop where
  | bool : GrBasicParType (.kwBool :: rest) .bool rest
  | int : GrBasicParType (.kwInt :: rest) .int rest
  | setOfInt : GrBasicParType (.kwSet :: .kwOf :: .kwInt :: rest) .setOfInt rest

/-- `<basic-var-type>` (int fragment). -/
inductive GrBasicVarType : List Token → BasicVarType → List Token → Prop where
  | parBool : GrBasicVarType (.kwVar :: .kwBool :: rest) (.par .bool) rest
  | parInt : GrBasicVarType (.kwVar :: .kwInt :: rest) (.par .int) rest
  | parSetOfInt : GrBasicVarType (.kwVar :: .kwSet :: .kwOf :: .kwInt :: rest)
      (.par .setOfInt) rest
  | intRange : GrBasicVarType (.kwVar :: .intLit lo :: .dotDot :: .intLit hi :: rest)
      (.intRange lo hi) rest
  | intSet : elems ≠ [] → GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrBasicVarType (.kwVar :: .lBrace :: toks) (.intSet elems) rest
  | setOfIntRange : GrBasicVarType
      (.kwVar :: .kwSet :: .kwOf :: .intLit lo :: .dotDot :: .intLit hi :: rest)
      (.setOfIntRange lo hi) rest
  | setOfIntSet : GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrBasicVarType (.kwVar :: .kwSet :: .kwOf :: .lBrace :: toks) (.setOfIntSet elems) rest

/-- `<index-set> ::= "1" ".." <int-literal>`. -/
inductive GrIndexSet : List Token → IndexSet → List Token → Prop where
  | mk : GrIndexSet (.intLit 1 :: .dotDot :: .intLit hi :: rest) ⟨hi⟩ rest

/-- `<basic-pred-param-type>` (int fragment). -/
inductive GrBasicPredParamType : List Token → BasicPredParamType → List Token → Prop where
  | par : GrBasicParType toks t rest → GrBasicPredParamType toks (.par t) rest
  | var : GrBasicVarType toks t rest → GrBasicPredParamType toks (.var t) rest
  | intRange : GrBasicPredParamType (.intLit lo :: .dotDot :: .intLit hi :: rest)
      (.intRange lo hi) rest
  | intSet : elems ≠ [] → GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrBasicPredParamType (.lBrace :: toks) (.intSet elems) rest
  | setOfIntRange : GrBasicPredParamType
      (.kwSet :: .kwOf :: .intLit lo :: .dotDot :: .intLit hi :: rest)
      (.setOfIntRange lo hi) rest
  | setOfIntSet : GrSepList GrIntAtom toks elems (.rBrace :: rest) →
      GrBasicPredParamType (.kwSet :: .kwOf :: .lBrace :: toks) (.setOfIntSet elems) rest

/-- `<pred-index-set>`. -/
inductive GrPredIndexSet : List Token → PredIndexSet → List Token → Prop where
  | int : GrPredIndexSet (.kwInt :: rest) .int rest
  | range : GrIndexSet toks i rest → GrPredIndexSet toks (.range i) rest

/-- `<pred-param-type>`. -/
inductive GrPredParamType : List Token → PredParamType → List Token → Prop where
  | basic : GrBasicPredParamType toks t rest → GrPredParamType toks (.basic t) rest
  | array : GrPredIndexSet toks₁ idx (.rBrack :: .kwOf :: toks₂) →
      GrBasicPredParamType toks₂ elem rest →
      GrPredParamType (.kwArray :: .lBrack :: toks₁) (.array idx elem) rest

/-- One predicate parameter: `<pred-param-type> ":" <identifier>`. -/
inductive GrPredParam : List Token → PredParam → List Token → Prop where
  | mk : IsPredIdent x → GrPredParamType toks₁ t (.colon :: .ident x :: rest) →
      GrPredParam toks₁ ⟨t, ⟨x⟩⟩ rest

/-- `<predicate-item>`. -/
inductive GrPredicateItem : List Token → PredicateItem → List Token → Prop where
  | mk : IsPredIdent x → GrSepList GrPredParam toks params (.rParen :: .semi :: rest) →
      GrPredicateItem (.kwPredicate :: .ident x :: .lParen :: toks) ⟨⟨x⟩, params⟩ rest

/-- `<par-decl-item>` (int fragment). -/
inductive GrParDeclItem : List Token → ParDeclItem → List Token → Prop where
  | basic : GrBasicParType toks₁ t (.colon :: .ident x :: .eq :: toks₂) →
      GrBasicLiteral toks₂ v (.semi :: rest) →
      GrParDeclItem toks₁ (.basic t ⟨x⟩ v) rest
  | array : GrIndexSet toks₁ idx (.rBrack :: .kwOf :: toks₂) →
      GrBasicParType toks₂ t (.colon :: .ident x :: .eq :: toks₃) →
      GrParArrayLiteral toks₃ v (.semi :: rest) →
      GrParDeclItem (.kwArray :: .lBrack :: toks₁) (.array idx t ⟨x⟩ v) rest

/-- `<var-decl-item>` (int fragment). -/
inductive GrVarDeclItem : List Token → VarDeclItem → List Token → Prop where
  | basicNoAssign : GrBasicVarType toks₁ t (.colon :: .ident x :: toks₂) →
      GrAnnotations toks₂ anns (.semi :: rest) →
      GrVarDeclItem toks₁ (.basic t ⟨x⟩ anns none) rest
  | basicAssign : GrBasicVarType toks₁ t (.colon :: .ident x :: toks₂) →
      GrAnnotations toks₂ anns (.eq :: toks₃) →
      GrBasicExpr toks₃ v (.semi :: rest) →
      GrVarDeclItem toks₁ (.basic t ⟨x⟩ anns (some v)) rest
  | array : GrIndexSet toks₁ idx (.rBrack :: .kwOf :: toks₂) →
      GrBasicVarType toks₂ t (.colon :: .ident x :: toks₃) →
      GrAnnotations toks₃ anns (.eq :: .lBrack :: toks₄) →
      GrSepList GrBasicExpr toks₄ elems (.rBrack :: .semi :: rest) →
      GrVarDeclItem (.kwArray :: .lBrack :: toks₁) (.array ⟨idx, t⟩ ⟨x⟩ anns elems) rest

/-- `<constraint-item>`. -/
inductive GrConstraintItem : List Token → ConstraintItem → List Token → Prop where
  | mk : IsPredIdent x → GrSepList GrExpr toks₁ args (.rParen :: toks₂) →
      GrAnnotations toks₂ anns (.semi :: rest) →
      GrConstraintItem (.kwConstraint :: .ident x :: .lParen :: toks₁) ⟨⟨x⟩, args, anns⟩ rest

/-- `<solve-item>`. -/
inductive GrSolveItem : List Token → SolveItem → List Token → Prop where
  | satisfy : GrAnnotations toks anns (.kwSatisfy :: .semi :: rest) →
      GrSolveItem (.kwSolve :: toks) (.satisfy anns) rest
  | minimize : GrAnnotations toks₁ anns (.kwMinimize :: toks₂) →
      GrBasicExpr toks₂ e (.semi :: rest) →
      GrSolveItem (.kwSolve :: toks₁) (.minimize anns e) rest
  | maximize : GrAnnotations toks₁ anns (.kwMaximize :: toks₂) →
      GrBasicExpr toks₂ e (.semi :: rest) →
      GrSolveItem (.kwSolve :: toks₁) (.maximize anns e) rest

end

/-- A list of items of the same kind, in sequence. -/
inductive GrItemList (item : List Token → α → List Token → Prop) :
    List Token → List α → List Token → Prop where
  | nil : GrItemList item toks [] toks
  | cons : item toks₁ x toks₂ → GrItemList item toks₂ xs toks₃ →
      GrItemList item toks₁ (x :: xs) toks₃

/-- `<model>`: predicates, then parameters, then variables, then constraints,
    then exactly one solve item, consuming all tokens. -/
inductive GrModel : List Token → Model → List Token → Prop where
  | mk : GrItemList GrPredicateItem toks₁ preds toks₂ →
      GrItemList GrParDeclItem toks₂ params toks₃ →
      GrItemList GrVarDeclItem toks₃ vars toks₄ →
      GrItemList GrConstraintItem toks₄ cons toks₅ →
      GrSolveItem toks₅ solve rest →
      GrModel toks₁ ⟨preds, params, vars, cons, solve⟩ rest

/-- A token list is a valid FlatZinc model iff it derives one and is fully
    consumed. -/
def ValidTokens (toks : List Token) : Prop := ∃ m, GrModel toks m []

/-- A string is valid FlatZinc iff its tokenization derives a model. -/
def ValidFlatZinc (s : String) : Prop :=
  ∃ toks m, tokenize s = .ok toks ∧ GrModel toks.toList m []

/-- The grammar judgement relating a string to the model it derives. -/
def Grammar (s : String) (m : Model) : Prop :=
  ∃ toks, tokenize s = .ok toks ∧ GrModel toks.toList m []

/-! ## Determinism at unambiguous grammar leaves -/

theorem GrIntAtom.deterministic
    (h₁ : GrIntAtom toks i₁ rest₁) (h₂ : GrIntAtom toks i₂ rest₂) :
    i₁ = i₂ ∧ rest₁ = rest₂ := by
  cases h₁
  cases h₂
  simp_all

theorem GrBasicParType.deterministic
    (h₁ : GrBasicParType toks t₁ rest₁) (h₂ : GrBasicParType toks t₂ rest₂) :
    t₁ = t₂ ∧ rest₁ = rest₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

end LeanFzn

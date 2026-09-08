/-
# FlatZinc Abstract Syntax Tree

Formalization of the FlatZinc grammar (`fzn-grammar.mzn`, as included in
`specification/flatzinc_specification.rst`, section "Grammar") as Lean 4 inductive types.

Each BNF non-terminal corresponds to one Lean type.  The ordering constraint
of `<model>` (predicate items, then parameter declarations, then variable
declarations, then constraints, then exactly one solve item) is encoded
structurally in `Model`, so every value of type `Model` is well-ordered by
construction.
-/

namespace LeanFzn

/-- `<identifier> ::= [A-Za-z][A-Za-z0-9_]*` and
    `<var-par-identifier> ::= [A-Za-z_][A-Za-z0-9_]*`.
    The distinction (leading underscore allowed) is enforced by the lexer;
    at the AST level both are just names. -/
structure Ident where
  name : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- The lexical distinction used by FlatZinc's `<identifier>` production.
    The lexer has already checked the identifier's characters, so only the
    leading-underscore restriction remains here. -/
def IsPredIdent (x : String) : Prop := x.startsWith "_" = false

/- This development deliberately formalizes the integer/Boolean fragment of
   FlatZinc. Float productions from the full grammar are omitted. -/

/-- Integer set literals, either enumerated or a closed range. -/
inductive SetLiteral where
  | intSet    (elems : List Int)          -- `"{" [ <int-literal> "," ... ] "}"`
  | intRange  (lo hi : Int)               -- `<int-literal> ".." <int-literal>`
  deriving Repr, Inhabited

/-- `<basic-literal-expr>` -/
inductive BasicLiteral where
  | bool  (b : Bool)
  | int   (i : Int)
  | set   (s : SetLiteral)
  deriving Repr, Inhabited

/-- `<basic-expr> ::= <basic-literal-expr> | <var-par-identifier>` -/
inductive BasicExpr where
  | lit  (l : BasicLiteral)
  | ident (x : Ident)
  deriving Repr, Inhabited

/-- `<array-literal> ::= "[" [ <basic-expr> "," ... ] "]"` -/
abbrev ArrayLiteral := List BasicExpr

/-- `<expr> ::= <basic-expr> | <array-literal>` -/
inductive Expr where
  | basic (b : BasicExpr)
  | array (elems : ArrayLiteral)
  deriving Repr, Inhabited

/-- `<par-array-literal> ::= "[" [ <basic-literal-expr> "," ... ] "]"` -/
abbrev ParArrayLiteral := List BasicLiteral

/-- `<basic-par-type>` -/
inductive BasicParType where
  | bool      -- "bool"
  | int       -- "int"
  | setOfInt  -- "set of int"
  deriving Repr, DecidableEq, Inhabited

/-- `<basic-var-type>` -/
inductive BasicVarType where
  | par (t : BasicParType)                -- "var" <basic-par-type>
  | intRange (lo hi : Int)                -- "var" <int-literal> ".." <int-literal>
  | intSet (elems : List Int)             -- "var" "{" <int-literal> "," ... "}"  (non-empty)
  | setOfIntRange (lo hi : Int)           -- "var" "set" "of" <int-literal> ".." <int-literal>
  | setOfIntSet (elems : List Int)        -- "var" "set" "of" "{" [ <int-literal> "," ... ] "}"
  deriving Repr, Inhabited

/-- `<index-set> ::= "1" ".." <int-literal>` -/
structure IndexSet where
  hi : Int
  deriving Repr, DecidableEq, Inhabited

/-- `<array-var-type> ::= "array" "[" <index-set> "]" "of" <basic-var-type>` -/
structure ArrayVarType where
  idx : IndexSet
  elem : BasicVarType
  deriving Repr, Inhabited

/-- `<basic-pred-param-type>` -/
inductive BasicPredParamType where
  | par (t : BasicParType)                -- <basic-par-type>
  | var (t : BasicVarType)                -- <basic-var-type>
  | intRange (lo hi : Int)                -- <int-literal> ".." <int-literal>
  | intSet (elems : List Int)             -- "{" <int-literal> "," ... "}" (non-empty)
  | setOfIntRange (lo hi : Int)           -- "set" "of" <int-literal> ".." <int-literal>
  | setOfIntSet (elems : List Int)        -- "set" "of" "{" [ <int-literal> "," ... ] "}"
  deriving Repr, Inhabited

/-- `<pred-index-set> ::= <index-set> | "int"` -/
inductive PredIndexSet where
  | range (idx : IndexSet)
  | int
  deriving Repr, Inhabited

/-- `<pred-param-type> ::= <basic-pred-param-type>
                          | "array" "[" <pred-index-set> "]" "of" <basic-pred-param-type>` -/
inductive PredParamType where
  | basic (t : BasicPredParamType)
  | array (idx : PredIndexSet) (elem : BasicPredParamType)
  deriving Repr, Inhabited

/-- One parameter of a predicate declaration: `<pred-param-type> ":" <identifier>`. -/
structure PredParam where
  type : PredParamType
  name : Ident
  deriving Repr, Inhabited

/-- `<predicate-item> ::= "predicate" <identifier> "(" [ <pred-param-type> ":"
    <identifier> "," ... ] ")" ";"` -/
structure PredicateItem where
  name : Ident
  params : List PredParam
  deriving Repr, Inhabited

/-- `<par-decl-item>`: either a basic parameter declaration
    `<basic-par-type> ":" <var-par-identifier> "=" <basic-literal-expr> ";"`
    or an array parameter declaration
    `"array" "[" <index-set> "]" "of" <basic-par-type> ":" <var-par-identifier>
     "=" <par-array-literal> ";"`. -/
inductive ParDeclItem where
  | basic (type : BasicParType) (name : Ident) (value : BasicLiteral)
  | array (idx : IndexSet) (elem : BasicParType) (name : Ident)
          (value : ParArrayLiteral)
  deriving Repr, Inhabited

/- `<annotation>` and `<ann-expr>` are mutually recursive (an annotation can
   appear as an annotation argument, without the leading `"::"`).

   `<annotation> ::= <identifier> | <identifier> "(" <ann-expr> "," ... ")"`
   `<ann-expr>   ::= <basic-ann-expr> | "[" [ <basic-ann-expr> "," ... ] "]"` -/
mutual
inductive Annotation where
  | ident (x : Ident)
  | call  (x : Ident) (args : List AnnExpr)
  deriving Repr, Inhabited

inductive AnnExpr where
  | lit    (l : BasicLiteral)
  | ident  (x : Ident)
  | string (s : String)          -- <string-literal> (contents, escapes decoded)
  | ann    (a : Annotation)      -- nested annotation (without leading "::")
  | array  (elems : List AnnExpr)
  deriving Repr, Inhabited
end

/-- `<var-decl-item>` -/
inductive VarDeclItem where
  /-- `<basic-var-type> ":" <var-par-identifier> <annotations>
       [ "=" <basic-expr> ] ";"` -/
  | basic (type : BasicVarType) (name : Ident) (anns : List Annotation)
          (value : Option BasicExpr)
  /-- `<array-var-type> ":" <var-par-identifier> <annotations>
       "=" <array-literal> ";"` -/
  | array (type : ArrayVarType) (name : Ident) (anns : List Annotation)
          (value : ArrayLiteral)
  deriving Repr, Inhabited

/-- `<constraint-item> ::= "constraint" <identifier> "(" [ <expr> "," ... ] ")"
    <annotations> ";"` -/
structure ConstraintItem where
  name : Ident
  args : List Expr
  anns : List Annotation
  deriving Repr, Inhabited

/-- `<solve-item>` -/
inductive SolveItem where
  | satisfy  (anns : List Annotation)                          -- "solve" <annotations> "satisfy" ";"
  | minimize (anns : List Annotation) (obj : BasicExpr)        -- "solve" <annotations> "minimize" <basic-expr> ";"
  | maximize (anns : List Annotation) (obj : BasicExpr)        -- "solve" <annotations> "maximize" <basic-expr> ";"
  deriving Repr, Inhabited

/-- `<model>`: the five sections, in order. -/
structure Model where
  predicates  : List PredicateItem
  parameters  : List ParDeclItem
  variables   : List VarDeclItem
  constraints : List ConstraintItem
  solve       : SolveItem
  deriving Repr, Inhabited

end LeanFzn

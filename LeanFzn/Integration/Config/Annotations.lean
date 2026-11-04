/-
Purpose: Parse source search annotations and construct slot priority/value-order tables.
Dependencies: Compiler.Normalize for array aliases and slot names; shared syntax and model types.
DAG: Compiler -> Config.Annotations -> Core or kernel presentation.
-/
import LeanFzn.Compiler.Normalize

namespace LeanFzn.Integration

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler

/-! ## §1 Reading the solve annotations -/

/-- The value order named by an `indomain_*` annotation.  `none` keeps the
    presentation unchanged. -/
inductive AnnValOrder where
  | min
  | max
  | median
  | split
  | reverseSplit
  /-- Rotate the value at enumeration rank `r` to the front (F3 phase
      saving; the rank is taken in the activity-ordered domain). -/
  | atRank (rank : Nat)
  | none
  deriving Repr, DecidableEq, Inhabited, BEq

/-- One `int_search`/`bool_search` item: its variable names (arrays already
    expanded to their element names), the variable-selection name and the
    requested value order. -/
structure AnnSearch where
  vars : List String
  inputOrder : Bool
  order : AnnValOrder
  deriving Repr, Inhabited

/-- The identifier carried by an annotation expression, if any. -/
def annIdent? : AnnExpr → Option String
  | .ident x => some x.name
  | _ => none

/-- The value order named by an annotation argument. -/
def annValOrder? : AnnExpr → AnnValOrder
  | .ident x =>
      match x.name with
      | "indomain_min" => .min
      | "indomain_max" => .max
      | "indomain_median" => .median
      | "indomain_split" => .split
      | "indomain_reverse_split" => .reverseSplit
      | _ => .none
  | _ => .none

/-- Expand a variable/array name to the element variable names.  An array
    element that is a literal (a fixed value) contributes no search slot. -/
def annVarNames (defs : List (Ident × List BasicExpr)) (x : Ident) : List String :=
  match lookupIdent x defs with
  | some es =>
      es.filterMap fun e =>
        match e with
        | .ident y => some y.name
        | _ => none
  | none => [x.name]

/-- The variable names of one annotation argument.  `[x,y]` is accepted as
    well as an array name. -/
def annExprNames (defs : List (Ident × List BasicExpr)) : AnnExpr → List String
  | .ident x => annVarNames defs x
  | .array es => es.flatMap (annExprNames defs)
  | _ => []

/- Node count of an annotation tree; used as fuel so the recursive
   `seq_search` walk is structurally terminating and never truncates. -/
mutual
def annSize : Annotation → Nat
  | .ident _ => 1
  | .call _ args => 1 + annExprListSize args

def annExprSize : AnnExpr → Nat
  | .lit _ => 1
  | .ident _ => 1
  | .string _ => 1
  | .ann a => 1 + annSize a
  | .array es => 1 + annExprListSize es

def annExprListSize : List AnnExpr → Nat
  | [] => 0
  | e :: es => annExprSize e + annExprListSize es
end

/-- Parse one search annotation into its items, with enough fuel for the
    whole nested tree.  `seq_search` contributes one item per nested search
    annotation, in sequence order (the group order of the priority vector). -/
def parseAnnSearchFuel (defs : List (Ident × List BasicExpr)) :
    Nat → Annotation → List AnnSearch
  | 0, _ => []
  | fuel + 1, .call x args =>
      match x.name, args with
      | "int_search", vars :: varSel :: valSel :: _ =>
          [{ vars := annExprNames defs vars
             inputOrder := annIdent? varSel == some "input_order"
             order := annValOrder? valSel }]
      | "bool_search", vars :: varSel :: valSel :: _ =>
          [{ vars := annExprNames defs vars
             inputOrder := annIdent? varSel == some "input_order"
             order := annValOrder? valSel }]
      | "seq_search", [.array elems] =>
          elems.flatMap fun e =>
            match e with
            | .ann a => parseAnnSearchFuel defs fuel a
            | _ => []
      | _, _ => []
  | _ + 1, .ident _ => []

/-- Parse one search annotation into its items. -/
def parseAnnSearch (defs : List (Ident × List BasicExpr))
    (a : Annotation) : List AnnSearch :=
  parseAnnSearchFuel defs (annSize a) a

/-- The solve item's annotations. -/
def solveAnnotations : SolveItem → List Annotation
  | .satisfy anns => anns
  | .minimize anns _ => anns
  | .maximize anns _ => anns

/-- The annotation search items of a model, in `seq_search` group order. -/
def annSearches (m : Model) : List AnnSearch :=
  (solveAnnotations m.solve).flatMap (parseAnnSearch (arrayDefs m))

/-- Resolve one name to its compiled slot. -/
def annSlot? (names : List String) (x : String) : Option Nat :=
  nameIndex names x

/-! ## §2 Priority vector and value-order table -/

/-- The annotation group base spacing: above `ACT_BOUND` and above every
    group size, so `input_order` offsets stay inside their group band. -/
def annBase (n : Nat) : Nat := max 4096 (n + 1)

/-- One group's contribution: `base + (n - i)` for `input_order`, `base` for
    the other variable choices, at the resolved slots.  A slot mentioned more
    than once keeps its highest score (the earlier group wins). -/
def annGroupPrio (base : Nat) (grp : AnnSearch) (names : List String)
    (acc : List Nat) : List Nat :=
  let n := grp.vars.length
  grp.vars.zipIdx.foldl (init := acc) fun acc (x, i) =>
    match annSlot? names x with
    | none => acc
    | some s =>
        let add := if grp.inputOrder then n - i else 0
        let score := base + add
        if acc.getD s 0 < score then acc.set s score else acc

/-- The group priority vector, in compiled slot order.  Group `g` of `G` gets
    base `(G - g) * annBase`; unannotated slots score 0 and fall back to the
    S1 minimum-cardinality rule. -/
def annotPrio (m : Model) (names : List String) : List Nat :=
  let groups := annSearches m
  let G := groups.length
  let K := annBase names.length
  groups.zipIdx.foldl
    (init := List.replicate names.length 0)
    fun acc (grp, g) => annGroupPrio ((G - g) * K) grp names acc

/-- The per-slot value order table; the first annotation naming a slot wins and
    unannotated slots keep `none`. -/
def annotOrders (m : Model) (names : List String) : List AnnValOrder :=
  (annSearches m).foldl
    (init := List.replicate names.length .none)
    fun acc grp =>
      grp.vars.foldl (init := acc) fun acc x =>
        match annSlot? names x with
        | none => acc
        | some s =>
            if acc.getD s .none == .none then acc.set s grp.order else acc


end LeanFzn.Integration

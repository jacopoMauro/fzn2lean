import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Regular-language and decision-diagram global constraints

Mathematical interpretations (`regularInterp`) and executable Boolean
twins (`regularInterpB`) for the `regular` family of the pinned MiniZinc
2.10.1 tree, per the decompositions recorded in
`specification/flatzinc_specification_assumptions.md`, G27–G28:

* `fzn_regular(xs, Q, S, d, q0, F)` (`fzn_regular.mzn`): DFA
  acceptance.  `d` is the Q×S transition matrix flattened row-major
  (both dimensions given by the sibling par ints `Q` and `S`); states
  `1..Q`; state 0 is the reserved sink (a `d[q,s] = 0` transition
  fails the run); `xs` values must lie in `1..S`; the empty `xs`
  accepts iff `q0 ∈ F`.  `F` is given as a 0/1 indicator array.
* `fzn_regular_nfa(xs, Q, S, d, q0, F)` (`fzn_regular_nfa.mzn`): NFA
  acceptance; `d` is the Q×S matrix of *sets* of target states
  (modelled as a flat row-major list of sets).  Computed as the
  forward set of states reachable from `q0` over `xs`.
* `fzn_cost_regular(xs, Q, S, d, q0, F, cost, total_cost)`
  (`fzn_cost_regular.mzn`): DFA acceptance plus the summed transition
  cost (the Q×S cost matrix, row-major) equals `total_cost`.
* `fzn_mdd(xs, N, level, E, from, label, to)` and
  `fzn_mdd_nondet(...)` (`fzn_mdd.mzn`): satisfying walks in an
  edge-list decision diagram (root 1, true node 0; strictly
  increasing levels; each `xs` value in the label set of the edge
  taken at its level).  The determinism axioms (P1/P4) of `fzn_mdd`
  restrict the diagram, not the satisfying-assignment relation, so
  the twins coincide.
* `fzn_cost_mdd(xs, N, level, E, from, label, cost, to, total_cost)`
  (`fzn_cost_mdd.mzn`): the satisfying-walks condition plus
  `total_cost` equal to the cost of *some* satisfying walk
  (existential reading of the longest-path decomposition).
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Regular

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## Row-major matrix access -/

/-- Row-major access into a flat Q-column matrix: entry (q, s) with
    q, s 1-based; 0 out of range. -/
private def matAt (flat : List Int) (cols : Int) (q s : Int) : Int :=
  flat.getD (((q - 1) * cols + (s - 1)).toNat) 0

/-! ## DFA runs -/

/-- The run function: state after consuming the whole word from
    `start`, failing (none) on sink transitions or bad symbols. -/
private def runFrom (d : List Int) (sigma : Int) : Int → List Int →
    Option Int
  | q, [] => some q
  | q, x :: rest =>
      if q ≤ 0 then none
      else if 1 ≤ x ∧ x ≤ sigma then
        let q' := matAt d sigma q x
        if q' ≤ 0 then none else runFrom d sigma q' rest
      else none

/-- `fzn_regular`: the DFA accepts `xs` from `q0`. -/
def regularProp (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : List Int) : Prop :=
  (runFrom d sigma q0 xs).isSome = true ∧
    decide (1 ≤ q0 ∧ q0 ≤ q) = true ∧
    decide (f.getD ((runFrom d sigma q0 xs).getD 0 - 1).toNat 0 = 1) = true

/-- Boolean twin of `regularProp`. -/
def regularB (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : List Int) : Bool :=
  (runFrom d sigma q0 xs).isSome &&
    decide (1 ≤ q0 ∧ q0 ≤ q) &&
    decide (f.getD ((runFrom d sigma q0 xs).getD 0 - 1).toNat 0 = 1)

theorem regularB_iff (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : List Int) :
    regularB xs q sigma d q0 f = true ↔
      regularProp xs q sigma d q0 f := by
  simp only [regularB, regularProp, Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-! ## NFA runs -/

/-- The set-valued transition matrix (row-major flat list of
    sets). -/
private def setMatAt (flat : List IntSetValue) (cols : Int) (q s : Int) :
    IntSetValue :=
  flat.getD (((q - 1) * cols + (s - 1)).toNat) (.enumeration [])

/-- NFA acceptance: the forward set of states reachable from `q0`
    after consuming all of `xs` (a state already in the frontier is
    kept: self-loops survive). -/
private def nfaFrontier (d : List IntSetValue) (sigma : Int) :
    List Int → List Int → List Int
  | [], frontier => frontier
  | x :: rest, frontier =>
      if 1 ≤ x ∧ x ≤ sigma then
        let next := frontier.foldl (fun acc q =>
          ((setElems (setMatAt d sigma q x)).filter (fun q' =>
            1 ≤ q' ∧ !(acc.contains q')))) []
        let next' := next.filter (fun q' => 1 ≤ q')
        if next'.isEmpty then [] else nfaFrontier d sigma rest next'
      else []

/-- `fzn_regular_nfa`. -/
def nfaProp (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : List Int) : Prop :=
  1 ≤ q0 ∧ q0 ≤ q ∧
    (nfaFrontier d sigma xs [q0]).any (fun q' =>
      f.getD (q' - 1).toNat 0 = 1)

def nfaB (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : List Int) : Bool :=
  decide (1 ≤ q0 ∧ q0 ≤ q) &&
    (nfaFrontier d sigma xs [q0]).any (fun q' =>
      decide (f.getD (q' - 1).toNat 0 = 1))

theorem nfaB_iff (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : List Int) :
    nfaB xs q sigma d q0 f = true ↔ nfaProp xs q sigma d q0 f := by
  simp only [nfaB, nfaProp, Bool.and_eq_true, decide_eq_true_iff]
  rw [and_assoc]

/-! ## Cost regular -/

/-- The state after consuming the first `i` symbols of `xs`. -/
private def runState (d : List Int) (sigma : Int) (q0 : Int)
    (xs : List Int) : Nat → Option Int
  | 0 => some q0
  | i + 1 =>
      match runState d sigma q0 xs i with
      | none => none
      | some q =>
          if q ≤ 0 then none
          else if 1 ≤ xs.getD i 0 ∧ xs.getD i 0 ≤ sigma then
            let q' := matAt d sigma q (xs.getD i 0)
            if q' ≤ 0 then none else some q'
          else none

/-- The cost of the run (0 if the run fails — matching the
    decomposition's accumulator, which is only read when the
    acceptance condition holds). -/
private def runCost (d cost : List Int) (sigma : Int) (q0 : Int)
    (xs : List Int) : Int :=
  match runFrom d sigma q0 xs with
  | some _ =>
      (List.range xs.length).foldl (fun acc i =>
        acc + cost.getD (((runState d sigma q0 xs i).getD 0 - 1) *
            sigma + (xs.getD i 0) - 1).toNat 0) 0
  | none => 0

/-- `fzn_cost_regular`: DFA acceptance plus the summed transition
    cost. -/
def costRegularProp (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f cost : List Int) (total : Int) : Prop :=
  regularProp xs q sigma d q0 f ∧ total = runCost d cost sigma q0 xs

def costRegularB (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f cost : List Int) (total : Int) : Bool :=
  regularB xs q sigma d q0 f && decide (total = runCost d cost sigma q0 xs)

theorem costRegularB_iff (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f cost : List Int) (total : Int) :
    costRegularB xs q sigma d q0 f cost total = true ↔
      costRegularProp xs q sigma d q0 f cost total := by
  simp only [costRegularB, costRegularProp, Bool.and_eq_true,
    regularB_iff, decide_eq_true_iff]

/-! ## MDD -/

/-- The MDD input: edge-list representation. -/
structure MddInput where
  /-- The variables (one per level). -/
  xs : List Int
  /-- Node count (root 1, true node 0). -/
  n : Int
  /-- Level of each node (1-based node ids). -/
  level : List Int
  /-- Edge count. -/
  e : Int
  /-- Source of each edge (1-based). -/
  fromArr : List Int
  /-- Label set of each edge. -/
  label : List IntSetValue
  /-- Target of each edge (0 = true node). -/
  toArr : List Int
  deriving Repr

/-- Source of edge `e` (1-based). -/
private def mddFrom (m : MddInput) (e : Nat) : Int :=
  m.fromArr.getD (e - 1) 0

/-- Target of edge `e` (1-based). -/
private def mddTo (m : MddInput) (e : Nat) : Int :=
  m.toArr.getD (e - 1) 0

/-- Label set of edge `e` (1-based). -/
private def mddLabel (m : MddInput) (e : Nat) : IntSetValue :=
  m.label.getD (e - 1) (.enumeration [])

/-- Level of node `node` (1-based). -/
private def mddLevel (m : MddInput) (node : Nat) : Int :=
  m.level.getD (node - 1) 0

/-- The edges out of `node` (0-based edge indices). -/
private def outEdges (m : MddInput) (node : Nat) : List Nat :=
  (List.range m.e.toNat).filter (fun e =>
    mddFrom m (e + 1) = (node : Int))

/-- Satisfying walks from `node` consuming `xs` from level `lvl`:
    a recursive search.  Returns `some cost` when a walk to T exists
    (with its edge-cost sum), `none` otherwise. -/
private def walkFrom (m : MddInput) (cost : List Int) :
    Nat → List Int → Nat → Option Int
  | node, [], _ =>
      if node == 0 then some 0 else none
  | node, x :: rest, lvl =>
      if node == 0 then none
      else if mddLevel m node ≠ (lvl : Int) then none
      else
        (outEdges m node).foldl (fun acc e =>
          match acc with
          | some c => some c
          | none =>
              if decide (x ∈ setElems (mddLabel m (e + 1))) then
                match walkFrom m cost (mddTo m (e + 1)).toNat rest
                    (lvl + 1) with
                | some c => some (c + cost.getD e 0)
                | none => none
              else none) none

/-- `fzn_mdd` / `fzn_mdd_nondet`: some satisfying walk exists. -/
def mddProp (m : MddInput) : Prop :=
  (walkFrom m (List.replicate m.e.toNat 0) 1 m.xs 1).isSome = true

/-- `fzn_cost_mdd`: some satisfying walk with total cost. -/
def costMddProp (m : MddInput) (cost : List Int) (total : Int) : Prop :=
  walkFrom m cost 1 m.xs 1 = some total

def mddB (m : MddInput) : Bool :=
  (walkFrom m (List.replicate m.e.toNat 0) 1 m.xs 1).isSome

def costMddB (m : MddInput) (cost : List Int) (total : Int) : Bool :=
  decide (walkFrom m cost 1 m.xs 1 = some total)

theorem mddB_iff (m : MddInput) : mddB m = true ↔ mddProp m := by
  simp only [mddB, mddProp]

theorem costMddB_iff (m : MddInput) (cost : List Int) (total : Int) :
    costMddB m cost total = true ↔ costMddProp m cost total := by
  simp only [costMddB, costMddProp, decide_eq_true_iff]

/-! ## Argument decoders -/

/-- Decode the full regular signature: (xs, Q, S, d, q0, F). -/
private def regularArgs (args : List Value) :
    Option (List Int × Int × Int × List Int × Int × List Int) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, Value.array fArr] =>
      match valueInts xsArr, valueInts dArr, valueInts fArr with
      | some xsL, some dL, some fL => some (xsL, q, s, dL, q0, fL)
      | _, _, _ => none
  | _ => none

/-- Decode the NFA signature: (xs, Q, S, d-sets, q0, F). -/
private def nfaArgs (args : List Value) :
    Option (List Int × Int × Int × List IntSetValue × Int × List Int) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, Value.array fArr] =>
      match valueInts xsArr,
        (dArr.mapM (fun v => match v with
          | Value.setOfInt sv => some sv
          | _ => none)), valueInts fArr with
      | some xsL, some dL, some fL => some (xsL, q, s, dL, q0, fL)
      | _, _, _ => none
  | _ => none

/-- Decode the cost-regular signature: (xs, Q, S, d, q0, F, cost,
    total). -/
private def costRegularArgs (args : List Value) :
    Option (List Int × Int × Int × List Int × Int × List Int ×
      List Int × Int) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, Value.array fArr, Value.array costArr,
     Value.int total] =>
      match valueInts xsArr, valueInts dArr, valueInts fArr,
        valueInts costArr with
      | some xsL, some dL, some fL, some costL =>
          some (xsL, q, s, dL, q0, fL, costL, total)
      | _, _, _, _ => none
  | _ => none

/-- Decode the MDD signature: (xs, N, level, E, from, label, to). -/
private def mddArgs (args : List Value) : Option MddInput :=
  match args with
  | [Value.array xsArr, Value.int n, Value.array levelArr, Value.int e,
     Value.array fromArr, Value.array labelArr, Value.array toArr] =>
      match valueInts xsArr, valueInts levelArr, valueInts fromArr,
        (labelArr.mapM (fun v => match v with
          | Value.setOfInt sv => some sv
          | _ => none)), valueInts toArr with
      | some xsL, some levelL, some fromL, some labelL, some toL =>
          some ⟨xsL, n, levelL, e, fromL, labelL, toL⟩
      | _, _, _, _, _ => none
  | _ => none

/-- Decode the cost-MDD signature: (xs, N, level, E, from, label,
    cost, to, total). -/
private def costMddArgs (args : List Value) :
    Option (MddInput × List Int × Int) :=
  match args with
  | [Value.array xsArr, Value.int n, Value.array levelArr, Value.int e,
     Value.array fromArr, Value.array labelArr, Value.array costArr,
     Value.array toArr, Value.int total] =>
      match valueInts xsArr, valueInts levelArr, valueInts fromArr,
        (labelArr.mapM (fun v => match v with
          | Value.setOfInt sv => some sv
          | _ => none)), valueInts costArr, valueInts toArr with
      | some xsL, some levelL, some fromL, some labelL, some costL,
        some toL =>
          some (⟨xsL, n, levelL, e, fromL, labelL, toL⟩, costL, total)
      | _, _, _, _, _, _ => none
  | _ => none

/-! ## The interpretations -/

/-- Mathematical interpretations of the regular family; wrong
    shapes yield `False`. -/
def regularInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_regular" => fun args =>
    match regularArgs args with
    | some (xs, q, s, d, q0, f) => regularProp xs q s d q0 f
    | none => False
  | "fzn_regular_nfa" => fun args =>
    match nfaArgs args with
    | some (xs, q, s, d, q0, f) => nfaProp xs q s d q0 f
    | none => False
  | "fzn_cost_regular" => fun args =>
    match costRegularArgs args with
    | some (xs, q, s, d, q0, f, cost, total) =>
        costRegularProp xs q s d q0 f cost total
    | none => False
  | "fzn_mdd" => fun args =>
    match mddArgs args with
    | some m => mddProp m
    | none => False
  | "fzn_mdd_nondet" => fun args =>
    match mddArgs args with
    | some m => mddProp m
    | none => False
  | "fzn_cost_mdd" => fun args =>
    match costMddArgs args with
    | some (m, cost, total) => costMddProp m cost total
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `regularInterp`.** -/
def regularInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_regular" => fun args =>
    match regularArgs args with
    | some (xs, q, s, d, q0, f) => regularB xs q s d q0 f
    | none => false
  | "fzn_regular_nfa" => fun args =>
    match nfaArgs args with
    | some (xs, q, s, d, q0, f) => nfaB xs q s d q0 f
    | none => false
  | "fzn_cost_regular" => fun args =>
    match costRegularArgs args with
    | some (xs, q, s, d, q0, f, cost, total) =>
        costRegularB xs q s d q0 f cost total
    | none => false
  | "fzn_mdd" => fun args =>
    match mddArgs args with
    | some m => mddB m
    | none => false
  | "fzn_mdd_nondet" => fun args =>
    match mddArgs args with
    | some m => mddB m
    | none => false
  | "fzn_cost_mdd" => fun args =>
    match costMddArgs args with
    | some (m, cost, total) => costMddB m cost total
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_regular_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_regular") args = true ↔
      regularInterp (Ident.mk "fzn_regular") args := by
  simp only [regularInterp, regularInterpB]
  cases h : regularArgs args with
  | none => simp
  | some p =>
    obtain ⟨xs, q, s, d, q0, f⟩ := p
    simp only
    exact regularB_iff xs q s d q0 f

theorem fzn_regular_nfa_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_regular_nfa") args = true ↔
      regularInterp (Ident.mk "fzn_regular_nfa") args := by
  simp only [regularInterp, regularInterpB]
  cases h : nfaArgs args with
  | none => simp
  | some p =>
    obtain ⟨xs, q, s, d, q0, f⟩ := p
    simp only
    exact nfaB_iff xs q s d q0 f

theorem fzn_cost_regular_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_cost_regular") args = true ↔
      regularInterp (Ident.mk "fzn_cost_regular") args := by
  simp only [regularInterp, regularInterpB]
  cases h : costRegularArgs args with
  | none => simp
  | some p =>
    obtain ⟨xs, q, s, d, q0, f, cost, total⟩ := p
    simp only
    exact costRegularB_iff xs q s d q0 f cost total

theorem fzn_mdd_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_mdd") args = true ↔
      regularInterp (Ident.mk "fzn_mdd") args := by
  simp only [regularInterp, regularInterpB]
  cases h : mddArgs args with
  | none => simp
  | some m =>
    simp only
    exact mddB_iff m

theorem fzn_mdd_nondet_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_mdd_nondet") args = true ↔
      regularInterp (Ident.mk "fzn_mdd_nondet") args := by
  simp only [regularInterp, regularInterpB]
  cases h : mddArgs args with
  | none => simp
  | some m =>
    simp only
    exact mddB_iff m

theorem fzn_cost_mdd_iff (args : List Value) :
    regularInterpB (Ident.mk "fzn_cost_mdd") args = true ↔
      regularInterp (Ident.mk "fzn_cost_mdd") args := by
  simp only [regularInterp, regularInterpB]
  cases h : costMddArgs args with
  | none => simp
  | some p =>
    obtain ⟨m, cost, total⟩ := p
    simp only
    exact costMddB_iff m cost total

end LeanFzn.Semantics.Globals.Regular

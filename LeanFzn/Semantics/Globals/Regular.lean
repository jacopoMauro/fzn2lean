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
  (both dimensions given by the sibling par ints `Q` and `S`); every
  state of the run, including `q0` and the final state, must lie in
  `1..Q`; every transition target must lie in `1..Q` and every `xs`
  value in `1..S`; the empty `xs` accepts iff `q0 ∈ F`, with no state
  bound in that branch.  `F` is a set of ints (`set of int` upstream), not a
  0/1 indicator array.
* `fzn_regular_nfa(xs, Q, S, d, q0, F)` (`fzn_regular_nfa.mzn`): NFA
  acceptance; `d` is the Q×S matrix of *sets* of target states
  (modelled as a flat row-major list of sets).  Computed as the union
  of the forward-reachable state sets over all current states, with
  every state of a run in `1..Q`; the empty `xs` accepts iff
  `q0 ∈ F`.
* `fzn_cost_regular(xs, Q, S, d, q0, F, cost, total_cost)`
  (`fzn_cost_regular.mzn`): DFA acceptance plus the summed transition
  cost (the Q×S cost matrix, row-major) equals `total_cost`; the empty
  word has `total_cost = 0` and `q0 ∈ F`.
* `fzn_mdd(xs, N, level, E, from, label, to)` (`fzn_mdd.mzn`): the
  literal upstream conjunction over the existentially quantified
  `bn : [0..N] → bool` and `be : [1..E] → bool`, for the fixed `xs`:
  `bn[0]`, `bn[1]`, T1 (active nodes need an outgoing active edge),
  T23 (active edges force both endpoints), T4 (active edges match
  `xs[level[from]]` against their label), P1 (matching outgoing edges
  are active), P2 (a terminal edge is active, and every active node
  except 1 has an incoming active edge), P3 (each fixed `xs[i]` has an
  active supporting edge at level `i`) and P4 (exactly one active node
  per level).  This is **not** a walk search: in particular levels are
  not required to increase along an edge.  `mddProp` is the literal
  bounded-`∃` transcription and `mddB` decides it exhaustively.
* `fzn_mdd_nondet(...)` (`fzn_mdd_nondet.mzn`): **restricted**.  The
  pinned body drops P1 and P4; this project keeps a sufficient
  first-walk search (root 1, level 1, levels increase by one per step,
  labels match) as its documented restriction.  It is deliberately
  not routed through the exact `fzn_mdd` core.
* `fzn_cost_mdd(xs, N, level, E, from, label, cost, to, total_cost)`
  (`fzn_cost_mdd.mzn`): **restricted** to the deterministic layered
  fragment `N = length(xs)`, `level[n] = n`, and every edge goes from
  level `l < N` to `l+1` or from level `N` to `0`.  On that fragment
  the upstream `ln`/`un` equations are evaluated literally by recursion
  on the acyclic level graph (with `be` forced by the label test), and
  the interpretation checks the `maxlevelcost`/`minlevelcost`/`maxcost`/
  `COST` definitions, every `ln`/`un` membership, the active-edge bound
  and `total_cost = ln[1]`.  Other cost-MDD calls are rejected by the
  decoder (`false`); see the MDD section below and
  `tmp/sc-repairs/T6/derivation.md` §2.2–2.3.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Regular

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

set_option synthInstance.maxSize 4096

/-! ## Row-major matrix access -/

/-- Row-major access into a flat Q-column matrix: entry (q, s) with
    q, s 1-based; 0 out of range. -/
private def matAt (flat : List Int) (cols : Int) (q s : Int) : Int :=
  flat.getD (((q - 1) * cols + (s - 1)).toNat) 0

/-! ## DFA runs -/

/-- The run function: the state after consuming the whole word from
    `start`, failing (none) on bad symbols or states outside `1..Q`.
    The empty word does not inspect `start`, so the empty-word
    acceptance condition is applied separately. -/
private def runFrom (d : List Int) (states sigma : Int) :
    Int → List Int → Option Int
  | state, [] => some state
  | state, x :: rest =>
      if 1 ≤ state ∧ state ≤ states then
        if 1 ≤ x ∧ x ≤ sigma then
          let state' := matAt d sigma state x
          if 1 ≤ state' ∧ state' ≤ states then
            runFrom d states sigma state' rest
          else none
        else none
      else none

/-- `fzn_regular`: the DFA accepts `xs` from `q0`.  The empty word is
    accepted exactly when `q0 ∈ F` (no state-bound check in that
    branch). -/
def regularProp (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) : Prop :=
  match runFrom d q sigma q0 xs with
  | some qf => f.Contains qf
  | none => False

/-- Boolean twin of `regularProp`. -/
def regularB (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) : Bool :=
  match runFrom d q sigma q0 xs with
  | some qf => setMemB f qf
  | none => false

theorem regularB_iff (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) :
    regularB xs q sigma d q0 f = true ↔
      regularProp xs q sigma d q0 f := by
  cases h : runFrom d q sigma q0 xs with
  | none => simp [regularB, regularProp, h]
  | some qf => simp [regularB, regularProp, h, setMemB_iff]

/-! ## NFA runs -/

/-- The set-valued transition matrix (row-major flat list of
    sets). -/
private def setMatAt (flat : List IntSetValue) (cols : Int) (q s : Int) :
    IntSetValue :=
  flat.getD (((q - 1) * cols + (s - 1)).toNat) (.enumeration [])

/-- The successor states of `q` on symbol `x`, restricted to the state
    range `1..Q`.  An out-of-range `q` or `x` has no successors. -/
private def nfaSuccs (d : List IntSetValue) (states sigma : Int)
    (q x : Int) : List Int :=
  if 1 ≤ q ∧ q ≤ states ∧ 1 ≤ x ∧ x ≤ sigma then
    (setElems (setMatAt d sigma q x)).filter
      (fun q' => 1 ≤ q' ∧ q' ≤ states)
  else []

/-- One NFA step: the union of the successor sets of *every* current
    frontier state, with duplicates removed. -/
private def nfaStep (d : List IntSetValue) (states sigma : Int)
    (frontier : List Int) (x : Int) : List Int :=
  frontier.foldl (fun acc q =>
    acc ++ (nfaSuccs d states sigma q x).filter
      (fun q' => !(acc.contains q'))) []

/-- NFA acceptance: the forward set of states reachable from `q0`
    after consuming all of `xs`; each step unions the successor sets of
    every state in the current frontier, with duplicates removed. -/
private def nfaFrontier (d : List IntSetValue) (states sigma : Int) :
    List Int → List Int → List Int
  | [], frontier => frontier
  | x :: rest, frontier =>
      nfaFrontier d states sigma rest (nfaStep d states sigma frontier x)

/-- `fzn_regular_nfa`.  The empty word accepts exactly when `q0 ∈ F`
    (no state bound in that branch); a nonempty word needs `q0` and
    every reachable state in `1..Q`. -/
def nfaProp (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : IntSetValue) : Prop :=
  match xs with
  | [] => f.Contains q0
  | _ :: _ =>
      1 ≤ q0 ∧ q0 ≤ q ∧
        (nfaFrontier d q sigma xs [q0]).any
          (fun q' => decide (f.Contains q')) = true

def nfaB (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : IntSetValue) : Bool :=
  match xs with
  | [] => setMemB f q0
  | _ :: _ =>
      decide (1 ≤ q0 ∧ q0 ≤ q) &&
        (nfaFrontier d q sigma xs [q0]).any (fun q' => setMemB f q')

theorem nfaB_iff (xs : List Int) (q sigma : Int) (d : List IntSetValue)
    (q0 : Int) (f : IntSetValue) :
    nfaB xs q sigma d q0 f = true ↔ nfaProp xs q sigma d q0 f := by
  cases xs with
  | nil => simp [nfaB, nfaProp, setMemB]
  | cons x rest =>
      simp only [nfaB, nfaProp, Bool.and_eq_true, decide_eq_true_iff,
        setMemB]
      rw [and_assoc]

/-! ## Cost regular -/

/-- The run together with its accumulated transition cost, failing
    (none) exactly like `runFrom`.  The empty word returns cost 0. -/
private def runFromCost (d cost : List Int) (states sigma : Int) :
    Int → List Int → Option (Int × Int)
  | state, [] => some (state, 0)
  | state, x :: rest =>
      if 1 ≤ state ∧ state ≤ states then
        if 1 ≤ x ∧ x ≤ sigma then
          let state' := matAt d sigma state x
          if 1 ≤ state' ∧ state' ≤ states then
            match runFromCost d cost states sigma state' rest with
            | some (qf, c) =>
                some (qf, cost.getD
                  (((state - 1) * sigma + (x - 1)).toNat) 0 + c)
            | none => none
          else none
        else none
      else none

/-- `fzn_cost_regular`: DFA acceptance plus the summed transition
    cost.  The empty word has `total = 0` and only requires `q0 ∈ F`. -/
def costRegularProp (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) (cost : List Int) (total : Int) : Prop :=
  match runFromCost d cost q sigma q0 xs with
  | some (qf, c) => f.Contains qf ∧ total = c
  | none => False

def costRegularB (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) (cost : List Int) (total : Int) : Bool :=
  match runFromCost d cost q sigma q0 xs with
  | some (qf, c) => setMemB f qf && decide (total = c)
  | none => false

theorem costRegularB_iff (xs : List Int) (q sigma : Int) (d : List Int)
    (q0 : Int) (f : IntSetValue) (cost : List Int) (total : Int) :
    costRegularB xs q sigma d q0 f cost total = true ↔
      costRegularProp xs q sigma d q0 f cost total := by
  cases h : runFromCost d cost q sigma q0 xs with
  | none => simp [costRegularB, costRegularProp, h]
  | some p =>
      obtain ⟨qf, c⟩ := p
      simp [costRegularB, costRegularProp, h, setMemB_iff, Bool.and_eq_true,
        decide_eq_true_iff]

/-! ## MDD

`fzn_mdd` is transcribed as the literal conjunction of
`share/minizinc/std/fzn_mdd.mzn`, not as a walk search.  The only
existential data are the Boolean arrays `bn : [0..N]` and `be : [1..E]`;
because both ranges are finite, they are enumerated with `allBits`.
`fzn_cost_mdd` is *restricted* to the deterministic layered fragment
documented in its section below.  `fzn_mdd_nondet` keeps a separate
restricted walk search. -/

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

/-! ### Index and enumeration helpers -/

/-- 1-based lookup in a list; `none` unless `1 ≤ i ≤ length`.  There is no
    silent default: `req` maps `none` to `False`, and every numeric site
    below is either `Fin`-bounded or covered by `mddGate` G3–G7. -/
def at1 {α : Type} (xs : List α) (i : Int) : Option α :=
  if 1 ≤ i ∧ i ≤ (xs.length : Int) then xs[i.toNat - 1]? else none

/-- `req o p` is `p a` for `o = some a`, and `False` for `none`:
    an undefined reference makes the enclosing conjunct false. -/
def req {α : Type} (o : Option α) (p : α → Prop) : Prop :=
  match o with
  | some a => p a
  | none => False

instance {α : Type} (o : Option α) (p : α → Prop) [DecidablePred p] :
    Decidable (req o p) := by
  cases o with
  | none => exact isFalse id
  | some a => exact (inferInstance : Decidable (p a))

/-- The 1-based id of a slot. -/
def idN {k : Nat} (i : Fin k) : Int := (i.val : Int) + 1

/-- All length-`k` Boolean lists. -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => ((allBits k).map (fun xs => [xs ++ [false], xs ++ [true]])).flatten

/-- `bn[n]`, with an out-of-universe read defaulting to `false`.  Every
    caller reads an index in `0..N` (`bn` is `allBits (N+1)`): node `0`/`1`
    by `mddRoot` (G1), `from[e]` by T1/P1/T23 (G5), `to[e]` by T23/P2
    (G6), and `idN n` for `n : Fin N` by T1/P2/P4 (G1). -/
def bnAt (bn : List Bool) (n : Int) : Bool :=
  if 0 ≤ n then bn.getD n.toNat false else false

/-- `be[e]` (1-based), with an out-of-universe read defaulting to `false`.
    Every caller passes `idN e` for `e : Fin E` and `be` is `allBits E`,
    so the index is in range; G2 gives `0 ≤ E`. -/
def beAt (be : List Bool) (e : Int) : Bool :=
  if 1 ≤ e then be.getD (e.toNat - 1) false else false

/-- Source of edge `e` (1-based, `Nat` for the nondeterministic search).
    For `e ∈ 1..E` the index `e-1` is in range because `mddGate` G4
    requires `E ≤ fromArr.length`. -/
private def mddFrom (m : MddInput) (e : Nat) : Int :=
  m.fromArr.getD (e - 1) 0

/-- Target of edge `e` (1-based, `Nat`).  G4 gives
    `E ≤ toArr.length`, so the index is in range for `e ∈ 1..E`. -/
private def mddTo (m : MddInput) (e : Nat) : Int :=
  m.toArr.getD (e - 1) 0

/-- Label set of edge `e` (1-based, `Nat`).  G4 gives
    `E ≤ label.length`, so the index is in range for `e ∈ 1..E`. -/
private def mddLabel (m : MddInput) (e : Nat) : IntSetValue :=
  m.label.getD (e - 1) (.enumeration [])

/-- Level of node `node` (1-based, `Nat`).  For `node ∈ 1..N` the index
    `node-1` is in range because `mddGate` G3 requires
    `N ≤ level.length`; `walkFrom` never passes `node = 0` (it tests that
    case first) and `from[e]`/`to[e]` are gated to `1..N`/`0..N`. -/
private def mddLevel (m : MddInput) (node : Nat) : Int :=
  m.level.getD (node - 1) 0

/-- Defined source of edge `e`; `none` outside `1..E`. -/
def mddFromAt (m : MddInput) (e : Int) : Option Int :=
  at1 m.fromArr e

/-- Defined target of edge `e`; `none` outside `1..E`. -/
def mddToAt (m : MddInput) (e : Int) : Option Int :=
  at1 m.toArr e

/-- Defined label of edge `e`; `none` outside `1..E`. -/
def mddLabelAt (m : MddInput) (e : Int) : Option IntSetValue :=
  at1 m.label e

/-- Defined level of node `n`; `none` outside `1..N` of the `level` list. -/
def mddLevelAt (m : MddInput) (n : Int) : Option Int :=
  at1 m.level n

/-! ### Literal conjuncts of `fzn_mdd.mzn` -/

/-- `bn[0]` and `bn[1]` (lines 17–18).  `bn : allBits (N+1)` and G1
    (`1 ≤ N`) make both indices readable. -/
abbrev mddRoot (bn : List Bool) : Prop :=
  bnAt bn 0 = true ∧ bnAt bn 1 = true

/-- T1 (line 20): every active node has an active outgoing edge. -/
abbrev mddT1 (m : MddInput) (bn be : List Bool) : Prop :=
  ∀ i : Fin m.n.toNat,
    bnAt bn (idN i) = true →
      ∃ e : Fin m.e.toNat,
        mddFromAt m (idN e) = some (idN i) ∧ beAt be (idN e) = true

/-- T23 (line 22): an active edge forces both endpoints.  `mddFromAt`/
    `mddToAt` are `at1` (no default) and G4/G5/G6 make them `some` for
    every `e : Fin E`; `bnAt` indices are in `0..N` (G5/G6). -/
abbrev mddT23 (m : MddInput) (bn be : List Bool) : Prop :=
  ∀ e : Fin m.e.toNat,
    beAt be (idN e) = true →
      req (mddFromAt m (idN e)) (fun f => bnAt bn f = true) ∧
      req (mddToAt m (idN e)) (fun t => bnAt bn t = true)

/-- T4 (line 24): an active edge's label contains `xs[level[from]]`.
    G5 puts `from[e]` in `1..N`, G3 makes `level[from[e]]` readable, G7
    puts it in `1..L`, and G4b makes `label[e]` readable; `req` maps any
    residual `none` (only reachable outside the gate) to `False`. -/
abbrev mddT4 (m : MddInput) (be : List Bool) : Prop :=
  ∀ e : Fin m.e.toNat,
    beAt be (idN e) = true →
      req (mddFromAt m (idN e)) (fun f =>
        req (mddLevelAt m f) (fun lv =>
          req (mddLabelAt m (idN e)) (fun lb =>
            req (at1 m.xs lv) (fun x => lb.Contains x))))

/-- P1 (line 26): matching outgoing edges are active.  Same `at1` chain
    as T4: G5/G3/G7/G4b give definedness, `req` is fail-closed. -/
abbrev mddP1 (m : MddInput) (bn be : List Bool) : Prop :=
  ∀ e : Fin m.e.toNat,
    req (mddFromAt m (idN e)) (fun f =>
      bnAt bn f = true ∧
        req (mddLevelAt m f) (fun lv =>
          req (at1 m.xs lv) (fun x =>
            req (mddLabelAt m (idN e)) (fun lb => lb.Contains x)))) →
    beAt be (idN e) = true

/-- P2 (lines 28–29): a terminal edge is active, and every active node
    except node 1 has an active incoming edge.  `Fin E` bounds the edge
    index, G6 keeps `to[e]` in `0..N`, and `Fin (N-1)` bounds
    `n ∈ 2..N`; `bnAt` reads then stay in `0..N`. -/
abbrev mddP2 (m : MddInput) (bn be : List Bool) : Prop :=
  (∃ e : Fin m.e.toNat,
    mddToAt m (idN e) = some 0 ∧ beAt be (idN e) = true) ∧
  (∀ j : Fin (m.n.toNat - 1),
    let n : Int := (j.val : Int) + 2
    bnAt bn n = true →
      ∃ e : Fin m.e.toNat,
        mddToAt m (idN e) = some n ∧ beAt be (idN e) = true)

/-- P3 (lines 31–33), reduced at fixed `xs`: every `xs[i]` has an active
    supporting edge with `level[from[e]] = i`.  See
    `tmp/sc-repairs/T6/derivation.md` §1.1.  `idN i ∈ 1..L` because
    `i : Fin xs.length`; the level and label reads are the same `at1`
    chain as T4 (G4b/G3/G5/G7), and `req` is fail-closed. -/
abbrev mddP3 (m : MddInput) (be : List Bool) : Prop :=
  ∀ i : Fin m.xs.length,
    ∃ e : Fin m.e.toNat,
      req (mddFromAt m (idN e)) (fun f =>
        req (mddLevelAt m f) (fun lv => lv = idN i)) ∧
      req (mddLabelAt m (idN e)) (fun lb =>
        req (at1 m.xs (idN i)) (fun x => lb.Contains x)) ∧
      beAt be (idN e) = true

/-- The sum in P4 (line 35) for level `i`.  `mddLevelAt m (idN n)` is
    `some` by G3 for `n ∈ 1..N`, and `bnAt` reads `idN n ∈ 1..N ⊆ 0..N`. -/
def mddLevelSum (m : MddInput) (bn : List Bool)
    (i : Fin m.xs.length) : Nat :=
  ((List.finRange m.n.toNat).map (fun n =>
    if mddLevelAt m (idN n) = some (idN i) then
      (if bnAt bn (idN n) then 1 else 0) else 0)).sum

/-- P4 (line 35): exactly one active node per level `1..L`.  The level
    index is a `Fin xs.length`, so `idN i ∈ 1..L`. -/
abbrev mddP4 (m : MddInput) (bn : List Bool) : Prop :=
  ∀ i : Fin m.xs.length, mddLevelSum m bn i = 1

/-- The full literal conjunction of `fzn_mdd.mzn`. -/
abbrev mddCore (m : MddInput) (bn be : List Bool) : Prop :=
  mddRoot bn ∧ mddT1 m bn be ∧ mddT23 m bn be ∧ mddT4 m be ∧
    mddP1 m bn be ∧ mddP2 m bn be ∧ mddP3 m be ∧ mddP4 m bn

/-- The conjunction as a Boolean; one `decide` per upstream conjunct so
    that instance synthesis stays small. -/
def mddBool (m : MddInput) (bn be : List Bool) : Bool :=
  decide (mddRoot bn) && decide (mddT1 m bn be) &&
    decide (mddT23 m bn be) && decide (mddT4 m be) &&
    decide (mddP1 m bn be) && decide (mddP2 m bn be) &&
    decide (mddP3 m be) && decide (mddP4 m bn)

theorem mddBool_iff (m : MddInput) (bn be : List Bool) :
    mddBool m bn be = true ↔ mddCore m bn be := by
  simp only [mddBool, mddCore, Bool.and_eq_true, decide_eq_true_iff,
    and_assoc]

/-- `fzn_mdd`: the upstream conjunction over `∃ bn ∈ allBits (N+1),
    ∃ be ∈ allBits E`.  The universes match the gated ranges: `bn` indexes
    `0..N`, `be` indexes `1..E` (`mddGate` G1–G3). -/
abbrev mddProp (m : MddInput) : Prop :=
  ∃ bn : List Bool, bn ∈ allBits (m.n.toNat + 1) ∧
    ∃ be : List Bool, be ∈ allBits (m.e.toNat) ∧ mddCore m bn be

/-- Exhaustive decision procedure for `mddProp`. -/
def mddB (m : MddInput) : Bool :=
  (allBits (m.n.toNat + 1)).any (fun bn =>
    (allBits (m.e.toNat)).any (fun be => mddBool m bn be))

theorem mddB_iff (m : MddInput) : mddB m = true ↔ mddProp m := by
  simp only [mddB, mddProp, List.any_eq_true]
  constructor
  · rintro ⟨bn, hbn, be, hbe, h⟩
    exact ⟨bn, hbn, be, hbe, (mddBool_iff m bn be).mp h⟩
  · rintro ⟨bn, hbn, be, hbe, h⟩
    exact ⟨bn, hbn, be, hbe, (mddBool_iff m bn be).mpr h⟩

/-! ### `fzn_mdd_nondet` (restricted) -/

/-- The edges out of `node` (0-based edge indices).  `mddFrom m (e+1)` with
    `e < E` (G4a) is an in-range `fromArr` read. -/
private def outEdges (m : MddInput) (node : Nat) : List Nat :=
  (List.range m.e.toNat).filter (fun e =>
    mddFrom m (e + 1) = (node : Int))

/-- Satisfying walks from `node` consuming `xs` from level `lvl`:
    a recursive search.  Returns `some cost` when a walk to T exists
    (with its edge-cost sum), `none` otherwise.

    Gate coverage: the start node is `1` (G1), every recursion step maps
    `to[e] ∈ 0..N` (G6) and checks `node == 0` before `mddLevel`, so each
    `mddLevel m node` read has `node ∈ 1..N` and is bounded by G3;
    `mddTo m (e+1)`/`mddLabel m (e+1)` use `e < E` (G4b/G4c); and
    `cost.getD e 0` reads the `List.replicate E 0` array in range. -/
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

/-- `fzn_mdd_nondet`: restricted to a single root-to-terminal walk whose
    level increases by one at every step.  This is a sufficient (not
    exact) interpretation of the pinned P1/P4-free body; the row is
    `restricted`.  It is deliberately not routed through `mddCore`. -/
def mddNondetProp (m : MddInput) : Prop :=
  (walkFrom m (List.replicate m.e.toNat 0) 1 m.xs 1).isSome = true

def mddNondetB (m : MddInput) : Bool :=
  (walkFrom m (List.replicate m.e.toNat 0) 1 m.xs 1).isSome

theorem mddNondetB_iff (m : MddInput) :
    mddNondetB m = true ↔ mddNondetProp m := by
  simp only [mddNondetB, mddNondetProp]

/-! ### `fzn_cost_mdd` (restricted to the canonical layered fragment) -/

/-- Maximum edge cost at level `l` (`maxlevelcost[l]`); `none` when the
    level has no edge, matching the undefined upstream `max ∅`.
    The `filterMap` reads `from[e]` (G4a), `cost[e]` (G8) and
    `level[from[e]]` (G3+G5) for every `e ∈ 1..E`; under `costMddGate`
    all three are defined, so no edge of the diagram is silently dropped.
    A call outside the gate is already `False` (`decoder = none`). -/
def maxLevelCost (m : MddInput) (cost : List Int) (l : Int) : Option Int :=
  match (List.finRange m.e.toNat).filterMap (fun e =>
      match mddFromAt m (idN e), at1 cost (idN e) with
      | some f, some c =>
          match mddLevelAt m f with
          | some lv => if lv = l then some c else none
          | none => none
      | _, _ => none) with
  | [] => none
  | c :: cs => some (cs.foldl (fun acc x => max acc x) c)

/-- `minlevelcost[l] = min([0] ++ negative costs at level l)`; always
    defined because `0` is included.  Same `filterMap` reads as
    `maxLevelCost`: G4a/G8/G3+G5 make every defined edge visible under
    `costMddGate`, so a level with edges is never silently treated as
    empty. -/
def minLevelCost (m : MddInput) (cost : List Int) (l : Int) : Int :=
  match (List.finRange m.e.toNat).filterMap (fun e =>
      match mddFromAt m (idN e), at1 cost (idN e) with
      | some f, some c =>
          match mddLevelAt m f with
          | some lv => if lv = l ∧ c < 0 then some c else none
          | none => none
      | _, _ => none) with
  | [] => 0
  | c :: cs => cs.foldl (fun acc x => min acc x) c

/-- Sum of an option list, `none` if any entry is undefined.  Total over
    the list, so it performs no index read. -/
def sumOptL : List (Option Int) → Option Int
  | [] => some 0
  | none :: _ => none
  | some x :: rest => (sumOptL rest).map (x + ·)

/-- `maxcost = Σ_l maxlevelcost[l]`; `none` if some level is edgeless.
    The `Fin xs.length` index is `l ∈ 1..L`, the exact `1..L` range of
    the upstream array comprehension. -/
def maxCost (m : MddInput) (cost : List Int) : Option Int :=
  sumOptL (List.ofFn fun l : Fin m.xs.length =>
    maxLevelCost m cost (idN l))

/-- Lower endpoint of `COST`: `Σ_l minlevelcost[l]`. -/
def costLo (m : MddInput) (cost : List Int) : Int :=
  (List.ofFn fun l : Fin m.xs.length =>
    minLevelCost m cost (idN l)).sum

/-- Upper endpoint of `COST`: `L * (maxcost + 1)`. -/
def costHi (m : MddInput) (cost : List Int) : Option Int :=
  (maxCost m cost).map (fun mc => (m.xs.length : Int) * (mc + 1))

/-- Minimum of a list; `none` for `[]` (upstream `min ∅`, which is
    undefined and therefore false). -/
def minOpt : List Int → Option Int
  | [] => none
  | c :: cs => some (cs.foldl (fun acc x => min acc x) c)

/-- Costs of the edges at level `l` whose label contains `xs[l]`.  Kept
    as the documentation of `m_l`; the executable `ln`/`un` recursion
    below does not assume the closed form in terms of `m_l`. -/
def matchingCosts (m : MddInput) (cost : List Int) (l : Int) : List Int :=
  (List.finRange m.e.toNat).filterMap (fun e =>
    match mddFromAt m (idN e), at1 cost (idN e) with
    | some f, some c =>
        match mddLevelAt m f, at1 m.xs l, mddLabelAt m (idN e) with
        | some lv, some x, some lb =>
            if lv = l ∧ lb.Contains x then some c else none
        | _, _, _ => none
    | _, _ => none)

/-- `m_l`, the minimum matching cost at level `l`; `none` if no matching
    edge exists. -/
def levelMatchMin (m : MddInput) (cost : List Int) (l : Int) :
    Option Int :=
  minOpt (matchingCosts m cost l)

/-- Boolean label test for edge `e` at `level[from[e]]`.  Under the
    canonical cost gate this is the forced value of `be[e]` (P1 + T4).
    `at1 m.xs lv` is `some` by G7; any residual `none` yields `false`
    (fail-closed). -/
def mddEdgeMatchB (m : MddInput) (e : Int) : Bool :=
  match mddFromAt m e, mddLabelAt m e with
  | some f, some lb =>
      match mddLevelAt m f with
      | some lv =>
          match at1 m.xs lv with
          | some x => setMemB lb x
          | none => false
      | none => false
  | _, _ => false

/-- The candidate terms of the upstream `ln[n]` minimum.  `next` is
    `ln[to[e]]`; on the canonical gate every edge from level `n < L`
    goes to `n+1`, and every edge from level `L` goes to `0`.
    The `filterMap` reads `from[e]` (G4a), `to[e]` (G4c), `cost[e]` (G8)
    and `level[from[e]]` (G3+G5), all defined for `e ∈ 1..E` under
    `costMddGate`; no default is used. -/
def lnTerms (m : MddInput) (cost : List Int) (mc : Int) (n : Nat)
    (next : Option Int) (expectedTo : Int) : List Int :=
  (List.finRange m.e.toNat).filterMap (fun e =>
    match mddFromAt m (idN e), mddToAt m (idN e), at1 cost (idN e) with
    | some _, some t, some c =>
        if mddLevelAt m (mddFrom m (e.val + 1)) = some (n : Int) ∧
            t = expectedTo then
          next.map (fun v =>
            v + c + (if mddEdgeMatchB m (idN e) then 0 else mc + 1 - c))
        else none
    | _, _, _ => none)

/-- `ln[n]` by the literal upstream recursion
    `ln[n] = min_e (ln[to[e]] + cost[e]
      + (not be[e]) * (maxcost + 1 - cost[e]))`,
    with `be[e]` forced by the label test.  `lnAux d n` computes
    `ln[n]` when `d = L - n`; it recurses structurally on `d`, using
    `ln[n+1] = lnAux (d-1) (n+1)`.  At `d = 0` (`n = L`) the next
    value is `ln[0] = 0`. -/
def lnAux (m : MddInput) (cost : List Int) (mc : Int) :
    Nat → Nat → Option Int
  | 0, n => minOpt (lnTerms m cost mc n (some 0) 0)
  | d + 1, n =>
      minOpt (lnTerms m cost mc n
        (lnAux m cost mc d (n + 1)) ((n : Int) + 1))

/-- `ln[n]` at `n ∈ 0..L`; `none` outside that range (upstream `ln` is
    defined on `0..N` and `costMddGate` fixes `N = L`).  `n = 0` is the
    upstream `ln[0] = 0`. -/
def lnAt (m : MddInput) (cost : List Int) (mc : Int) (n : Nat) :
    Option Int :=
  if n = 0 then some 0
  else if n ≤ m.xs.length then
    lnAux m cost mc (m.xs.length - n) n
  else none

/-- The candidate terms of the upstream `un[n]` minimum.  `prev` is
    `un[from[e]]`; on the canonical gate the only edges into node `n`
    come from node `n-1`.  Same `filterMap` reads as `lnTerms`
    (G4a/G4c/G8), all defined under `costMddGate`. -/
def unTerms (m : MddInput) (cost : List Int) (mc : Int) (n : Nat)
    (prev : Option Int) : List Int :=
  (List.finRange m.e.toNat).filterMap (fun e =>
    match mddFromAt m (idN e), mddToAt m (idN e), at1 cost (idN e) with
    | some f, some t, some c =>
        if t = (n : Int) ∧ f = (n : Int) - 1 then
          prev.map (fun v =>
            v + c + (if mddEdgeMatchB m (idN e) then 0 else mc + 1 - c))
        else none
    | _, _, _ => none)

/-- `un[n]` by the literal upstream recursion, with `un[1] = 0` and
    `un[0]` unconstrained (we return `0`).  Structural recursion on the
    level index; `none` for `n > L`, which `costMddGate` (`N = L`) never
    reaches from `costMddValuesB`/`costEdgeBoundOk`. -/
def unAt (m : MddInput) (cost : List Int) (mc : Int) : Nat → Option Int
  | 0 => some 0
  | 1 => some 0
  | n + 2 =>
      if n + 2 ≤ m.xs.length then
        minOpt (unTerms m cost mc (n + 2) (unAt m cost mc (n + 1)))
      else none

/-- `pathCost = ln[1]`, computed by the upstream recursion. -/
def pathCost (m : MddInput) (cost : List Int) : Option Int :=
  match maxCost m cost with
  | some mc => lnAt m cost mc 1
  | none => none

/-- T23 of `fzn_cost_mdd.mzn` line 35: an active edge forces **only**
    its target endpoint (`be[e] -> bn[to[e]]`, printed twice upstream).
    The source endpoint is not forced. -/
abbrev costMddT23 (m : MddInput) (bn be : List Bool) : Prop :=
  ∀ e : Fin m.e.toNat,
    beAt be (idN e) = true →
      req (mddToAt m (idN e)) (fun t => bnAt bn t = true)

/-- The deterministic base conjuncts of `fzn_cost_mdd.mzn`. -/
abbrev costMddBase (m : MddInput) (bn be : List Bool) : Prop :=
  mddRoot bn ∧ mddT1 m bn be ∧ costMddT23 m bn be ∧ mddT4 m be ∧
    mddP1 m bn be ∧ mddP2 m bn be ∧ mddP3 m be ∧ mddP4 m bn

/-- The upstream `maxlevelcost`/`minlevelcost`/`maxcost`/`COST` values
    and the literal `ln`/`un`/`total_cost` equations, on the canonical
    fragment.  Every `ln[n]` and `un[n]` must lie in `COST`.  Boolean
    form so that `costMddBool` can evaluate it without reducing the
    `Option` matches during instance synthesis.

    Indices: `lnAt` is read for `n ∈ 0..L` (`Fin (L+1)`) and `unAt` for
    `n ∈ 2..L` (`Fin (L-1)` offset by 2), both inside the `lnAt`/`unAt`
    domains; `costLo`/`costHi` read the level arrays at `1..L`.  No
    argument-derived index is involved beyond those. -/
def costMddValuesB (m : MddInput) (cost : List Int)
    (total : Int) : Bool :=
  match maxCost m cost with
  | none => false
  | some mc =>
      let hi := (m.xs.length : Int) * (mc + 1)
      (List.finRange (m.xs.length + 1)).all (fun n =>
        match lnAt m cost mc n.val with
        | some v => decide (costLo m cost ≤ v ∧ v ≤ hi)
        | none => false) &&
      (List.finRange (m.xs.length - 1)).all (fun j =>
        match unAt m cost mc (j.val + 2) with
        | some v => decide (costLo m cost ≤ v ∧ v ≤ hi)
        | none => false) &&
      (match lnAt m cost mc 1 with
       | some pc => decide (total = pc)
       | none => false) &&
      decide (costLo m cost ≤ total ∧ total ≤ hi)

abbrev costMddValues (m : MddInput) (cost : List Int)
    (total : Int) : Prop :=
  costMddValuesB m cost total = true

/-- The active-edge bound `un[from] + cost[e] + ln[to] ≤ maxcost`
    (line 63), computed on the recursive `unAt`/`lnAt`.  `f = from[e]` is
    in `1..N` (G5) and `t = to[e]` in `0..N` (G6); `costMddGate` gives
    `N = L`, so both `f.toNat` and `t.toNat` are in the `lnAt`/`unAt`
    domain `0..L`.  The `at1` reads are `some` by G4a/G4c/G8. -/
def costEdgeBoundOk (m : MddInput) (cost : List Int) (be : List Bool)
    (mc : Int) (e : Fin m.e.toNat) : Bool :=
  if beAt be (idN e) then
    match mddFromAt m (idN e), mddToAt m (idN e), at1 cost (idN e) with
    | some f, some t, some c =>
        match unAt m cost mc f.toNat, lnAt m cost mc t.toNat with
        | some u, some v => decide (u + c + v ≤ mc)
        | _, _ => false
    | _, _, _ => false
  else true

def costMddActiveBoundB (m : MddInput) (cost : List Int)
    (be : List Bool) : Bool :=
  match maxCost m cost with
  | some mc =>
      (List.finRange m.e.toNat).all
        (fun e => costEdgeBoundOk m cost be mc e)
  | none => false

abbrev costMddActiveBound (m : MddInput) (cost : List Int)
    (be : List Bool) : Prop :=
  costMddActiveBoundB m cost be = true

/-- The full restricted cost-MDD core. -/
abbrev costMddCore (m : MddInput) (cost : List Int) (total : Int)
    (bn be : List Bool) : Prop :=
  costMddBase m bn be ∧ costMddValues m cost total ∧
    costMddActiveBound m cost be

def costMddBool (m : MddInput) (cost : List Int) (total : Int)
    (bn be : List Bool) : Bool :=
  decide (costMddBase m bn be) && decide (costMddValues m cost total) &&
    decide (costMddActiveBound m cost be)

theorem costMddBool_iff (m : MddInput) (cost : List Int) (total : Int)
    (bn be : List Bool) :
    costMddBool m cost total bn be = true ↔
      costMddCore m cost total bn be := by
  simp only [costMddBool, costMddCore, Bool.and_eq_true,
    decide_eq_true_iff, and_assoc]

/-- `fzn_cost_mdd` on the canonical fragment: the deterministic base
    conjuncts plus the upstream cost array/equation block. -/
abbrev costMddProp (m : MddInput) (cost : List Int) (total : Int) : Prop :=
  ∃ bn : List Bool, bn ∈ allBits (m.n.toNat + 1) ∧
    ∃ be : List Bool, be ∈ allBits (m.e.toNat) ∧
      costMddCore m cost total bn be

def costMddB (m : MddInput) (cost : List Int) (total : Int) : Bool :=
  (allBits (m.n.toNat + 1)).any (fun bn =>
    (allBits (m.e.toNat)).any (fun be => costMddBool m cost total bn be))

theorem costMddB_iff (m : MddInput) (cost : List Int) (total : Int) :
    costMddB m cost total = true ↔ costMddProp m cost total := by
  simp only [costMddB, costMddProp, List.any_eq_true]
  constructor
  · rintro ⟨bn, hbn, be, hbe, h⟩
    exact ⟨bn, hbn, be, hbe, (costMddBool_iff m cost total bn be).mp h⟩
  · rintro ⟨bn, hbn, be, hbe, h⟩
    exact ⟨bn, hbn, be, hbe, (costMddBool_iff m cost total bn be).mpr h⟩

/-!
### SC-04 range gates

The T10 SC-04 audit of every argument-derived read in this file (see the
per-site comments above and the site table in
`tmp/sc-repairs/T10-W4/report.md`) found **no gap**: `mddGate` below
already covers every `level`, `from`, `label`, `to` and `level[from]`
read of `fzn_mdd.mzn` / `fzn_mdd_nondet.mzn` (G1–G7), and
`costMddGate` adds G8 (`E ≤ length(cost)`) and the canonical layered
conditions needed by the `ln`/`un` recursion. The gates are unchanged. -/

/-- The shared array-read gate of §3 of
    `tmp/sc-repairs/T6/derivation.md`: every `level`, `from`, `label`,
    `to` and `level[from]` reference is defined, and `N ≥ 1`, `E ≥ 0`.

    G1 `1 ≤ N`; G2 `0 ≤ E`; G3 `N ≤ length(level)`; G4
    `E ≤ length(from) ∧ E ≤ length(label) ∧ E ≤ length(to)`; G5
    `1 ≤ from[e] ≤ N`; G6 `0 ≤ to[e] ≤ N`; G7
    `1 ≤ level[from[e]] ≤ L`.  Defensive `getD` default `0` cannot
    contribute to an accepting call: the conjuncts themselves are
    fail-closed when a read is undefined. -/
abbrev mddGate (m : MddInput) : Prop :=
  1 ≤ m.n ∧ 0 ≤ m.e ∧ (m.n : Int) ≤ (m.level.length : Int) ∧
    (m.e : Int) ≤ (m.fromArr.length : Int) ∧
    (m.e : Int) ≤ (m.label.length : Int) ∧
    (m.e : Int) ≤ (m.toArr.length : Int) ∧
    (∀ e : Fin m.e.toNat,
      1 ≤ mddFrom m (e.val + 1) ∧
        mddFrom m (e.val + 1) ≤ m.n ∧
        0 ≤ mddTo m (e.val + 1) ∧
        mddTo m (e.val + 1) ≤ m.n ∧
        1 ≤ mddLevel m (mddFrom m (e.val + 1)).toNat ∧
        mddLevel m (mddFrom m (e.val + 1)).toNat ≤
          (m.xs.length : Int))

def mddGateB (m : MddInput) : Bool := decide (mddGate m)

theorem mddGateB_iff (m : MddInput) : mddGateB m = true ↔ mddGate m :=
  decide_eq_true_iff

/-- The canonical deterministic layered gate of `fzn_cost_mdd`.  This is
    a restriction, not the full upstream relation. -/
def costNext (n f : Int) : Int := if f < n then f + 1 else 0

abbrev costMddGate (m : MddInput) (cost : List Int) : Prop :=
  mddGate m ∧
    m.n = (m.xs.length : Int) ∧
    (∀ k : Fin m.n.toNat, mddLevelAt m (idN k) = some (idN k)) ∧
    (∀ e : Fin m.e.toNat,
      mddToAt m (idN e) =
        some (costNext m.n (mddFrom m (e.val + 1)))) ∧
    (m.e : Int) ≤ (cost.length : Int)

def costMddGateB (m : MddInput) (cost : List Int) : Bool :=
  decide (costMddGate m cost)

theorem costMddGateB_iff (m : MddInput) (cost : List Int) :
    costMddGateB m cost = true ↔ costMddGate m cost :=
  decide_eq_true_iff

/-! ## Argument decoders -/

/-- Decode the full regular signature: (xs, Q, S, d, q0, F). -/
private def regularArgs (args : List Value) :
    Option (List Int × Int × Int × List Int × Int × IntSetValue) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, fVal] =>
      match valueInts xsArr, valueInts dArr, valueSet fVal with
      | some xsL, some dL, some f =>
          if 0 ≤ q ∧ 0 ≤ s ∧ dL.length = q.toNat * s.toNat then
            some (xsL, q, s, dL, q0, f)
          else none
      | _, _, _ => none
  | _ => none

/-- Decode the NFA signature: (xs, Q, S, d-sets, q0, F). -/
private def nfaArgs (args : List Value) :
    Option (List Int × Int × Int × List IntSetValue × Int × IntSetValue) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, fVal] =>
      match valueInts xsArr, valueSets dArr, valueSet fVal with
      | some xsL, some dL, some f =>
          if 0 ≤ q ∧ 0 ≤ s ∧ dL.length = q.toNat * s.toNat then
            some (xsL, q, s, dL, q0, f)
          else none
      | _, _, _ => none
  | _ => none

/-- Decode the cost-regular signature: (xs, Q, S, d, q0, F, cost,
    total). -/
private def costRegularArgs (args : List Value) :
    Option (List Int × Int × Int × List Int × Int × IntSetValue ×
      List Int × Int) :=
  match args with
  | [Value.array xsArr, Value.int q, Value.int s, Value.array dArr,
     Value.int q0, fVal, Value.array costArr, Value.int total] =>
      match valueInts xsArr, valueInts dArr, valueSet fVal,
        valueInts costArr with
      | some xsL, some dL, some f, some costL =>
          if 0 ≤ q ∧ 0 ≤ s ∧ dL.length = q.toNat * s.toNat ∧
              costL.length = q.toNat * s.toNat then
            some (xsL, q, s, dL, q0, f, costL, total)
          else none
      | _, _, _, _ => none
  | _ => none

/-- Decode the MDD signature: (xs, N, level, E, from, label, to). -/
private def mddArgs (args : List Value) : Option MddInput :=
  match args with
  | [Value.array xsArr, Value.int n, Value.array levelArr, Value.int e,
     Value.array fromArr, Value.array labelArr, Value.array toArr] =>
      match valueInts xsArr, valueInts levelArr, valueInts fromArr,
        valueSets labelArr, valueInts toArr with
      | some xsL, some levelL, some fromL, some labelL, some toL =>
          let m : MddInput := ⟨xsL, n, levelL, e, fromL, labelL, toL⟩
          if mddGateB m then some m else none
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
        valueSets labelArr, valueInts costArr, valueInts toArr with
      | some xsL, some levelL, some fromL, some labelL, some costL,
        some toL =>
          let m : MddInput := ⟨xsL, n, levelL, e, fromL, labelL, toL⟩
          if mddGateB m && costMddGateB m costL then
            some (m, costL, total)
          else none
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
    | some m => mddNondetProp m
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
    | some m => mddNondetB m
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
    exact mddNondetB_iff m

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

/-! ## Decodability gates

`regularDecodes` is the Boolean decodability gate of the family: the `isSome`
of the very decoder `regularInterp` uses, and `true` outside the family.
`regularDecodes_agree` states that the gate cannot distinguish two argument
lists which agree on the shape information that is statically known from a
well-typed call (`ArgsAgree`): constructor tags and array lengths, plus the
exact values of the `par` arguments.  In the six real signatures only `xs`
and the trailing `total` of the two cost constraints may be variables, and
`total` is stored by the decoder but never inspected by the gate.  Hence the
hypothesis `regularDecodesParamsOK n params`: every argument after the first
is `par`, except that for `fzn_cost_regular` and `fzn_cost_mdd` the last
argument is exempt. -/

/-- Boolean decodability gate of the `regular` family.  Neutral (`true`)
    outside the family. -/
def regularDecodes (n : String) (args : List Value) : Bool :=
  match n with
  | "fzn_regular" => (regularArgs args).isSome
  | "fzn_regular_nfa" => (nfaArgs args).isSome
  | "fzn_cost_regular" => (costRegularArgs args).isSome
  | "fzn_mdd" => (mddArgs args).isSome
  | "fzn_mdd_nondet" => (mddArgs args).isSome
  | "fzn_cost_mdd" => (costMddArgs args).isSome
  | _ => true

/-- `mddGateB` depends on the MDD variables `xs` only through their length. -/
theorem mddGateB_congr {xs xs' : List Int} {n e : Int}
    {level fromArr toArr : List Int} {label : List IntSetValue}
    (hlen : xs.length = xs'.length) :
    mddGateB ⟨xs, n, level, e, fromArr, label, toArr⟩ =
      mddGateB ⟨xs', n, level, e, fromArr, label, toArr⟩ := by
  simp only [mddGateB, mddGate, mddFrom, mddTo, mddLevel, hlen]
  rfl

/-- `costMddGateB` depends on the MDD variables `xs` only through their
    length. -/
theorem costMddGateB_congr {xs xs' : List Int} {n e : Int}
    {level fromArr cost toArr : List Int} {label : List IntSetValue}
    (hlen : xs.length = xs'.length) :
    costMddGateB ⟨xs, n, level, e, fromArr, label, toArr⟩ cost =
      costMddGateB ⟨xs', n, level, e, fromArr, label, toArr⟩ cost := by
  simp only [costMddGateB, costMddGate, mddGate, mddLevelAt, mddToAt,
    mddFrom, mddTo, hlen]
  rfl

/-- The `fzn_regular` decoder accepts exactly the same argument shapes. -/
theorem regularArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params.drop 1, pt.isPar = true) :
    (regularArgs vs).isSome = (regularArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  have htail : vs.drop 1 = ws.drop 1 := ArgsAgree.drop_one_eq h hpar
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead _ =>
      have htail' : vs1 = ws1 := by simpa using htail
      subst htail'
      cases hhead with
      | bool _ _ => rfl
      | int _ _ => rfl
      | setOfInt _ _ => rfl
      | @array xs ys harr =>
        cases vs1 with
        | nil => rfl
        | cons v1 vs2 =>
          cases v1 with
          | bool _ => rfl
          | setOfInt _ => rfl
          | array _ => rfl
          | int q =>
            cases vs2 with
            | nil => rfl
            | cons v2 vs3 =>
              cases v2 with
              | bool _ => rfl
              | setOfInt _ => rfl
              | array _ => rfl
              | int s =>
                cases vs3 with
                | nil => rfl
                | cons v3 vs4 =>
                  cases v3 with
                  | bool _ => rfl
                  | int _ => rfl
                  | setOfInt _ => rfl
                  | array d =>
                    cases vs4 with
                    | nil => rfl
                    | cons v4 vs5 =>
                      cases v4 with
                      | bool _ => rfl
                      | setOfInt _ => rfl
                      | array _ => rfl
                      | int q0 =>
                        cases vs5 with
                        | nil => rfl
                        | cons v5 vs6 =>
                          cases vs6 with
                          | cons _ _ => rfl
                          | nil =>
                            have hx : (valueInts xs).isSome =
                                (valueInts ys).isSome :=
                              valueInts_isSome_sameShape harr
                            simp only [regularArgs]
                            cases h1 : valueInts xs with
                            | none =>
                              cases h2 : valueInts ys with
                              | none => rfl
                              | some ysL =>
                                simp [h1, h2] at hx
                            | some xsL =>
                              cases h2 : valueInts ys with
                              | none =>
                                simp [h1, h2] at hx
                              | some ysL =>
                                cases h3 : valueInts d with
                                | none => rfl
                                | some dL =>
                                  cases h4 : valueSet v5 with
                                  | none => rfl
                                  | some fv =>
                                    by_cases hg : 0 ≤ q ∧ 0 ≤ s ∧
                                        dL.length = q.toNat * s.toNat <;>
                                      simp [hg]

/-- The `fzn_regular_nfa` decoder accepts exactly the same argument shapes. -/
theorem nfaArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params.drop 1, pt.isPar = true) :
    (nfaArgs vs).isSome = (nfaArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  have htail : vs.drop 1 = ws.drop 1 := ArgsAgree.drop_one_eq h hpar
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead _ =>
      have htail' : vs1 = ws1 := by simpa using htail
      subst htail'
      cases hhead with
      | bool _ _ => rfl
      | int _ _ => rfl
      | setOfInt _ _ => rfl
      | @array xs ys harr =>
        cases vs1 with
        | nil => rfl
        | cons v1 vs2 =>
          cases v1 with
          | bool _ => rfl
          | setOfInt _ => rfl
          | array _ => rfl
          | int q =>
            cases vs2 with
            | nil => rfl
            | cons v2 vs3 =>
              cases v2 with
              | bool _ => rfl
              | setOfInt _ => rfl
              | array _ => rfl
              | int s =>
                cases vs3 with
                | nil => rfl
                | cons v3 vs4 =>
                  cases v3 with
                  | bool _ => rfl
                  | int _ => rfl
                  | setOfInt _ => rfl
                  | array d =>
                    cases vs4 with
                    | nil => rfl
                    | cons v4 vs5 =>
                      cases v4 with
                      | bool _ => rfl
                      | setOfInt _ => rfl
                      | array _ => rfl
                      | int q0 =>
                        cases vs5 with
                        | nil => rfl
                        | cons v5 vs6 =>
                          cases vs6 with
                          | cons _ _ => rfl
                          | nil =>
                            have hx : (valueInts xs).isSome =
                                (valueInts ys).isSome :=
                              valueInts_isSome_sameShape harr
                            simp only [nfaArgs]
                            cases h1 : valueInts xs with
                            | none =>
                              cases h2 : valueInts ys with
                              | none => rfl
                              | some ysL => simp [h1, h2] at hx
                            | some xsL =>
                              cases h2 : valueInts ys with
                              | none => simp [h1, h2] at hx
                              | some ysL =>
                                cases h3 : valueSets d with
                                | none => rfl
                                | some dL =>
                                  cases h4 : valueSet v5 with
                                  | none => rfl
                                  | some fv =>
                                    by_cases hg : 0 ≤ q ∧ 0 ≤ s ∧
                                        dL.length = q.toNat * s.toNat <;>
                                      simp [hg]

/-- The `fzn_cost_regular` decoder accepts exactly the same argument
    shapes. -/
theorem costRegularArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true) :
    (costRegularArgs vs).isSome = (costRegularArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead _ =>
      cases hhead with
      | bool _ _ => rfl
      | int _ _ => rfl
      | setOfInt _ _ => rfl
      | @array xs ys harr =>
        cases vs1 with
        | nil =>
          cases ws1 with
          | nil => simp [costRegularArgs]
          | cons _ _ =>
            cases params with
            | nil => simp [ArgsAgree] at h
            | cons _ _ => simp [ArgsAgree] at h
        | cons v1 vs2 =>
          cases ws1 with
          | nil =>
            cases params with
            | nil => simp [ArgsAgree] at h
            | cons _ _ => simp [ArgsAgree] at h
          | cons w1 ws2 =>
            obtain ⟨pre, a, b, hvsEq, hwsEq, hlastShape⟩ :=
              h.drop_one_eq_init_lastShape hpar (by simp) (by simp)
            have hvsTail : v1 :: vs2 = pre ++ [a] := by simpa using hvsEq
            have hwsTail : w1 :: ws2 = pre ++ [b] := by simpa using hwsEq
            rw [hvsTail, hwsTail]
            cases pre with
            | nil => simp [costRegularArgs]
            | cons p1 pre1 =>
              cases p1 with
              | bool _ => simp [costRegularArgs]
              | setOfInt _ => simp [costRegularArgs]
              | array _ => simp [costRegularArgs]
              | int q =>
                cases pre1 with
                | nil => simp [costRegularArgs]
                | cons p2 pre2 =>
                  cases p2 with
                  | bool _ => simp [costRegularArgs]
                  | setOfInt _ => simp [costRegularArgs]
                  | array _ => simp [costRegularArgs]
                  | int s =>
                    cases pre2 with
                    | nil => simp [costRegularArgs]
                    | cons p3 pre3 =>
                      cases p3 with
                      | bool _ => simp [costRegularArgs]
                      | int _ => simp [costRegularArgs]
                      | setOfInt _ => simp [costRegularArgs]
                      | array d =>
                        cases pre3 with
                        | nil => simp [costRegularArgs]
                        | cons p4 pre4 =>
                          cases p4 with
                          | bool _ => simp [costRegularArgs]
                          | setOfInt _ => simp [costRegularArgs]
                          | array _ => simp [costRegularArgs]
                          | int q0 =>
                            cases pre4 with
                            | nil => simp [costRegularArgs]
                            | cons p5 pre5 =>
                              cases pre5 with
                              | nil => simp [costRegularArgs]
                              | cons p6 pre6 =>
                                cases p6 with
                                | bool _ => simp [costRegularArgs]
                                | int _ => simp [costRegularArgs]
                                | setOfInt _ => simp [costRegularArgs]
                                | array cost =>
                                  cases pre6 with
                                  | cons _ _ => simp [costRegularArgs]
                                  | nil =>
                                    cases hlastShape with
                                    | bool _ _ => simp [costRegularArgs]
                                    | int ta tb =>
                                      have hx :
                                          (valueInts xs).isSome =
                                            (valueInts ys).isSome :=
                                        valueInts_isSome_sameShape harr
                                      simp only [List.nil_append,
                                        List.cons_append, costRegularArgs]
                                      cases h1 : valueInts xs with
                                      | none =>
                                        cases h2 : valueInts ys with
                                        | none => rfl
                                        | some ysL =>
                                          simp [h1, h2] at hx
                                      | some xsL =>
                                        cases h2 : valueInts ys with
                                        | none => simp [h1, h2] at hx
                                        | some ysL =>
                                          cases h3 : valueInts d with
                                          | none => rfl
                                          | some dL =>
                                            cases h4 : valueSet p5 with
                                            | none => rfl
                                            | some fv =>
                                              cases h5 :
                                                  valueInts cost with
                                              | none => rfl
                                              | some costL =>
                                                by_cases hg : 0 ≤ q ∧
                                                    0 ≤ s ∧
                                                    dL.length =
                                                      q.toNat * s.toNat ∧
                                                    costL.length =
                                                      q.toNat * s.toNat <;>
                                                  simp [hg]
                                    | setOfInt _ _ =>
                                      simp [costRegularArgs]
                                    | array _ => simp [costRegularArgs]

/-- The `fzn_mdd` and `fzn_mdd_nondet` decoders accept exactly the same
    argument shapes. -/
theorem mddArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params.drop 1, pt.isPar = true) :
    (mddArgs vs).isSome = (mddArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  have htail : vs.drop 1 = ws.drop 1 := ArgsAgree.drop_one_eq h hpar
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead _ =>
      have htail' : vs1 = ws1 := by simpa using htail
      subst htail'
      cases hhead with
      | bool _ _ => rfl
      | int _ _ => rfl
      | setOfInt _ _ => rfl
      | @array xs ys harr =>
        cases vs1 with
        | nil => rfl
        | cons v1 vs2 =>
          cases v1 with
          | bool _ => rfl
          | setOfInt _ => rfl
          | array _ => rfl
          | int n =>
            cases vs2 with
            | nil => rfl
            | cons v2 vs3 =>
              cases v2 with
              | bool _ => rfl
              | int _ => rfl
              | setOfInt _ => rfl
              | array level =>
                cases vs3 with
                | nil => rfl
                | cons v3 vs4 =>
                  cases v3 with
                  | bool _ => rfl
                  | setOfInt _ => rfl
                  | array _ => rfl
                  | int e =>
                    cases vs4 with
                    | nil => rfl
                    | cons v4 vs5 =>
                      cases v4 with
                      | bool _ => rfl
                      | int _ => rfl
                      | setOfInt _ => rfl
                      | array fromArr =>
                        cases vs5 with
                        | nil => rfl
                        | cons v5 vs6 =>
                          cases v5 with
                          | bool _ => rfl
                          | int _ => rfl
                          | setOfInt _ => rfl
                          | array label =>
                            cases vs6 with
                            | nil => rfl
                            | cons v6 vs7 =>
                              cases v6 with
                              | bool _ => rfl
                              | int _ => rfl
                              | setOfInt _ => rfl
                              | array to =>
                                cases vs7 with
                                | cons _ _ => rfl
                                | nil =>
                                  have hx : (valueInts xs).isSome =
                                      (valueInts ys).isSome :=
                                    valueInts_isSome_sameShape harr
                                  simp only [mddArgs]
                                  cases h1 : valueInts xs with
                                  | none =>
                                    cases h2 : valueInts ys with
                                    | none => rfl
                                    | some ysL => simp [h1, h2] at hx
                                  | some xsL =>
                                    cases h2 : valueInts ys with
                                    | none => simp [h1, h2] at hx
                                    | some ysL =>
                                      cases h3 : valueInts level with
                                      | none => rfl
                                      | some levelL =>
                                        cases h4 : valueInts fromArr with
                                        | none => rfl
                                        | some fromL =>
                                          cases h5 : valueSets label with
                                          | none => rfl
                                          | some labelL =>
                                            cases h6 : valueInts to with
                                            | none => rfl
                                            | some toL =>
                                              have hlen :
                                                  xsL.length = ysL.length :=
                                                valueInts_length_eq harr h1
                                                  h2
                                              have hgate :
                                                  mddGateB
                                                      ⟨xsL, n, levelL, e,
                                                        fromL, labelL,
                                                        toL⟩ =
                                                    mddGateB
                                                      ⟨ysL, n, levelL, e,
                                                        fromL, labelL,
                                                        toL⟩ :=
                                                mddGateB_congr hlen
                                              by_cases hg :
                                                  mddGateB
                                                    ⟨ysL, n, levelL, e,
                                                      fromL, labelL,
                                                      toL⟩ <;>
                                                simp [hgate, hg]

/-- The `fzn_cost_mdd` decoder accepts exactly the same argument shapes. -/
theorem costMddArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true) :
    (costMddArgs vs).isSome = (costMddArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead _ =>
      cases hhead with
      | bool _ _ => rfl
      | int _ _ => rfl
      | setOfInt _ _ => rfl
      | @array xs ys harr =>
        cases vs1 with
        | nil =>
          cases ws1 with
          | nil => simp [costMddArgs]
          | cons _ _ =>
            cases params with
            | nil => simp [ArgsAgree] at h
            | cons _ _ => simp [ArgsAgree] at h
        | cons v1 vs2 =>
          cases ws1 with
          | nil =>
            cases params with
            | nil => simp [ArgsAgree] at h
            | cons _ _ => simp [ArgsAgree] at h
          | cons w1 ws2 =>
            obtain ⟨pre, a, b, hvsEq, hwsEq, hlastShape⟩ :=
              h.drop_one_eq_init_lastShape hpar (by simp) (by simp)
            have hvsTail : v1 :: vs2 = pre ++ [a] := by simpa using hvsEq
            have hwsTail : w1 :: ws2 = pre ++ [b] := by simpa using hwsEq
            rw [hvsTail, hwsTail]
            cases pre with
            | nil => simp [costMddArgs]
            | cons p1 pre1 =>
              cases p1 with
              | bool _ => simp [costMddArgs]
              | setOfInt _ => simp [costMddArgs]
              | array _ => simp [costMddArgs]
              | int n =>
                cases pre1 with
                | nil => simp [costMddArgs]
                | cons p2 pre2 =>
                  cases p2 with
                  | bool _ => simp [costMddArgs]
                  | int _ => simp [costMddArgs]
                  | setOfInt _ => simp [costMddArgs]
                  | array level =>
                    cases pre2 with
                    | nil => simp [costMddArgs]
                    | cons p3 pre3 =>
                      cases p3 with
                      | bool _ => simp [costMddArgs]
                      | setOfInt _ => simp [costMddArgs]
                      | array _ => simp [costMddArgs]
                      | int e =>
                        cases pre3 with
                        | nil => simp [costMddArgs]
                        | cons p4 pre4 =>
                          cases p4 with
                          | bool _ => simp [costMddArgs]
                          | int _ => simp [costMddArgs]
                          | setOfInt _ => simp [costMddArgs]
                          | array fromArr =>
                            cases pre4 with
                            | nil => simp [costMddArgs]
                            | cons p5 pre5 =>
                              cases p5 with
                              | bool _ => simp [costMddArgs]
                              | int _ => simp [costMddArgs]
                              | setOfInt _ => simp [costMddArgs]
                              | array label =>
                                cases pre5 with
                                | nil => simp [costMddArgs]
                                | cons p6 pre6 =>
                                  cases p6 with
                                  | bool _ => simp [costMddArgs]
                                  | int _ => simp [costMddArgs]
                                  | setOfInt _ =>
                                    simp [costMddArgs]
                                  | array cost =>
                                    cases pre6 with
                                    | nil => simp [costMddArgs]
                                    | cons p7 pre7 =>
                                      cases p7 with
                                      | bool _ => simp [costMddArgs]
                                      | int _ => simp [costMddArgs]
                                      | setOfInt _ =>
                                        simp [costMddArgs]
                                      | array to =>
                                        cases pre7 with
                                        | cons _ _ =>
                                          simp [costMddArgs]
                                        | nil =>
                                          cases hlastShape with
                                          | bool _ _ =>
                                            simp [costMddArgs]
                                          | int ta tb =>
                                            have hx :
                                                (valueInts xs).isSome =
                                                  (valueInts ys).isSome :=
                                              valueInts_isSome_sameShape
                                                harr
                                            simp only [List.nil_append,
                                              List.cons_append,
                                              costMddArgs]
                                            cases h1 : valueInts xs with
                                            | none =>
                                              cases h2 : valueInts ys with
                                              | none => rfl
                                              | some ysL =>
                                                simp [h1, h2] at hx
                                            | some xsL =>
                                              cases h2 :
                                                  valueInts ys with
                                              | none =>
                                                simp [h1, h2] at hx
                                              | some ysL =>
                                                cases h3 :
                                                    valueInts level with
                                                | none => rfl
                                                | some levelL =>
                                                  cases h4 :
                                                      valueInts fromArr with
                                                  | none => rfl
                                                  | some fromL =>
                                                    cases h5 :
                                                        valueSets label with
                                                    | none => rfl
                                                    | some labelL =>
                                                      cases h6 :
                                                          valueInts cost with
                                                      | none => rfl
                                                      | some costL =>
                                                        cases h7 :
                                                            valueInts to with
                                                        | none => rfl
                                                        | some toL =>
                                                          have hlen :
                                                              xsL.length =
                                                                ysL.length :=
                                                            valueInts_length_eq
                                                              harr h1 h2
                                                          have hgate :
                                                              mddGateB
                                                                  ⟨xsL, n,
                                                                    levelL,
                                                                    e, fromL,
                                                                    labelL,
                                                                    toL⟩ =
                                                                mddGateB
                                                                  ⟨ysL, n,
                                                                    levelL,
                                                                    e, fromL,
                                                                    labelL,
                                                                    toL⟩ :=
                                                            mddGateB_congr
                                                              hlen
                                                          have hcostgate :
                                                              costMddGateB
                                                                  ⟨xsL, n,
                                                                    levelL,
                                                                    e, fromL,
                                                                    labelL,
                                                                    toL⟩
                                                                  costL =
                                                                costMddGateB
                                                                  ⟨ysL, n,
                                                                    levelL,
                                                                    e, fromL,
                                                                    labelL,
                                                                    toL⟩
                                                                  costL :=
                                                            costMddGateB_congr
                                                              hlen
                                                          by_cases hg :
                                                              mddGateB
                                                                ⟨ysL, n,
                                                                  levelL, e,
                                                                  fromL,
                                                                  labelL,
                                                                  toL⟩ &&
                                                              costMddGateB
                                                                ⟨ysL, n,
                                                                  levelL, e,
                                                                  fromL,
                                                                  labelL,
                                                                  toL⟩
                                                                costL <;>
                                                            simp [hgate,
                                                              hcostgate,
                                                              hg]
                                          | setOfInt _ _ =>
                                            simp [costMddArgs]
                                          | array _ =>
                                            simp [costMddArgs]

/-- The parameter condition needed by one branch of `regularDecodes`: every
    argument position after the first is `par`, except that the trailing
    `total` of the two cost signatures is only stored, not inspected, so it
    may be a variable. -/
def regularDecodesParamsOK (n : String) (params : List PredParamType) : Prop :=
  match n with
  | "fzn_cost_regular" | "fzn_cost_mdd" =>
      ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true
  | _ => ∀ pt ∈ params.drop 1, pt.isPar = true

/-- The decodability gate is invariant under `ArgsAgree`, provided the
    statically known arguments that the gate inspects are `par`. -/
theorem regularDecodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String)
    (hpar : regularDecodesParamsOK n params) :
    regularDecodes n vs = regularDecodes n ws := by
  unfold regularDecodes
  split
  · simpa [regularDecodesParamsOK] using
      regularArgs_isSome_agree h hpar
  · simpa [regularDecodesParamsOK] using
      nfaArgs_isSome_agree h hpar
  · simpa [regularDecodesParamsOK] using
      costRegularArgs_isSome_agree h hpar
  · simpa [regularDecodesParamsOK] using
      mddArgs_isSome_agree h hpar
  · simpa [regularDecodesParamsOK] using
      mddArgs_isSome_agree h hpar
  · simpa [regularDecodesParamsOK] using
      costMddArgs_isSome_agree h hpar
  · rfl

/-! ## Last-position congruence for the two cost decoders

`costRegularArgs` and `costMddArgs` pattern-match their trailing `total`
argument as an `int` but never inspect its value.  The lemmas below record
that the decoders' `isSome` therefore depends on the last argument only
through its constructor, provided the shared prefix is literally the same.

These support the weakened cost agreement lemmas below: for the two cost
names, the last `globalsSig` position is the variable total-cost output, so
`ArgsAgree` there yields only `SameShape`, not equality. -/

/-- `ArgsAgree` is stable under dropping the first argument. -/
theorem argsAgree_drop_one {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws) :
    ArgsAgree (params.drop 1) (vs.drop 1) (ws.drop 1) := by
  cases vs with
  | nil =>
    cases params with
    | nil =>
      cases ws with
      | nil => trivial
      | cons _ _ => cases h
    | cons _ _ => cases h
  | cons v vs' =>
    cases params with
    | nil => cases h
    | cons pt pts =>
      cases ws with
      | nil => cases h
      | cons _ ws' =>
        obtain ⟨-, h1⟩ := h
        exact h1

/-- `ArgsAgree` is stable under dropping the last argument. -/
theorem argsAgree_dropLast {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws) :
    ArgsAgree params.dropLast vs.dropLast ws.dropLast := by
  induction vs generalizing params ws with
  | nil =>
    cases params with
    | nil =>
      cases ws with
      | nil => trivial
      | cons _ _ => cases h
    | cons _ _ => cases h
  | cons v vs ih =>
    cases params with
    | nil => cases h
    | cons pt pts =>
      cases ws with
      | nil => cases h
      | cons w ws =>
        obtain ⟨h0, h1⟩ := h
        cases pts with
        | nil =>
          cases vs with
          | nil =>
            cases ws with
            | nil => trivial
            | cons _ _ => cases h1
          | cons _ _ => cases h1
        | cons q qs =>
          cases vs with
          | nil => cases h1
          | cons v2 vs2 =>
            cases ws with
            | nil => cases h1
            | cons w2 ws2 =>
              exact ⟨h0, ih h1⟩

/-- With all `par` positions except the first and the last, `ArgsAgree`
    forces the two argument lists to coincide on their common middle. -/
theorem argsAgree_drop_one_dropLast_eq {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true) :
    (vs.drop 1).dropLast = (ws.drop 1).dropLast :=
  ArgsAgree.eq_of_all_par (argsAgree_dropLast (argsAgree_drop_one h)) hpar

/-- Every nonempty list is its `dropLast` with its last element re-appended. -/
theorem exists_eq_dropLast_append_last {vs : List Value} (h : vs ≠ []) :
    ∃ last, vs = vs.dropLast ++ [last] := by
  induction vs with
  | nil => exact absurd rfl h
  | cons v vs ih =>
    cases vs with
    | nil => exact ⟨v, by simp⟩
    | cons w ws =>
      obtain ⟨last, hlast⟩ := ih (by simp)
      refine ⟨last, ?_⟩
      rw [List.dropLast_cons_of_ne_nil (by simp), List.cons_append, ← hlast]

/-- Pointwise shape agreement of two lists with a common prefix and a final
    element forces shape agreement of the final elements. -/
theorem listSameShape_append_last {R : Value → Value → Prop}
    {l : List Value} {vl wl : Value}
    (h : ListSameShape R (l ++ [vl]) (l ++ [wl])) : R vl wl := by
  induction l with
  | nil => cases h with | cons h _ => exact h
  | cons a l ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons _ htail => exact ih htail

/-- `costRegularArgs` sees its first and last arguments only through their
    constructors; the shared middle is common to both calls. -/
theorem costRegularArgs_isSome_congr_ends {v w vl wl : Value}
    {mid : List Value} (hv : v.SameShape w) (hl : vl.SameShape wl) :
    (costRegularArgs (v :: (mid ++ [vl]))).isSome =
      (costRegularArgs (w :: (mid ++ [wl]))).isSome := by
  cases hv with
  | bool _ _ => cases hl <;> rfl
  | int _ _ => cases hl <;> rfl
  | setOfInt _ _ => cases hl <;> rfl
  | @array xsArr ysArr harr =>
    have hx : (valueInts xsArr).isSome = (valueInts ysArr).isSome :=
      valueInts_isSome_sameShape harr
    rcases mid with _ | ⟨m1, mid1⟩
    · cases hl <;> rfl
    cases m1 with
    | bool => rfl
    | setOfInt => rfl
    | array => rfl
    | int q =>
      rcases mid1 with _ | ⟨m2, mid2⟩
      · cases hl <;> rfl
      cases m2 with
      | bool => rfl
      | setOfInt => rfl
      | array => rfl
      | int s =>
        rcases mid2 with _ | ⟨m3, mid3⟩
        · cases hl <;> rfl
        cases m3 with
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
        | array d =>
          rcases mid3 with _ | ⟨m4, mid4⟩
          · cases hl <;> rfl
          cases m4 with
          | bool => rfl
          | setOfInt => rfl
          | array => rfl
          | int q0 =>
            rcases mid4 with _ | ⟨m5, mid5⟩
            · cases hl <;> rfl
            rcases mid5 with _ | ⟨m6, mid6⟩
            · cases hl <;> rfl
            cases m6 with
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
            | array cost =>
              rcases mid6 with _ | ⟨m7, mid7⟩
              · simp only [List.cons_append, List.nil_append]
                cases hl with
                | bool _ _ => rfl
                | setOfInt _ _ => rfl
                | array _ => rfl
                | int i i' =>
                  simp only [costRegularArgs]
                  cases h1 : valueInts xsArr with
                  | none =>
                    cases h2 : valueInts ysArr with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx
                  | some xsL =>
                    cases h2 : valueInts ysArr with
                    | none => simp [h1, h2] at hx
                    | some ysL =>
                      cases h3 : valueInts d with
                      | none => rfl
                      | some dL =>
                        cases m5 with
                        | bool => rfl
                        | int => rfl
                        | array => rfl
                        | setOfInt s0 =>
                          cases h4 : valueInts cost with
                          | none => rfl
                          | some costL =>
                            by_cases hg : 0 ≤ q ∧ 0 ≤ s ∧
                                dL.length = q.toNat * s.toNat ∧
                                costL.length = q.toNat * s.toNat <;>
                              simp [valueSet, hg]
              · cases m7 with
                | bool => rfl
                | setOfInt => rfl
                | array => rfl
                | int => cases mid7 <;> rfl

/-- `costMddArgs` sees its first and last arguments only through their
    constructors; the shared middle is common to both calls. -/
theorem costMddArgs_isSome_congr_ends {v w vl wl : Value}
    {mid : List Value} (hv : v.SameShape w) (hl : vl.SameShape wl) :
    (costMddArgs (v :: (mid ++ [vl]))).isSome =
      (costMddArgs (w :: (mid ++ [wl]))).isSome := by
  cases hv with
  | bool _ _ => cases hl <;> rfl
  | int _ _ => cases hl <;> rfl
  | setOfInt _ _ => cases hl <;> rfl
  | @array xsArr ysArr harr =>
    have hx : (valueInts xsArr).isSome = (valueInts ysArr).isSome :=
      valueInts_isSome_sameShape harr
    rcases mid with _ | ⟨m1, mid1⟩
    · cases hl <;> rfl
    cases m1 with
    | bool => rfl
    | setOfInt => rfl
    | array => rfl
    | int n =>
      rcases mid1 with _ | ⟨m2, mid2⟩
      · cases hl <;> rfl
      cases m2 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | array level =>
        rcases mid2 with _ | ⟨m3, mid3⟩
        · cases hl <;> rfl
        cases m3 with
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
        | int e =>
          rcases mid3 with _ | ⟨m4, mid4⟩
          · cases hl <;> rfl
          cases m4 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | array fromArr =>
            rcases mid4 with _ | ⟨m5, mid5⟩
            · cases hl <;> rfl
            cases m5 with
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
            | array label =>
              rcases mid5 with _ | ⟨m6, mid6⟩
              · cases hl <;> rfl
              cases m6 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | array cost =>
                rcases mid6 with _ | ⟨m7, mid7⟩
                · cases hl <;> rfl
                cases m7 with
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
                | array to =>
                  rcases mid7 with _ | ⟨m8, mid8⟩
                  · simp only [List.cons_append, List.nil_append]
                    cases hl with
                    | bool _ _ => rfl
                    | setOfInt _ _ => rfl
                    | array _ => rfl
                    | int i i' =>
                      simp only [costMddArgs]
                      cases h1 : valueInts xsArr with
                      | none =>
                        cases h2 : valueInts ysArr with
                        | none => rfl
                        | some _ => simp [h1, h2] at hx
                      | some xsL =>
                        cases h2 : valueInts ysArr with
                        | none => simp [h1, h2] at hx
                        | some ysL =>
                          cases h3 : valueInts level with
                          | none => rfl
                          | some levelL =>
                            cases h4 : valueInts fromArr with
                            | none => rfl
                            | some fromL =>
                              cases h5 : valueSets label with
                              | none => rfl
                              | some labelL =>
                                cases h6 : valueInts cost with
                                | none => rfl
                                | some costL =>
                                  cases h7 : valueInts to with
                                  | none => rfl
                                  | some toL =>
                                    have hlen : xsL.length = ysL.length :=
                                      valueInts_length_eq harr h1 h2
                                    have hgate :
                                        mddGateB ⟨xsL, n, levelL, e, fromL,
                                            labelL, toL⟩ =
                                          mddGateB ⟨ysL, n, levelL, e, fromL,
                                            labelL, toL⟩ :=
                                      mddGateB_congr hlen
                                    have hcostgate :
                                        costMddGateB ⟨xsL, n, levelL, e,
                                            fromL, labelL, toL⟩ costL =
                                          costMddGateB ⟨ysL, n, levelL, e,
                                            fromL, labelL, toL⟩ costL :=
                                      costMddGateB_congr hlen
                                    by_cases hg :
                                        mddGateB ⟨ysL, n, levelL, e, fromL,
                                          labelL, toL⟩ &&
                                        costMddGateB ⟨ysL, n, levelL, e,
                                          fromL, labelL, toL⟩ costL <;>
                                      simp [hgate, hcostgate, hg]
                  · cases m8 with
                    | bool => rfl
                    | setOfInt => rfl
                    | array => rfl
                    | int => cases mid8 <;> rfl

/-- `costRegularArgs` accepts the same argument shapes when the trailing
    total-cost position is only shape-agreeing (its value is never read). -/
theorem costRegularArgs_isSome_agree_weak {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true) :
    (costRegularArgs vs).isSome = (costRegularArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  have hmid : (vs.drop 1).dropLast = (ws.drop 1).dropLast :=
    argsAgree_drop_one_dropLast_eq h hpar
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      rcases vs1 with _ | ⟨v1, vs2⟩
      · have hws1 : ws1 = [] := by cases htail; rfl
        subst hws1
        simp [costRegularArgs]
      · rcases ws1 with _ | ⟨w1, ws2⟩
        · cases htail
        · obtain ⟨vl, hvl⟩ :=
            exists_eq_dropLast_append_last (vs := v1 :: vs2) (by simp)
          obtain ⟨wl, hwl⟩ :=
            exists_eq_dropLast_append_last (vs := w1 :: ws2) (by simp)
          have hmid' : (v1 :: vs2).dropLast = (w1 :: ws2).dropLast := hmid
          rw [hvl, hwl, ← hmid'] at htail
          have hlast : vl.SameShape wl := listSameShape_append_last htail
          have hvl' : v0 :: (v1 :: vs2) =
              v0 :: ((v1 :: vs2).dropLast ++ [vl]) := congrArg _ hvl
          have hwl'' : w1 :: ws2 = (v1 :: vs2).dropLast ++ [wl] := by
            rw [hwl, ← hmid']
          have hwl' : w0 :: (w1 :: ws2) =
              w0 :: ((v1 :: vs2).dropLast ++ [wl]) := congrArg _ hwl''
          rw [hvl', hwl']
          exact costRegularArgs_isSome_congr_ends hhead hlast

/-- `costMddArgs` accepts the same argument shapes when the trailing
    total-cost position is only shape-agreeing (its value is never read). -/
theorem costMddArgs_isSome_agree_weak {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true) :
    (costMddArgs vs).isSome = (costMddArgs ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  have hmid : (vs.drop 1).dropLast = (ws.drop 1).dropLast :=
    argsAgree_drop_one_dropLast_eq h hpar
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      rcases vs1 with _ | ⟨v1, vs2⟩
      · have hws1 : ws1 = [] := by cases htail; rfl
        subst hws1
        simp [costMddArgs]
      · rcases ws1 with _ | ⟨w1, ws2⟩
        · cases htail
        · obtain ⟨vl, hvl⟩ :=
            exists_eq_dropLast_append_last (vs := v1 :: vs2) (by simp)
          obtain ⟨wl, hwl⟩ :=
            exists_eq_dropLast_append_last (vs := w1 :: ws2) (by simp)
          have hmid' : (v1 :: vs2).dropLast = (w1 :: ws2).dropLast := hmid
          rw [hvl, hwl, ← hmid'] at htail
          have hlast : vl.SameShape wl := listSameShape_append_last htail
          have hvl' : v0 :: (v1 :: vs2) =
              v0 :: ((v1 :: vs2).dropLast ++ [vl]) := congrArg _ hvl
          have hwl'' : w1 :: ws2 = (v1 :: vs2).dropLast ++ [wl] := by
            rw [hwl, ← hmid']
          have hwl' : w0 :: (w1 :: ws2) =
              w0 :: ((v1 :: vs2).dropLast ++ [wl]) := congrArg _ hwl''
          rw [hvl', hwl']
          exact costMddArgs_isSome_congr_ends hhead hlast

/-- Which signature positions must be `par` for the value-inspecting
    regular-family decoders.  The two cost predicates have a trailing
    variable total whose value is not inspected. -/
def regularGateParB (n : String) (params : List PredParamType) : Bool :=
  match n with
  | "fzn_cost_regular" | "fzn_cost_mdd" =>
      (params.drop 1).dropLast.all (fun pt => pt.isPar)
  | "fzn_regular" | "fzn_regular_nfa" | "fzn_mdd" | "fzn_mdd_nondet" =>
      (params.drop 1).all (fun pt => pt.isPar)
  | _ => true

/-- The decodability gate is invariant under `ArgsAgree`, provided the
    positions the gate actually inspects are `par`: every position after the
    first for the four non-cost names, and every such position except the
    trailing total-cost output for the two cost names. -/
theorem regularDecodes_agree_gated {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String)
    (hgate : regularGateParB n params = true) :
    regularDecodes n vs = regularDecodes n ws := by
  unfold regularDecodes
  split
  · exact regularArgs_isSome_agree h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · exact nfaArgs_isSome_agree h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · exact costRegularArgs_isSome_agree_weak h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · exact mddArgs_isSome_agree h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · exact mddArgs_isSome_agree h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · exact costMddArgs_isSome_agree_weak h
      (List.all_eq_true.mp (by simpa [regularGateParB] using hgate))
  · rfl

end LeanFzn.Semantics.Globals.Regular

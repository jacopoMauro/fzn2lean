import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Circuit and graph global constraints

Mathematical interpretations (`graphInterp`) and executable Boolean
twins (`graphInterpB`) for the circuit and graph predicates of the
pinned MiniZinc 2.10.0 tree, per the decompositions recorded in
`specification/flatzinc_specification_assumptions.md`, G25 and G29:

* `fzn_circuit(xs)` / `fzn_subcircuit(xs)` (`fzn_circuit.mzn`,
  `fzn_subcircuit.mzn`): successor-array Hamiltonian cycle
  constraints over 1-based positions; `xs[i] = i` marks a node out
  of the subcircuit; the empty subcircuit is allowed.
* The graph family (`fzn_subgraph`, `fzn_dag`, `fzn_connected`,
  `fzn_dconnected`, `fzn_dreachable`, `fzn_reachable`, `fzn_dtree`,
  `fzn_tree`, `fzn_dpath`, `fzn_path`, `fzn_bounded_dpath`,
  `fzn_bounded_path`, `fzn_dsteiner`, `fzn_steiner`, `fzn_dwst`,
  `fzn_wst`): par `from`/`to` edge arrays over nodes `1..N` plus
  `ns`/`es` var-bool selections (the int form's leading `N`, `E`
  parameters are recovered from the array lengths, matching the enum
  form's signatures).

**Representation discipline:** every position in the twins is a
1-based `Nat`; the par node ids of the edge arrays are `Int` values
compared with `Int.ofNat`-cast positions; the var roots/sources of
`reachable`/`tree`/`path` arrive as `Int` values and are converted
once, with an in-range guard (a nonpositive or oversized root makes
the predicate false).  Reachability is decided by a BFS-style fixed
point over the selected edges.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Graph

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## Index helpers -/

/-- 1-based Bool lookup in a selection list (out of range: false). -/
private def selAt (bs : List Bool) (i : Nat) : Bool :=
  bs[i - 1]?.getD false

/-- 1-based Int lookup in a par list (out of range: 0). -/
private def intAt (xs : List Int) (i : Nat) : Int :=
  xs[i - 1]?.getD 0

/-- In-range guard for an Int node id: `1 ≤ i ≤ N`? -/
private def inRange (i : Int) (n : Nat) : Bool :=
  decide (1 ≤ i ∧ i ≤ (n : Int))

/-! ## Circuit -/

/-- Positions `1..n` visited by iterating the successor `xs` from
    position `start` for `fuel` steps. -/
private def orbitFrom (xs : List Int) : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, start =>
      start :: orbitFrom xs fuel (xs.getD (start.toNat - 1) 0)

/-- A core shared by Prop and twin: the orbit of `xs` from position 1
    has n pairwise-distinct nodes. -/
private def orbitOk (xs : List Int) : Bool :=
  let orb := orbitFrom xs xs.length 1
  orb.length == xs.length && orb.eraseDups.length == xs.length

/-- `fzn_circuit(xs)`: a single cycle over all `1..n` (per
    `fzn_circuit.mzn`: a fixed-point-free permutation of `1..n` whose
    successor iteration from 1 visits all n positions; empty ⇒ true
    is vacuous since n = 0 fails the first conjunct's absence — the
    decomposition guards `length = 0` with `true`). -/
def circuitProp (xs : List Int) : Prop :=
  (xs.length = 0) ∨
    (0 < xs.length ∧
      (List.range xs.length).all (fun i =>
        match xs[i]? with
        | some v => 1 ≤ v ∧ v ≤ (xs.length : Int) ∧
            xs.count v = 1 ∧ v ≠ (i : Int) + 1
        | none => decide False = true) ∧
      orbitOk xs = true)

/-- Boolean twin of `circuitProp`. -/
def circuitB (xs : List Int) : Bool :=
  (xs.length == 0) ||
    (decide (0 < xs.length) &&
      (List.range xs.length).all (fun i =>
        match xs[i]? with
        | some v => decide (1 ≤ v ∧ v ≤ (xs.length : Int) ∧
            xs.count v = 1 ∧ v ≠ (i : Int) + 1)
        | none => false) &&
      orbitOk xs)

theorem circuitB_iff (xs : List Int) : circuitB xs = true ↔ circuitProp xs := by
  unfold circuitB circuitProp orbitOk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_iff, decide_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_iff, List.all_eq_true, beq_iff_eq, beq_iff_eq,
    Bool.and_eq_true]
  constructor
  · rintro (h0 | ⟨⟨h2, h3⟩, h4⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨h2, h3, h4⟩
  · rintro (h0 | ⟨h2, ⟨h3, h4⟩⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨⟨h2, h3⟩, h4⟩

/-- The non-fixed positions of `xs` (1-based). -/
private def inPositions (xs : List Int) : List Nat :=
  (List.range xs.length).filter (fun i => xs[i]?.getD 0 ≠ (i : Int) + 1)

/-- Shared core: the in-positions form one single cycle.  The
    in-positions are 0-based, so the orbit starts at the 1-based
    position `(ins.getD 0 0) + 1`. -/
private def subcircuitCore (xs : List Int) : Bool :=
  let ins := inPositions xs
  ins.isEmpty ||
    (((orbitFrom xs ins.length (((ins.getD 0 0) : Int) + 1)).eraseDups.length
        == ins.length) &&
      ((List.range ins.length).all (fun k =>
        decide ((orbitFrom xs ins.length (((ins.getD 0 0) : Int) + 1)).getD k 0
          ∈ (ins.map (fun i => Int.ofNat i + 1) : List Int)))))

/-- `fzn_subcircuit(xs)`: every value in `1..n`; the non-fixed
    positions form one single cycle (or there are none: the empty
    subcircuit is allowed). -/
def subcircuitProp (xs : List Int) : Prop :=
  (List.range xs.length).all (fun i =>
    match xs[i]? with
    | some v => decide (1 ≤ v ∧ v ≤ (xs.length : Int))
    | none => false) = true ∧
    subcircuitCore xs = true

/-- Boolean twin of `subcircuitProp`. -/
def subcircuitB (xs : List Int) : Bool :=
  (List.range xs.length).all (fun i =>
    match xs[i]? with
    | some v => decide (1 ≤ v ∧ v ≤ (xs.length : Int))
    | none => false) &&
    subcircuitCore xs

theorem subcircuitB_iff (xs : List Int) :
    subcircuitB xs = true ↔ subcircuitProp xs := by
  simp only [subcircuitB, subcircuitProp, Bool.and_eq_true, List.all_eq_true]

/-! ## Graph inputs -/

/-- A graph constraint input: par edge arrays and var selections. -/
structure GraphInput where
  /-- Par `from` endpoints (node ids, 1-based). -/
  fromArr : List Int
  /-- Par `to` endpoints. -/
  toArr : List Int
  /-- Node selection. -/
  ns : List Bool
  /-- Edge selection. -/
  es : List Bool
  deriving Repr

/-- `fzn_subgraph`: every selected edge has both endpoints
    selected. -/
def subgraphProp (g : GraphInput) : Prop :=
  (List.range g.es.length).all (fun e =>
    (selAt g.es (e + 1) = true →
      selAt g.ns (intAt g.fromArr (e + 1)).toNat = true ∧
        selAt g.ns (intAt g.toArr (e + 1)).toNat = true)) ∧
    (List.range g.es.length).all (fun e =>
      (selAt g.es (e + 1) = true →
        1 ≤ intAt g.fromArr (e + 1) ∧ intAt g.fromArr (e + 1) ≤ (g.ns.length : Int) ∧
          1 ≤ intAt g.toArr (e + 1) ∧ intAt g.toArr (e + 1) ≤ (g.ns.length : Int)))

/-- Boolean twin of `subgraphProp`. -/
def subgraphB (g : GraphInput) : Bool :=
  (List.range g.es.length).all (fun e =>
    !(selAt g.es (e + 1)) ||
      (selAt g.ns (intAt g.fromArr (e + 1)).toNat &&
        selAt g.ns (intAt g.toArr (e + 1)).toNat)) &&
    (List.range g.es.length).all (fun e =>
      !(selAt g.es (e + 1)) ||
        (decide (1 ≤ intAt g.fromArr (e + 1)) &&
          decide (intAt g.fromArr (e + 1) ≤ (g.ns.length : Int)) &&
          decide (1 ≤ intAt g.toArr (e + 1)) &&
          decide (intAt g.toArr (e + 1) ≤ (g.ns.length : Int))))

theorem subgraphB_iff (g : GraphInput) :
    subgraphB g = true ↔ subgraphProp g := by
  simp only [subgraphB, subgraphProp, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro x hx hsel
      have := h1 x hx
      rcases this with hfalse | hval
      · rw [hfalse] at hsel; exact absurd hsel (by simp)
      · exact hval
    · intro x hx hsel
      have := h2 x hx
      rcases this with hfalse | ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
      · rw [hfalse] at hsel; exact absurd hsel (by simp)
      · exact ⟨ha, hb, hc, hd⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases hsel : selAt g.es (x + 1) = true
      · rw [hsel]
        simpa using h1 x hx hsel
      · rw [show selAt g.es (x + 1) = false from by
          cases h : selAt g.es (x + 1) <;> simp_all]
        simp
    · intro x hx
      by_cases hsel : selAt g.es (x + 1) = true
      · rw [hsel]
        obtain ⟨ha, hb, hc, hd⟩ := h2 x hx hsel
        exact Or.inr ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
      · rw [show selAt g.es (x + 1) = false from by
          cases h : selAt g.es (x + 1) <;> simp_all]
        simp

/-- The neighbours of node `n` (1-based Nat) along selected edges,
    directed or undirected. -/
def neighbours (directed : Bool) (g : GraphInput) (n : Nat) :
    List Int :=
  (List.range g.es.length).filterMap (fun e =>
    if selAt g.es (e + 1) then
      if intAt g.fromArr (e + 1) = (n : Int) then
        some (intAt g.toArr (e + 1))
      else if !directed ∧ intAt g.toArr (e + 1) = (n : Int) then
        some (intAt g.fromArr (e + 1))
      else none
    else none)

/-- One BFS round: all unvisited neighbours of the seen nodes. -/
def bfsRound (directed : Bool) (g : GraphInput) (seen : List Int) :
    List Int :=
  seen.foldl (fun acc n =>
    ((neighbours directed g n.toNat).filter (fun m =>
      !(acc.contains m) ∧ !(seen.contains m))) ++ acc) []

/-- Reachable node ids from `start` (1-based Nat position) by BFS to
    a fixed point (bounded by the node count). -/
def reachFrom (directed : Bool) (g : GraphInput) (start : Nat) :
    List Int :=
  let rec step : List Int → Nat → List Int
    | seen, 0 => seen
    | seen, fuel + 1 =>
        let newNodes := bfsRound directed g seen
        if newNodes.isEmpty then seen else step (seen ++ newNodes) fuel
  step [(start : Int)] g.ns.length

/-- `fzn_dreachable`/`fzn_reachable`: `root` is a selected node id
    in `1..N`, and the selected nodes are exactly those reachable
    from it (directed resp. undirected selected subgraph). -/
def reachableProp (directed : Bool) (g : GraphInput) (root : Int) : Prop :=
  inRange root g.ns.length = true ∧
    decide (selAt g.ns root.toNat = true) = true ∧
    (List.range g.ns.length).all (fun n =>
      (selAt g.ns (n + 1) == decide ((reachFrom directed g root.toNat).contains
        ((n : Int) + 1)))) = true

def reachableB (directed : Bool) (g : GraphInput) (root : Int) : Bool :=
  inRange root g.ns.length && decide (selAt g.ns root.toNat = true) &&
    (List.range g.ns.length).all (fun n =>
      (selAt g.ns (n + 1) == decide ((reachFrom directed g root.toNat).contains
        ((n : Int) + 1))))

theorem reachableB_iff (directed : Bool) (g : GraphInput) (root : Int) :
    reachableB directed g root = true ↔ reachableProp directed g root := by
  simp only [reachableB, reachableProp, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- `fzn_connected`/`fzn_dconnected`: some selected node reaches
    exactly the selected set. -/
def connectedProp (directed : Bool) (g : GraphInput) : Prop :=
  ∃ root, reachableProp directed g root

def connectedB (directed : Bool) (g : GraphInput) : Bool :=
  (List.range g.ns.length).any (fun n =>
    reachableB directed g ((n : Int) + 1))

theorem connectedB_iff (directed : Bool) (g : GraphInput) :
    connectedB directed g = true ↔ connectedProp directed g := by
  simp only [connectedB, connectedProp, List.any_eq_true, reachableB_iff]
  constructor
  · rintro ⟨n, hn, hreach⟩
    exact ⟨(n : Int) + 1, hreach.1, hreach.2.1, hreach.2.2⟩
  · rintro ⟨root, h1, h2, h3⟩
    have hb1 : 1 ≤ root := by
      have := of_decide_eq_true h1
      exact this.1
    have hb2 : root ≤ (g.ns.length : Int) := by
      have := of_decide_eq_true h1
      exact this.2
    have hsub : ((root - 1).toNat : Int) < g.ns.length := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      omega
    have hn : (root - 1).toNat < g.ns.length := by
      have : ((root - 1).toNat : Int) < (g.ns.length : Int) := hsub
      omega
    have hkey : ((root - 1).toNat : Int) + 1 = root := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      omega
    refine ⟨(root - 1).toNat, List.mem_range.mpr hn, ?_, ?_, ?_⟩
    · simp only [inRange, decide_eq_true_iff]
      omega
    · rw [show ((root - 1).toNat : Int) + 1 = root from hkey]
      exact h2
    · rw [show ((root - 1).toNat : Int) + 1 = root from hkey]
      exact h3

/-- `fzn_dag`: the selected directed subgraph is acyclic: no selected
    edge leads back to its own source. -/
def dagProp (g : GraphInput) : Prop :=
  (List.range g.es.length).all (fun e =>
    (selAt g.es (e + 1) = false ∨
      (reachFrom true g (intAt g.toArr (e + 1)).toNat).contains
          (intAt g.fromArr (e + 1)) = false))

def dagB (g : GraphInput) : Bool :=
  (List.range g.es.length).all (fun e =>
    !(selAt g.es (e + 1)) ||
      !((reachFrom true g (intAt g.toArr (e + 1)).toNat).contains
          (intAt g.fromArr (e + 1))))

theorem dagB_iff (g : GraphInput) : dagB g = true ↔ dagProp g := by
  simp only [dagB, dagProp, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_iff]

/-- Edge-induced weight of a selection. -/
private def weightOf (w : List Int) (g : GraphInput) : Int :=
  (List.range g.es.length).foldl (fun acc e =>
    if selAt g.es (e + 1) then acc + intAt w (e + 1) else acc) 0

/-- `fzn_dtree`/`fzn_tree`: the selected edges form an arborescence
    rooted at `root` spanning exactly the selected nodes: `root`
    selected, every selected node reachable from `root`, and
    (#selected nodes) = (#selected edges) + 1. -/
def treeProp (directed : Bool) (g : GraphInput) (root : Int) : Prop :=
  inRange root g.ns.length = true ∧
    decide (selAt g.ns root.toNat = true) = true ∧
    (List.range g.ns.length).all (fun n =>
      (selAt g.ns (n + 1) == decide ((reachFrom directed g root.toNat).contains
        ((n : Int) + 1)))) ∧
    (List.range g.ns.length).countP (fun n => selAt g.ns (n + 1)) =
      (List.range g.es.length).countP (fun e => selAt g.es (e + 1)) + 1

def treeB (directed : Bool) (g : GraphInput) (root : Int) : Bool :=
  inRange root g.ns.length && decide (selAt g.ns root.toNat = true) &&
    (List.range g.ns.length).all (fun n =>
      (selAt g.ns (n + 1) == decide ((reachFrom directed g root.toNat).contains
        ((n : Int) + 1)))) &&
    decide ((List.range g.ns.length).countP (fun n => selAt g.ns (n + 1)) =
      (List.range g.es.length).countP (fun e => selAt g.es (e + 1)) + 1)

theorem treeB_iff (directed : Bool) (g : GraphInput) (root : Int) :
    treeB directed g root = true ↔ treeProp directed g root := by
  simp only [treeB, treeProp, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨h1, h2, h3, of_decide_eq_true h4⟩
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨⟨⟨h1, h2⟩, h3⟩, by
      simp only [decide_eq_true_eq]
      exact h4⟩

/-- Selected in-degree of node id `n`. -/
def inDeg (g : GraphInput) (n : Int) : Nat :=
  (List.range g.es.length).countP (fun e =>
    selAt g.es (e + 1) ∧ intAt g.toArr (e + 1) = n)

/-- Selected out-degree of node id `n`. -/
def outDeg (g : GraphInput) (n : Int) : Nat :=
  (List.range g.es.length).countP (fun e =>
    selAt g.es (e + 1) ∧ intAt g.fromArr (e + 1) = n)

/-- `fzn_dpath`/`fzn_path`: the selected nodes form a simple path
    from `source` to `sink`: a tree rooted at `source` where the
    source has no incoming selected edge, the sink no outgoing one,
    and every other selected node has exactly one incoming and one
    outgoing selected edge. -/
def pathProp (directed : Bool) (g : GraphInput) (source sink : Int) : Prop :=
  treeProp directed g source ∧
    (List.range g.ns.length).all (fun n =>
      selAt g.ns (n + 1) = true →
        ((n : Int) + 1 = source → inDeg g ((n : Int) + 1) = 0 ∧
          ((n : Int) + 1 = sink → outDeg g ((n : Int) + 1) = 0))) ∧
    (List.range g.ns.length).all (fun n =>
      selAt g.ns (n + 1) = true ∧ (n : Int) + 1 ≠ source ∧ (n : Int) + 1 ≠ sink →
        inDeg g ((n : Int) + 1) = 1 ∧ outDeg g ((n : Int) + 1) = 1)

def pathB (directed : Bool) (g : GraphInput) (source sink : Int) : Bool :=
  treeB directed g source &&
    (List.range g.ns.length).all (fun n =>
      !(selAt g.ns (n + 1)) ||
        (!(((n : Int) + 1) == source) ||
          (inDeg g ((n : Int) + 1) == 0 &&
            (!(((n : Int) + 1) == sink) ||
              outDeg g ((n : Int) + 1) == 0)))) &&
    (List.range g.ns.length).all (fun n =>
      !(selAt g.ns (n + 1)) ||
        !(!(((n : Int) + 1) == source)) ||
        !(!(((n : Int) + 1) == sink)) ||
        (inDeg g ((n : Int) + 1) == 1 && outDeg g ((n : Int) + 1) == 1))

theorem pathB_iff (directed : Bool) (g : GraphInput) (source sink : Int) :
    pathB directed g source sink = true ↔ pathProp directed g source sink := by
  simp only [pathB, pathProp, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, treeB_iff,
    decide_eq_true_iff]
  constructor
  · rintro ⟨⟨htree, hall1⟩, hall2⟩
    refine ⟨htree, ?_, ?_⟩
    · intro x hx hsel hsrc
      have h1 := hall1 x hx
      rcases h1 with hfalse | hrest
      · rw [hfalse] at hsel; exact absurd hsel (by simp)
      · rcases hrest with hne1 | ⟨hin, hrest⟩
        · exact absurd hsrc (by simpa using hne1)
        · refine ⟨hin, ?_⟩
          intro hsnk
          rcases hrest with hne2 | hout
          · exact absurd hsnk (by simpa using hne2)
          · exact hout
    · intro x hx ⟨hsel, hne1, hne2⟩
      have h2 := hall2 x hx
      rcases h2 with hleft | hdeg
      · rcases hleft with hleft2 | hnsnk
        · rcases hleft2 with hnsel | hnsrc
          · rw [hnsel] at hsel; exact absurd hsel (by simp)
          · exact (hne1 (by simpa using hnsrc)).elim
        · exact (hne2 (by simpa using hnsnk)).elim
      · exact hdeg
  · rintro ⟨htree, hall1, hall2⟩
    refine ⟨⟨htree, ?_⟩, ?_⟩
    · intro x hx
      by_cases hsel : selAt g.ns (x + 1) = true
      · by_cases hsrc : (x : Int) + 1 = source
        · obtain ⟨hin, hout⟩ := hall1 x hx hsel hsrc
          refine Or.inr (Or.inr ⟨hin, ?_⟩)
          by_cases hsnk : (x : Int) + 1 = sink
          · exact Or.inr (hout hsnk)
          · exact Or.inl (by simp [hsnk])
        · exact Or.inr (Or.inl (by simp [hsrc]))
      · exact Or.inl (by simp [hsel])
    · intro x hx
      by_cases hsel : selAt g.ns (x + 1) = true
      · by_cases hsrc : (x : Int) + 1 = source
        · exact Or.inl (Or.inl (by simp [hsrc]))
        · by_cases hsnk : (x : Int) + 1 = sink
          · exact Or.inl (Or.inr (by simp [hsnk]))
          · obtain ⟨hin, hout⟩ := hall2 x hx ⟨hsel, hsrc, hsnk⟩
            exact Or.inr ⟨hin, hout⟩
      · exact Or.inl (by simp [hsel])

/-- Weighted path: path + `bound = Σ es[e]·w[e]`. -/
def boundedPathProp (directed : Bool) (g : GraphInput) (w : List Int)
    (source sink bound : Int) : Prop :=
  pathProp directed g source sink ∧ bound = weightOf w g

def boundedPathB (directed : Bool) (g : GraphInput) (w : List Int)
    (source sink bound : Int) : Bool :=
  pathB directed g source sink && decide (bound = weightOf w g)

theorem boundedPathB_iff (directed : Bool) (g : GraphInput) (w : List Int)
    (source sink bound : Int) :
    boundedPathB directed g w source sink bound = true ↔
      boundedPathProp directed g w source sink bound := by
  simp only [boundedPathB, boundedPathProp, Bool.and_eq_true, pathB_iff,
    decide_eq_true_iff]

/-- Steiner tree: tree with existential root + weight bound. -/
def steinerProp (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) : Prop :=
  ∃ root, treeProp directed g root ∧ bound = weightOf w g

def steinerB (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) : Bool :=
  (List.range g.ns.length).any (fun n =>
    treeB directed g ((n : Int) + 1)) && decide (bound = weightOf w g)

theorem steinerB_iff (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) :
    steinerB directed g w bound = true ↔ steinerProp directed g w bound := by
  simp only [steinerB, steinerProp, Bool.and_eq_true, treeB_iff,
    List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨n, hn, htree⟩, hb⟩
    exact ⟨(n : Int) + 1, htree, hb⟩
  · rintro ⟨root, htree, hb⟩
    obtain ⟨h1, h2, h3, h4⟩ := htree
    have hb1 : 1 ≤ root := by
      have := of_decide_eq_true h1
      exact this.1
    have hb2 : root ≤ (g.ns.length : Int) := by
      have := of_decide_eq_true h1
      exact this.2
    have hsub : ((root - 1).toNat : Int) < g.ns.length := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      omega
    have hn : (root - 1).toNat < g.ns.length := by
      have : ((root - 1).toNat : Int) < (g.ns.length : Int) := hsub
      omega
    have hkey : ((root - 1).toNat : Int) + 1 = root := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      omega
    have hkey' : ((root - 1).toNat : Int) + 1 = root := hkey
    refine ⟨⟨(root - 1).toNat, List.mem_range.mpr hn, ?_, ?_, ?_, ?_⟩, hb⟩
    · have := h1
      simp only [inRange, decide_eq_true_iff] at *
      omega
    · rw [hkey']; exact h2
    · rw [hkey']; exact h3
    · exact h4

/-- Weighted spanning tree: tree over *all* nodes + weight bound. -/
def wstProp (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) : Prop :=
  (List.range g.ns.length).all (fun n => selAt g.ns (n + 1) = true) ∧
    ∃ root, treeProp directed g root ∧ bound = weightOf w g

def wstB (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) : Bool :=
  (List.range g.ns.length).all (fun n => selAt g.ns (n + 1)) &&
    (List.range g.ns.length).any (fun n =>
      treeB directed g ((n : Int) + 1)) &&
    decide (bound = weightOf w g)

theorem wstB_iff (directed : Bool) (g : GraphInput) (w : List Int)
    (bound : Int) :
    wstB directed g w bound = true ↔ wstProp directed g w bound := by
  simp only [wstB, wstProp, Bool.and_eq_true, List.all_eq_true,
    List.any_eq_true, treeB_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨hall, ⟨n, hn, htree⟩⟩, hb⟩
    exact ⟨hall, (n : Int) + 1, htree, hb⟩
  · rintro ⟨hall, root, htree, hb⟩
    obtain ⟨h1, h2, h3, h4⟩ := htree
    have hb1 : 1 ≤ root := by
      have := of_decide_eq_true h1
      exact this.1
    have hb2 : root ≤ (g.ns.length : Int) := by
      have := of_decide_eq_true h1
      exact this.2
    have hn : (root - 1).toNat < g.ns.length := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      have hb1' : 1 ≤ root := hb1
      have hb2' : root ≤ (g.ns.length : Int) := hb2
      omega
    have hkey : ((root - 1).toNat : Int) + 1 = root := by
      have hle : ((root - 1).toNat : Int) ≤ root - 1 := by
        have := Int.toNat_le (m := root - 1) (n := (root - 1).toNat + 1)
        omega
      have hb1' : 1 ≤ root := hb1
      omega
    refine ⟨⟨hall, ⟨(root - 1).toNat, List.mem_range.mpr hn, ?_, ?_, ?_, ?_⟩⟩, hb⟩
    · have := h1
      simp only [inRange, decide_eq_true_iff] at *
      omega
    · rw [hkey]; exact h2
    · rw [hkey]; exact h3
    · exact h4

/-! ## Argument decoders -/

/-- Decode the circuit argument. -/
private def oneIntArray' (args : List Value) : Option (List Int) :=
  match args with
  | [Value.array xs] => valueInts xs
  | _ => none

/-- Decode (from, to, ns, es). -/
private def graphArgs (args : List Value) : Option GraphInput :=
  match args with
  | [Value.array f, Value.array t, Value.array nsArr, Value.array esArr] =>
      match valueInts f, valueInts t, valueBools nsArr, valueBools esArr with
      | some fa, some ta, some nsl, some esl =>
          some ⟨fa, ta, nsl, esl⟩
      | _, _, _, _ => none
  | _ => none

/-- Decode (from, to, ns, es, root). -/
private def graphRootArgs (args : List Value) :
    Option (GraphInput × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array nsArr, Value.array esArr,
     Value.int root] =>
      match valueInts f, valueInts t, valueBools nsArr, valueBools esArr with
      | some fa, some ta, some nsl, some esl =>
          some (⟨fa, ta, nsl, esl⟩, root)
      | _, _, _, _ => none
  | _ => none

/-- Decode (from, to, ns, es, source, sink). -/
private def graphPathArgs (args : List Value) :
    Option (GraphInput × Int × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array nsArr, Value.array esArr,
     Value.int source, Value.int sink] =>
      match valueInts f, valueInts t, valueBools nsArr, valueBools esArr with
      | some fa, some ta, some nsl, some esl =>
          some (⟨fa, ta, nsl, esl⟩, source, sink)
      | _, _, _, _ => none
  | _ => none

/-- Decode (from, to, w, ns, es, source, sink, bound) — the full
    bounded-path shape (6 arrays/ints in FlatZinc order per the
    int-form signature with both source and sink). -/
private def graphBoundedPathArgs (args : List Value) :
    Option (GraphInput × List Int × Int × Int × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array w, Value.array nsArr,
     Value.array esArr, Value.int source, Value.int sink,
     Value.int bound] =>
      match valueInts f, valueInts t, valueInts w, valueBools nsArr,
        valueBools esArr with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (⟨fa, ta, nsl, esl⟩, wl, source, sink, bound)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (from, to, w, ns, es, root, bound) — steiner. -/
private def graphSteinerArgs (args : List Value) :
    Option (GraphInput × List Int × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array w, Value.array nsArr,
     Value.array esArr, Value.int _root, Value.int bound] =>
      match valueInts f, valueInts t, valueInts w, valueBools nsArr,
        valueBools esArr with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (⟨fa, ta, nsl, esl⟩, wl, bound)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (from, to, w, es, bound) — wst (no `ns`, no root). -/
private def graphWstArgs (args : List Value) :
    Option (GraphInput × List Int × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array w, Value.array esArr,
     Value.int bound] =>
      match valueInts f, valueInts t, valueInts w, valueBools esArr with
      | some fa, some ta, some wl, some esl =>
          -- node count from the largest id appearing in either endpoint
          -- array, all nodes selected
          let n := max (fa.foldl (fun acc v => max acc v) 0)
            (ta.foldl (fun acc v => max acc v) 0)
          some (⟨fa, ta, List.replicate (max (max fa.length ta.length)
            n.toNat) true, esl⟩, wl, bound)
      | _, _, _, _ => none
  | _ => none

/-- Decode (from, to, w, es, root, bound) — dwst. -/
private def graphDwstArgs (args : List Value) :
    Option (GraphInput × List Int × Int × Int) :=
  match args with
  | [Value.array f, Value.array t, Value.array w, Value.array esArr,
     Value.int root, Value.int bound] =>
      match valueInts f, valueInts t, valueInts w, valueBools esArr with
      | some fa, some ta, some wl, some esl =>
          let n := max (fa.foldl (fun acc v => max acc v) 0)
            (ta.foldl (fun acc v => max acc v) 0)
          some (⟨fa, ta, List.replicate (max (max fa.length ta.length)
            n.toNat) true, esl⟩, wl, root, bound)
      | _, _, _, _ => none
  | _ => none

/-! ## The interpretations -/

/-- Mathematical interpretations of the circuit and graph
    predicates; wrong shapes yield `False`. -/
def graphInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_circuit" => fun args =>
    match oneIntArray' args with
    | some xs => circuitProp xs
    | none => False
  | "fzn_subcircuit" => fun args =>
    match oneIntArray' args with
    | some xs => subcircuitProp xs
    | none => False
  | "fzn_subgraph" => fun args =>
    match graphArgs args with
    | some g => subgraphProp g
    | none => False
  | "fzn_dag" => fun args =>
    match graphArgs args with
    | some g => dagProp g
    | none => False
  | "fzn_connected" => fun args =>
    match graphArgs args with
    | some g => connectedProp false g
    | none => False
  | "fzn_dconnected" => fun args =>
    match graphArgs args with
    | some g => connectedProp true g
    | none => False
  | "fzn_reachable" => fun args =>
    match graphRootArgs args with
    | some (g, root) => reachableProp false g root
    | none => False
  | "fzn_dreachable" => fun args =>
    match graphRootArgs args with
    | some (g, root) => reachableProp true g root
    | none => False
  | "fzn_tree" => fun args =>
    match graphRootArgs args with
    | some (g, root) => treeProp false g root
    | none => False
  | "fzn_dtree" => fun args =>
    match graphRootArgs args with
    | some (g, root) => treeProp true g root
    | none => False
  | "fzn_path" => fun args =>
    match graphPathArgs args with
    | some (g, source, sink) => pathProp false g source sink
    | none => False
  | "fzn_dpath" => fun args =>
    match graphPathArgs args with
    | some (g, source, sink) => pathProp true g source sink
    | none => False
  | "fzn_bounded_path" => fun args =>
    match graphBoundedPathArgs args with
    | some (g, w, source, sink, bound) =>
        boundedPathProp false g w source sink bound
    | none => False
  | "fzn_bounded_dpath" => fun args =>
    match graphBoundedPathArgs args with
    | some (g, w, source, sink, bound) =>
        boundedPathProp true g w source sink bound
    | none => False
  | "fzn_steiner" => fun args =>
    match graphSteinerArgs args with
    | some (g, w, bound) => steinerProp false g w bound
    | none => False
  | "fzn_dsteiner" => fun args =>
    match graphSteinerArgs args with
    | some (g, w, bound) => steinerProp true g w bound
    | none => False
  | "fzn_wst" => fun args =>
    match graphWstArgs args with
    | some (g, w, bound) => wstProp false g w bound
    | none => False
  | "fzn_dwst" => fun args =>
    match graphDwstArgs args with
    | some (g, w, root, bound) =>
        treeProp true g root ∧ bound = weightOf w g
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `graphInterp`.** -/
def graphInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_circuit" => fun args =>
    match oneIntArray' args with
    | some xs => circuitB xs
    | none => false
  | "fzn_subcircuit" => fun args =>
    match oneIntArray' args with
    | some xs => subcircuitB xs
    | none => false
  | "fzn_subgraph" => fun args =>
    match graphArgs args with
    | some g => subgraphB g
    | none => false
  | "fzn_dag" => fun args =>
    match graphArgs args with
    | some g => dagB g
    | none => false
  | "fzn_connected" => fun args =>
    match graphArgs args with
    | some g => connectedB false g
    | none => false
  | "fzn_dconnected" => fun args =>
    match graphArgs args with
    | some g => connectedB true g
    | none => false
  | "fzn_reachable" => fun args =>
    match graphRootArgs args with
    | some (g, root) => reachableB false g root
    | none => false
  | "fzn_dreachable" => fun args =>
    match graphRootArgs args with
    | some (g, root) => reachableB true g root
    | none => false
  | "fzn_tree" => fun args =>
    match graphRootArgs args with
    | some (g, root) => treeB false g root
    | none => false
  | "fzn_dtree" => fun args =>
    match graphRootArgs args with
    | some (g, root) => treeB true g root
    | none => false
  | "fzn_path" => fun args =>
    match graphPathArgs args with
    | some (g, source, sink) => pathB false g source sink
    | none => false
  | "fzn_dpath" => fun args =>
    match graphPathArgs args with
    | some (g, source, sink) => pathB true g source sink
    | none => false
  | "fzn_bounded_path" => fun args =>
    match graphBoundedPathArgs args with
    | some (g, w, source, sink, bound) =>
        boundedPathB false g w source sink bound
    | none => false
  | "fzn_bounded_dpath" => fun args =>
    match graphBoundedPathArgs args with
    | some (g, w, source, sink, bound) =>
        boundedPathB true g w source sink bound
    | none => false
  | "fzn_steiner" => fun args =>
    match graphSteinerArgs args with
    | some (g, w, bound) => steinerB false g w bound
    | none => false
  | "fzn_dsteiner" => fun args =>
    match graphSteinerArgs args with
    | some (g, w, bound) => steinerB true g w bound
    | none => false
  | "fzn_wst" => fun args =>
    match graphWstArgs args with
    | some (g, w, bound) => wstB false g w bound
    | none => false
  | "fzn_dwst" => fun args =>
    match graphDwstArgs args with
    | some (g, w, root, bound) =>
        treeB true g root && decide (bound = weightOf w g)
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_circuit_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_circuit") args = true ↔
      graphInterp (Ident.mk "fzn_circuit") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_circuit") args
      = match oneIntArray' args with
      | some xs => circuitB xs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_circuit") args
      = match oneIntArray' args with
      | some xs => circuitProp xs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneIntArray' args with
  | none => simp
  | some xs =>
    simp only
    exact circuitB_iff xs

theorem fzn_subcircuit_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_subcircuit") args = true ↔
      graphInterp (Ident.mk "fzn_subcircuit") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_subcircuit") args
      = match oneIntArray' args with
      | some xs => subcircuitB xs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_subcircuit") args
      = match oneIntArray' args with
      | some xs => subcircuitProp xs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneIntArray' args with
  | none => simp
  | some xs =>
    simp only
    exact subcircuitB_iff xs

theorem fzn_subgraph_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_subgraph") args = true ↔
      graphInterp (Ident.mk "fzn_subgraph") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_subgraph") args
      = match graphArgs args with
      | some g => subgraphB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_subgraph") args
      = match graphArgs args with
      | some g => subgraphProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphArgs args with
  | none => simp
  | some g =>
    simp only
    exact subgraphB_iff g

theorem fzn_dag_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dag") args = true ↔
      graphInterp (Ident.mk "fzn_dag") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dag") args
      = match graphArgs args with
      | some g => dagB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dag") args
      = match graphArgs args with
      | some g => dagProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphArgs args with
  | none => simp
  | some g =>
    simp only
    exact dagB_iff g

theorem fzn_connected_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_connected") args = true ↔
      graphInterp (Ident.mk "fzn_connected") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_connected") args
      = match graphArgs args with
      | some g => connectedB false g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_connected") args
      = match graphArgs args with
      | some g => connectedProp false g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphArgs args with
  | none => simp
  | some g =>
    simp only
    exact connectedB_iff false g

theorem fzn_dconnected_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dconnected") args = true ↔
      graphInterp (Ident.mk "fzn_dconnected") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dconnected") args
      = match graphArgs args with
      | some g => connectedB true g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dconnected") args
      = match graphArgs args with
      | some g => connectedProp true g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphArgs args with
  | none => simp
  | some g =>
    simp only
    exact connectedB_iff true g

theorem fzn_reachable_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_reachable") args = true ↔
      graphInterp (Ident.mk "fzn_reachable") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_reachable") args
      = match graphRootArgs args with
      | some (g, root) => reachableB false g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_reachable") args
      = match graphRootArgs args with
      | some (g, root) => reachableProp false g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphRootArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, root⟩ := p
    simp only
    exact reachableB_iff false g root

theorem fzn_dreachable_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dreachable") args = true ↔
      graphInterp (Ident.mk "fzn_dreachable") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dreachable") args
      = match graphRootArgs args with
      | some (g, root) => reachableB true g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dreachable") args
      = match graphRootArgs args with
      | some (g, root) => reachableProp true g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphRootArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, root⟩ := p
    simp only
    exact reachableB_iff true g root

theorem fzn_tree_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_tree") args = true ↔
      graphInterp (Ident.mk "fzn_tree") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_tree") args
      = match graphRootArgs args with
      | some (g, root) => treeB false g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_tree") args
      = match graphRootArgs args with
      | some (g, root) => treeProp false g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphRootArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, root⟩ := p
    simp only
    exact treeB_iff false g root

theorem fzn_dtree_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dtree") args = true ↔
      graphInterp (Ident.mk "fzn_dtree") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dtree") args
      = match graphRootArgs args with
      | some (g, root) => treeB true g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dtree") args
      = match graphRootArgs args with
      | some (g, root) => treeProp true g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphRootArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, root⟩ := p
    simp only
    exact treeB_iff true g root

theorem fzn_path_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_path") args = true ↔
      graphInterp (Ident.mk "fzn_path") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_path") args
      = match graphPathArgs args with
      | some (g, source, sink) => pathB false g source sink
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_path") args
      = match graphPathArgs args with
      | some (g, source, sink) => pathProp false g source sink
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphPathArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, source, sink⟩ := p
    simp only
    exact pathB_iff false g source sink

theorem fzn_dpath_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dpath") args = true ↔
      graphInterp (Ident.mk "fzn_dpath") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dpath") args
      = match graphPathArgs args with
      | some (g, source, sink) => pathB true g source sink
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dpath") args
      = match graphPathArgs args with
      | some (g, source, sink) => pathProp true g source sink
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphPathArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, source, sink⟩ := p
    simp only
    exact pathB_iff true g source sink

theorem fzn_bounded_path_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_bounded_path") args = true ↔
      graphInterp (Ident.mk "fzn_bounded_path") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_bounded_path") args
      = match graphBoundedPathArgs args with
      | some (g, w, source, sink, bound) =>
      boundedPathB false g w source sink bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_bounded_path") args
      = match graphBoundedPathArgs args with
      | some (g, w, source, sink, bound) =>
      boundedPathProp false g w source sink bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphBoundedPathArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, source, sink, bound⟩ := p
    simp only
    exact boundedPathB_iff false g w source sink bound

theorem fzn_bounded_dpath_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_bounded_dpath") args = true ↔
      graphInterp (Ident.mk "fzn_bounded_dpath") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_bounded_dpath") args
      = match graphBoundedPathArgs args with
      | some (g, w, source, sink, bound) =>
      boundedPathB true g w source sink bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_bounded_dpath") args
      = match graphBoundedPathArgs args with
      | some (g, w, source, sink, bound) =>
      boundedPathProp true g w source sink bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphBoundedPathArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, source, sink, bound⟩ := p
    simp only
    exact boundedPathB_iff true g w source sink bound

theorem fzn_steiner_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_steiner") args = true ↔
      graphInterp (Ident.mk "fzn_steiner") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_steiner") args
      = match graphSteinerArgs args with
      | some (g, w, bound) => steinerB false g w bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_steiner") args
      = match graphSteinerArgs args with
      | some (g, w, bound) => steinerProp false g w bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphSteinerArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, bound⟩ := p
    simp only
    exact steinerB_iff false g w bound

theorem fzn_dsteiner_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dsteiner") args = true ↔
      graphInterp (Ident.mk "fzn_dsteiner") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dsteiner") args
      = match graphSteinerArgs args with
      | some (g, w, bound) => steinerB true g w bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dsteiner") args
      = match graphSteinerArgs args with
      | some (g, w, bound) => steinerProp true g w bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphSteinerArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, bound⟩ := p
    simp only
    exact steinerB_iff true g w bound

theorem fzn_wst_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_wst") args = true ↔
      graphInterp (Ident.mk "fzn_wst") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_wst") args
      = match graphWstArgs args with
      | some (g, w, bound) => wstB false g w bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_wst") args
      = match graphWstArgs args with
      | some (g, w, bound) => wstProp false g w bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphWstArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, bound⟩ := p
    simp only
    exact wstB_iff false g w bound

theorem fzn_dwst_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dwst") args = true ↔
      graphInterp (Ident.mk "fzn_dwst") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dwst") args
      = match graphDwstArgs args with
      | some (g, w, root, bound) =>
      treeB true g root && decide (bound = weightOf w g)
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dwst") args
      = match graphDwstArgs args with
      | some (g, w, root, bound) =>
      treeProp true g root ∧ bound = weightOf w g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : graphDwstArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, root, bound⟩ := p
    simp only
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact and_congr (treeB_iff true g root) Iff.rfl

end LeanFzn.Semantics.Globals.Graph

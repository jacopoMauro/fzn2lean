import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Circuit and graph global constraints

Mathematical interpretations (`graphInterp`) and executable Boolean
twins (`graphInterpB`) for the circuit and graph predicates of the
pinned MiniZinc 2.10.1 tree.

The graph family is a literal transcription of the pinned `fzn_*.mzn`
decompositions (`tmp/semantic-conformance/upstream/share/minizinc/std/`,
commit `c3448c48e7f05f13805616cfd1b9e94972eef58c`).  Every array read
is routed through `at1`, whose result is `none` outside `1..length`,
and through `req`, which is `False` on `none`; auxiliary arrays are
existentially quantified over explicit finite enumerations.  The
names have two overloads (`_int` with leading `N`, `E`, and `_enum`
without them); decoders dispatch on arity and never infer a node or
edge count from the data.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Graph

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

set_option synthInstance.maxSize 4096

/-! ## Index helpers -/

/-- 1-based lookup in a list; `none` unless `1 ≤ i ≤ length`. -/
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

/-- All length-`k` lists with entries in `lo..hi` (empty if `lo > hi`). -/
def allVals : Nat → Int → Int → List (List Int)
  | 0, _, _ => [[]]
  | k + 1, lo, hi =>
      ((allVals k lo hi).map (fun xs =>
        (List.range (max (hi - lo + 1) 0).toNat).map
          (fun j => xs ++ [lo + Int.ofNat j]))).flatten

/-- All length-`k` Boolean lists. -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => ((allBits k).map (fun xs => [xs ++ [false], xs ++ [true]])).flatten

/-- The 1-based id of a slot. -/
def idN {k : Nat} (i : Fin k) : Int := (i.val : Int) + 1

/-- Sum of an option list, `none` if any entry is undefined. -/
def sumOpt : List (Option Int) → Option Int
  | [] => some 0
  | none :: _ => none
  | some x :: rest => (sumOpt rest).map (x + ·)

/-- Maximum of an option list with fallback `0` (`max([0] ++ xs)`),
    `none` if any entry is undefined. -/
def maxOpt : List (Option Int) → Option Int
  | [] => some 0
  | none :: _ => none
  | some x :: rest => (maxOpt rest).map (max x ·)

/-- `if b then 1 else 0`, `none` outside the list. -/
def selTerm (bs : List Bool) (i : Int) : Option Int :=
  (at1 bs i).map (fun b => if b then 1 else 0)

/-- `es[i] * w[i]`, `none` outside either list. -/
def weightTerm (bs : List Bool) (ws : List Int) (i : Int) : Option Int :=
  match at1 bs i, at1 ws i with
  | some b, some v => some (if b then v else 0)
  | _, _ => none

/-- `sum (e in 1..m where to[e] = n) (sel[e])`. -/
def sumWhereTo (toArr : List Int) (sel : List Bool) (m : Nat) (n : Int) :
    Option Int :=
  sumOpt (List.ofFn fun e : Fin m =>
    match at1 toArr (idN e) with
    | none => none
    | some t => if t = n then selTerm sel (idN e) else some 0)

/-- `sum (e in 1..m where from[e] = n) (sel[e])`. -/
def sumWhereFrom (fromArr : List Int) (sel : List Bool) (m : Nat) (n : Int) :
    Option Int :=
  sumOpt (List.ofFn fun e : Fin m =>
    match at1 fromArr (idN e) with
    | none => none
    | some t => if t = n then selTerm sel (idN e) else some 0)

/-! ## Graph inputs and shape gates -/

/-- An `_int`-form graph: leading `N` and `E`, then the arrays. -/
structure IntGraph where
  nodeCount : Int
  edgeCount : Int
  fromArr : List Int
  toArr : List Int
  ns : List Bool
  es : List Bool

/-- An `_enum`-form graph: no `N`/`E`, nodes are `index_set(ns)`. -/
structure EnumGraph where
  fromArr : List Int
  toArr : List Int
  ns : List Bool
  es : List Bool

def IntGraph.K (g : IntGraph) : Nat := (max g.nodeCount 0).toNat
def IntGraph.M (g : IntGraph) : Nat := (max g.edgeCount 0).toNat
def IntGraph.M2 (g : IntGraph) : Nat := (max (2 * g.edgeCount) 0).toNat
def EnumGraph.K (g : EnumGraph) : Nat := g.ns.length
def EnumGraph.M (g : EnumGraph) : Nat := g.es.length

/-- `_int` shape: `index_set(from) = index_set(to) = index_set(es) = 1..E`
    and `index_set(ns) = 1..N`.  These are the `subgraph`/`dreachable`/
    `dtree`/`dpath` wrapper assertions. -/
abbrev intLen (g : IntGraph) : Prop :=
  g.fromArr.length = g.M ∧ g.toArr.length = g.M ∧
    g.ns.length = g.K ∧ g.es.length = g.M

/-- `_enum` shape: equal index sets of `from`, `to`, `es`, and all
    endpoint values in `index_set(ns)` (the enum `subgraph` wrapper
    assertions). -/
abbrev enumLen (g : EnumGraph) : Prop :=
  g.fromArr.length = g.toArr.length ∧
    g.fromArr.length = g.es.length ∧
    (∀ x ∈ g.fromArr, 1 ≤ x ∧ x ≤ (g.ns.length : Int)) ∧
    (∀ x ∈ g.toArr, 1 ≤ x ∧ x ≤ (g.ns.length : Int))

def enumLenB (g : EnumGraph) : Bool :=
  decide (g.fromArr.length = g.toArr.length ∧
      g.fromArr.length = g.es.length) &&
    g.fromArr.all (fun x => decide (1 ≤ x ∧ x ≤ (g.ns.length : Int))) &&
    g.toArr.all (fun x => decide (1 ≤ x ∧ x ≤ (g.ns.length : Int)))

theorem enumLenB_iff (g : EnumGraph) : enumLenB g = true ↔ enumLen g := by
  simp only [enumLenB, enumLen, Bool.and_eq_true, decide_eq_true_iff,
    List.all_eq_true, and_assoc]

/-- Shape gate of `fzn_tree_int`: the duplicated arrays `from ++ to`
    and `to ++ from` both have `1..2E`, and `ns` has `1..N`. -/
abbrev treeIntGate (g : IntGraph) : Prop :=
  g.fromArr.length + g.toArr.length = g.M2 ∧ g.ns.length = g.K

/-- Shape gate of `fzn_reachable_int`: additionally `es ++ es` must
    have `1..2E`. -/
abbrev reachableIntGate (g : IntGraph) : Prop :=
  g.fromArr.length + g.toArr.length = g.M2 ∧
    g.es.length = g.M ∧ g.ns.length = g.K

/-- Shape gate of `fzn_path_int`: same as `fzn_tree_int`. -/
abbrev pathIntGate (g : IntGraph) : Prop := treeIntGate g

/-- Shape gate of `fzn_tree_enum`/`fzn_path_enum`/`fzn_reachable_enum`. -/
abbrev treeEnumGate (g : EnumGraph) : Prop :=
  g.fromArr.length + g.toArr.length = 2 * g.M ∧
    (∀ x ∈ g.fromArr, 1 ≤ x ∧ x ≤ (g.ns.length : Int)) ∧
    (∀ x ∈ g.toArr, 1 ≤ x ∧ x ≤ (g.ns.length : Int))

/-- Shape gate of `fzn_wst`/`fzn_dwst` (no `ns` argument). -/
abbrev stGate (g : IntGraph) : Prop :=
  g.fromArr.length = g.M ∧ g.toArr.length = g.M ∧ g.es.length = g.M

/-! ## Bounded quantification over auxiliary arrays and roots -/

abbrev existsAux1 (k : Nat) (lo hi : Int) (p : List Int → Prop) : Prop :=
  ∃ xs : List Int, xs ∈ allVals k lo hi ∧ p xs

def existsAux1B (k : Nat) (lo hi : Int) (p : List Int → Bool) : Bool :=
  (allVals k lo hi).any p

theorem existsAux1B_iff {k : Nat} {lo hi : Int}
    {p : List Int → Bool} {P : List Int → Prop}
    (h : ∀ xs, p xs = true ↔ P xs) :
    existsAux1B k lo hi p = true ↔ existsAux1 k lo hi P := by
  simp only [existsAux1B, existsAux1, List.any_eq_true]
  exact ⟨fun ⟨xs, hmem, hp⟩ => ⟨xs, hmem, (h xs).mp hp⟩,
    fun ⟨xs, hmem, hp⟩ => ⟨xs, hmem, (h xs).mpr hp⟩⟩

abbrev existsAux2 (k : Nat) (dlo dhi plo phi : Int)
    (p : List Int → List Int → Prop) : Prop :=
  ∃ dist : List Int, dist ∈ allVals k dlo dhi ∧
    ∃ parent : List Int, parent ∈ allVals k plo phi ∧ p dist parent

def existsAux2B (k : Nat) (dlo dhi plo phi : Int)
    (p : List Int → List Int → Bool) : Bool :=
  (allVals k dlo dhi).any
    (fun dist => (allVals k plo phi).any (fun parent => p dist parent))

theorem existsAux2B_iff {k : Nat} {dlo dhi plo phi : Int}
    {p : List Int → List Int → Bool} {P : List Int → List Int → Prop}
    (h : ∀ d pa, p d pa = true ↔ P d pa) :
    existsAux2B k dlo dhi plo phi p = true ↔
      existsAux2 k dlo dhi plo phi P := by
  simp only [existsAux2B, existsAux2, List.any_eq_true]
  constructor
  · rintro ⟨d, hd, pa, hpa, hp⟩
    exact ⟨d, hd, pa, hpa, (h d pa).mp hp⟩
  · rintro ⟨d, hd, pa, hpa, hp⟩
    exact ⟨d, hd, pa, hpa, (h d pa).mpr hp⟩

abbrev existsBits (k : Nat) (p : List Bool → Prop) : Prop :=
  ∃ des : List Bool, des ∈ allBits k ∧ p des

def existsBitsB (k : Nat) (p : List Bool → Bool) : Bool :=
  (allBits k).any p

theorem existsBitsB_iff {k : Nat} {p : List Bool → Bool}
    {P : List Bool → Prop} (h : ∀ d, p d = true ↔ P d) :
    existsBitsB k p = true ↔ existsBits k P := by
  simp only [existsBitsB, existsBits, List.any_eq_true]
  exact ⟨fun ⟨d, hmem, hp⟩ => ⟨d, hmem, (h d).mp hp⟩,
    fun ⟨d, hmem, hp⟩ => ⟨d, hmem, (h d).mpr hp⟩⟩

abbrev existsRoot (k : Nat) (p : Int → Prop) : Prop :=
  ∃ i : Fin k, p (idN i)

def existsRootB (k : Nat) (p : Int → Bool) : Bool :=
  (List.range k).any (fun j => p (Int.ofNat j + 1))

theorem existsRootB_iff {k : Nat} {p : Int → Bool} {P : Int → Prop}
    (h : ∀ x, p x = true ↔ P x) :
    existsRootB k p = true ↔ existsRoot k P := by
  simp only [existsRootB, existsRoot, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, hj, hp⟩
    exact ⟨⟨j, hj⟩, (h (Int.ofNat j + 1)).mp hp⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.val, i.isLt, (h (idN i)).mpr ?_⟩
    simpa [idN] using hi

/-! ## Core relations (literal `fzn_*.mzn` bodies) -/

/-- `fzn_subgraph_int` body. -/
abbrev subgraphIntCore (g : IntGraph) : Prop :=
  ∀ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true →
    req (at1 g.fromArr (idN e)) (fun f =>
      req (at1 g.ns f) (fun x => x = true)) ∧
    req (at1 g.toArr (idN e)) (fun t =>
      req (at1 g.ns t) (fun x => x = true)))

/-- `fzn_subgraph_enum` body (`index_set(from)` loop). -/
abbrev subgraphEnumCore (g : EnumGraph) : Prop :=
  ∀ e : Fin g.fromArr.length,
    req (at1 g.es (idN e)) (fun b => b = true →
      req (at1 g.fromArr (idN e)) (fun f =>
        req (at1 g.ns f) (fun x => x = true)) ∧
      req (at1 g.toArr (idN e)) (fun t =>
        req (at1 g.ns t) (fun x => x = true)))

/-- `fzn_dreachable_int` body after the `subgraph` call. -/
abbrev dreachableIntCore (g : IntGraph) (root : Int)
    (dist parent : List Int) : Prop :=
  req (at1 g.ns root) (fun b => b = true) ∧
  req (at1 dist root) (fun d => d = 0) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 parent (idN n)) (fun p => p = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → (idN n = root ∨
      req (at1 parent (idN n)) (fun p => 0 < p)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    req (at1 g.ns (idN n)) (fun x => x = true) ∧
    req (at1 g.ns p) (fun x => x = true))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    req (at1 dist (idN n)) (fun dn =>
      req (at1 dist p) (fun dp => dn = dp + 1)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    ∃ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true ∧
      req (at1 g.fromArr (idN e)) (fun f => f = p) ∧
      req (at1 g.toArr (idN e)) (fun t => t = idN n)))) ∧
  subgraphIntCore g

/-- `fzn_dtree_int` body after the `subgraph` call. -/
abbrev dtreeIntCore (g : IntGraph) (root : Int)
    (dist parent : List Int) : Prop :=
  req (at1 g.ns root) (fun b => b = true) ∧
  req (at1 dist root) (fun d => d = 0) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 parent (idN n)) (fun p => p ≤ 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → (idN n = root ∨
      req (at1 parent (idN n)) (fun p => 0 < p)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    req (at1 g.ns (idN n)) (fun x => x = true) ∧
    req (at1 g.ns p) (fun x => x = true))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    req (at1 dist (idN n)) (fun dn =>
      req (at1 dist p) (fun dp => dn = dp + 1)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => 0 < p →
    ∃ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true ∧
      req (at1 g.fromArr (idN e)) (fun f => f = p) ∧
      req (at1 g.toArr (idN e)) (fun t => t = idN n)))) ∧
  (∀ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true →
    req (at1 g.toArr (idN e)) (fun t =>
      req (at1 parent t) (fun p =>
        req (at1 g.fromArr (idN e)) (fun f => p = f))))) ∧
  req (sumOpt (List.ofFn fun e : Fin g.M => selTerm g.es (idN e)))
    (fun s => req (sumOpt (List.ofFn fun n : Fin g.K =>
      selTerm g.ns (idN n))) (fun t => s = t - 1)) ∧
  subgraphIntCore g

/-- `fzn_dreachable_enum` body after the `subgraph` call. -/
abbrev dreachableEnumCore (g : EnumGraph) (root : Int)
    (dist parent : List Int) : Prop :=
  req (at1 g.ns root) (fun b => b = true) ∧
  req (at1 dist root) (fun d => d = 0) ∧
  req (at1 parent root) (fun p => p = root) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 parent (idN n)) (fun p => p = idN n))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → (idN n = root ∨
      req (at1 parent (idN n)) (fun p => p ≠ idN n)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    req (at1 g.ns (idN n)) (fun x => x = true) ∧
    req (at1 g.ns p) (fun x => x = true))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    req (at1 dist (idN n)) (fun dn =>
      req (at1 dist p) (fun dp => dn = dp + 1)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    ∃ e : Fin g.fromArr.length,
      req (at1 g.toArr (idN e)) (fun t => t = idN n ∧
        req (at1 g.es (idN e)) (fun b => b = true ∧
          req (at1 g.fromArr (idN e)) (fun f => f = p))))) ∧
  subgraphEnumCore g

/-- `fzn_dtree_enum` body after the `subgraph` call. -/
abbrev dtreeEnumCore (g : EnumGraph) (root : Int)
    (dist parent : List Int) : Prop :=
  req (at1 g.ns root) (fun b => b = true) ∧
  req (at1 dist root) (fun d => d = 0) ∧
  req (at1 parent root) (fun p => p = root) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 parent (idN n)) (fun p => p = idN n))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → (idN n = root ∨
      req (at1 parent (idN n)) (fun p => p ≠ idN n)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    req (at1 g.ns (idN n)) (fun x => x = true) ∧
    req (at1 g.ns p) (fun x => x = true))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    req (at1 dist (idN n)) (fun dn =>
      req (at1 dist p) (fun dp => dn = dp + 1)))) ∧
  (∀ n : Fin g.K, req (at1 parent (idN n)) (fun p => p ≠ idN n →
    ∃ e : Fin g.M,
      req (at1 g.toArr (idN e)) (fun t => t = idN n ∧
        req (at1 g.es (idN e)) (fun b => b = true ∧
          req (at1 g.fromArr (idN e)) (fun f => f = p))))) ∧
  (∀ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true →
    req (at1 g.toArr (idN e)) (fun t =>
      req (at1 parent t) (fun p =>
        req (at1 g.fromArr (idN e)) (fun f => p = f))))) ∧
  req (sumOpt (List.ofFn fun e : Fin g.M => selTerm g.es (idN e)))
    (fun s => req (sumOpt (List.ofFn fun n : Fin g.K =>
      selTerm g.ns (idN n))) (fun t => s = t - 1)) ∧
  subgraphEnumCore g

/-- `fzn_dpath_enum` body after the `subgraph` call. -/
abbrev dpathEnumCore (g : EnumGraph) (source sink : Int)
    (dist : List Int) : Prop :=
  req (at1 g.ns source) (fun b => b = true) ∧
  req (at1 g.ns sink) (fun b => b = true) ∧
  req (at1 dist source) (fun d => d = 0) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → idN n ≠ source →
      ∃ e : Fin g.M, req (at1 g.toArr (idN e)) (fun t => t = idN n ∧
        req (at1 g.es (idN e)) (fun x => x = true)))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → idN n ≠ sink →
      ∃ e : Fin g.M, req (at1 g.fromArr (idN e)) (fun t => t = idN n ∧
        req (at1 g.es (idN e)) (fun x => x = true)))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → idN n ≠ source →
      req (sumWhereTo g.toArr g.es g.M (idN n)) (fun s => s ≤ 1))) ∧
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = true → idN n ≠ sink →
      req (sumWhereFrom g.fromArr g.es g.M (idN n)) (fun s => s ≤ 1))) ∧
  (∀ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true →
    req (at1 g.toArr (idN e)) (fun t =>
      req (at1 dist t) (fun dt =>
        req (at1 g.fromArr (idN e)) (fun f =>
          req (at1 dist f) (fun df => dt = df + 1)))))) ∧
  req (sumOpt (List.ofFn fun n : Fin g.K => selTerm g.ns (idN n)))
    (fun t => req (sumOpt (List.ofFn fun e : Fin g.M =>
      selTerm g.es (idN e))) (fun s => t = s + 1)) ∧
  subgraphEnumCore g

/-- `fzn_dag` body. -/
abbrev dagEnumCore (g : EnumGraph) (dist : List Int) : Prop :=
  (∀ n : Fin g.K, req (at1 g.ns (idN n)) (fun b =>
    b = false → req (at1 dist (idN n)) (fun d => d = 0))) ∧
  (∀ e : Fin g.M, req (at1 g.es (idN e)) (fun b => b = true →
    req (at1 g.fromArr (idN e)) (fun f =>
      req (at1 dist f) (fun df =>
        req (at1 g.toArr (idN e)) (fun t =>
          req (at1 dist t) (fun dt => df + 1 ≤ dt)))))) ∧
  (∀ n : Fin g.K, req (at1 dist (idN n)) (fun dn =>
    req (maxOpt (List.ofFn fun e : Fin g.M =>
      match at1 g.toArr (idN e) with
      | none => none
      | some t => if t = idN n then
          match at1 g.es (idN e), at1 g.fromArr (idN e) with
          | some b, some f => (at1 dist f).map (fun df =>
              if b then df + 1 else 0)
          | _, _ => none
        else some 0)) (fun mx => dn = mx)))

/-! ## Duplicated-edge constructions -/

def swapInt (g : IntGraph) : IntGraph :=
  ⟨g.nodeCount, g.edgeCount, g.toArr, g.fromArr, g.ns, g.es⟩

def dupInt (g : IntGraph) (des : List Bool) : IntGraph :=
  ⟨g.nodeCount, 2 * g.edgeCount,
    g.fromArr ++ g.toArr, g.toArr ++ g.fromArr, g.ns, des⟩

def dupEnum (g : EnumGraph) (des : List Bool) : EnumGraph :=
  ⟨g.fromArr ++ g.toArr, g.toArr ++ g.fromArr, g.ns, des⟩

def allTrueGraph (g : IntGraph) : IntGraph :=
  ⟨g.nodeCount, g.edgeCount, g.fromArr, g.toArr,
    List.replicate g.K true, g.es⟩

/-- The pointwise bridge `es[e] ↔ des[e] ∨ des[e+E]` of the
    duplicated-edge wrappers. -/
abbrev bridgeSel (es des : List Bool) (m : Nat) : Prop :=
  ∀ e : Fin m, req (at1 es (idN e)) (fun b =>
    req (at1 des (idN e)) (fun d1 =>
      req (at1 des (idN e + (m : Int))) (fun d2 => b = (d1 || d2))))

/-! ## Boolean shape gates -/

def treeIntGateB (g : IntGraph) : Bool :=
  decide (g.fromArr.length + g.toArr.length = g.M2) &&
    decide (g.ns.length = g.K)

theorem treeIntGateB_iff (g : IntGraph) :
    treeIntGateB g = true ↔ treeIntGate g := by
  simp only [treeIntGateB, treeIntGate, Bool.and_eq_true, decide_eq_true_iff]

def reachableIntGateB (g : IntGraph) : Bool :=
  decide (g.fromArr.length + g.toArr.length = g.M2) &&
    decide (g.es.length = g.M) && decide (g.ns.length = g.K)

theorem reachableIntGateB_iff (g : IntGraph) :
    reachableIntGateB g = true ↔ reachableIntGate g := by
  simp only [reachableIntGateB, reachableIntGate, Bool.and_eq_true,
    decide_eq_true_iff, and_assoc]

def treeEnumGateB (g : EnumGraph) : Bool :=
  decide (g.fromArr.length + g.toArr.length = 2 * g.M) &&
    g.fromArr.all (fun x => decide (1 ≤ x ∧ x ≤ (g.ns.length : Int))) &&
    g.toArr.all (fun x => decide (1 ≤ x ∧ x ≤ (g.ns.length : Int)))

theorem treeEnumGateB_iff (g : EnumGraph) :
    treeEnumGateB g = true ↔ treeEnumGate g := by
  simp only [treeEnumGateB, treeEnumGate, Bool.and_eq_true,
    decide_eq_true_iff, List.all_eq_true, and_assoc]

def stGateB (g : IntGraph) : Bool :=
  decide (g.fromArr.length = g.M) && decide (g.toArr.length = g.M) &&
    decide (g.es.length = g.M)

theorem stGateB_iff (g : IntGraph) : stGateB g = true ↔ stGate g := by
  simp only [stGateB, stGate, Bool.and_eq_true, decide_eq_true_iff,
    and_assoc]

/-! ## `fzn_subgraph` -/

abbrev subgraphIntProp (g : IntGraph) : Prop := subgraphIntCore g

def subgraphIntB (g : IntGraph) : Bool := decide (subgraphIntCore g)

theorem subgraphIntB_iff (g : IntGraph) :
    subgraphIntB g = true ↔ subgraphIntProp g :=
  decide_eq_true_iff

abbrev subgraphEnumProp (g : EnumGraph) : Prop := subgraphEnumCore g

def subgraphEnumB (g : EnumGraph) : Bool := decide (subgraphEnumCore g)

theorem subgraphEnumB_iff (g : EnumGraph) :
    subgraphEnumB g = true ↔ subgraphEnumProp g :=
  decide_eq_true_iff

/-! ## `fzn_dreachable` -/

abbrev dreachableIntProp (g : IntGraph) (root : Int) : Prop :=
  intLen g ∧ existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dreachableIntCore g root d p)

def dreachableIntB (g : IntGraph) (root : Int) : Bool :=
  decide (intLen g) && existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => decide (dreachableIntCore g root d p))

theorem dreachableIntB_iff (g : IntGraph) (root : Int) :
    dreachableIntB g root = true ↔ dreachableIntProp g root := by
  simp only [dreachableIntB, dreachableIntProp, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev dreachableEnumProp (g : EnumGraph) (root : Int) : Prop :=
  enumLen g ∧ existsAux2 g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p => dreachableEnumCore g root d p)

def dreachableEnumB (g : EnumGraph) (root : Int) : Bool :=
  enumLenB g && existsAux2B g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p => decide (dreachableEnumCore g root d p))

theorem dreachableEnumB_iff (g : EnumGraph) (root : Int) :
    dreachableEnumB g root = true ↔ dreachableEnumProp g root := by
  simp only [dreachableEnumB, dreachableEnumProp, Bool.and_eq_true,
    enumLenB_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

/-! ## `fzn_dtree` -/

abbrev dtreeIntProp (g : IntGraph) (root : Int) : Prop :=
  intLen g ∧ existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dtreeIntCore g root d p)

def dtreeIntB (g : IntGraph) (root : Int) : Bool :=
  decide (intLen g) && existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => decide (dtreeIntCore g root d p))

theorem dtreeIntB_iff (g : IntGraph) (root : Int) :
    dtreeIntB g root = true ↔ dtreeIntProp g root := by
  simp only [dtreeIntB, dtreeIntProp, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev dtreeEnumProp (g : EnumGraph) (root : Int) : Prop :=
  enumLen g ∧ existsAux2 g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p => dtreeEnumCore g root d p)

def dtreeEnumB (g : EnumGraph) (root : Int) : Bool :=
  enumLenB g && existsAux2B g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p => decide (dtreeEnumCore g root d p))

theorem dtreeEnumB_iff (g : EnumGraph) (root : Int) :
    dtreeEnumB g root = true ↔ dtreeEnumProp g root := by
  simp only [dtreeEnumB, dtreeEnumProp, Bool.and_eq_true,
    enumLenB_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

/-! ## `fzn_dpath` -/

abbrev dpathIntProp (g : IntGraph) (source sink : Int) : Prop :=
  (intLen g ∧ existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dtreeIntCore g source d p)) ∧
  existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dtreeIntCore (swapInt g) sink d p)

def dpathIntB (g : IntGraph) (source sink : Int) : Bool :=
  (decide (intLen g) &&
    existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
      (fun d p => decide (dtreeIntCore g source d p))) &&
  existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => decide (dtreeIntCore (swapInt g) sink d p))

theorem dpathIntB_iff (g : IntGraph) (source sink : Int) :
    dpathIntB g source sink = true ↔ dpathIntProp g source sink := by
  simp only [dpathIntB, dpathIntProp, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev dpathEnumProp (g : EnumGraph) (source sink : Int) : Prop :=
  enumLen g ∧ existsAux1 g.K 0 ((g.K : Int) - 1)
    (dpathEnumCore g source sink)

def dpathEnumB (g : EnumGraph) (source sink : Int) : Bool :=
  enumLenB g && existsAux1B g.K 0 ((g.K : Int) - 1)
    (fun d => decide (dpathEnumCore g source sink d))

theorem dpathEnumB_iff (g : EnumGraph) (source sink : Int) :
    dpathEnumB g source sink = true ↔ dpathEnumProp g source sink := by
  simp only [dpathEnumB, dpathEnumProp, Bool.and_eq_true,
    enumLenB_iff]
  rw [existsAux1B_iff (fun d => decide_eq_true_iff)]

/-! ## `fzn_reachable` -/

abbrev reachableIntInner (g : IntGraph) (root : Int) : Prop :=
  existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dreachableIntCore (dupInt g (g.es ++ g.es)) root d p)

def reachableIntInnerB (g : IntGraph) (root : Int) : Bool :=
  existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p =>
      decide (dreachableIntCore (dupInt g (g.es ++ g.es)) root d p))

theorem reachableIntInnerB_iff (g : IntGraph) (root : Int) :
    reachableIntInnerB g root = true ↔ reachableIntInner g root := by
  simp only [reachableIntInnerB, reachableIntInner]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev reachableIntProp (g : IntGraph) (root : Int) : Prop :=
  reachableIntGate g ∧ reachableIntInner g root

def reachableIntB (g : IntGraph) (root : Int) : Bool :=
  reachableIntGateB g && reachableIntInnerB g root

theorem reachableIntB_iff (g : IntGraph) (root : Int) :
    reachableIntB g root = true ↔ reachableIntProp g root := by
  simp only [reachableIntB, reachableIntProp, Bool.and_eq_true,
    reachableIntGateB_iff, reachableIntInnerB_iff]

abbrev reachableEnumInner (g : EnumGraph) (root : Int) : Prop :=
  existsAux2 g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p => dreachableEnumCore (dupEnum g (g.es ++ g.es)) root d p)

def reachableEnumInnerB (g : EnumGraph) (root : Int) : Bool :=
  existsAux2B g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
    (fun d p =>
      decide (dreachableEnumCore (dupEnum g (g.es ++ g.es)) root d p))

theorem reachableEnumInnerB_iff (g : EnumGraph) (root : Int) :
    reachableEnumInnerB g root = true ↔ reachableEnumInner g root := by
  simp only [reachableEnumInnerB, reachableEnumInner]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev reachableEnumProp (g : EnumGraph) (root : Int) : Prop :=
  treeEnumGate g ∧ reachableEnumInner g root

def reachableEnumB (g : EnumGraph) (root : Int) : Bool :=
  treeEnumGateB g && reachableEnumInnerB g root

theorem reachableEnumB_iff (g : EnumGraph) (root : Int) :
    reachableEnumB g root = true ↔ reachableEnumProp g root := by
  simp only [reachableEnumB, reachableEnumProp, Bool.and_eq_true,
    treeEnumGateB_iff, reachableEnumInnerB_iff]

/-! ## `fzn_tree` -/

abbrev treeIntInner (g : IntGraph) (root : Int) (des : List Bool) : Prop :=
  bridgeSel g.es des g.M ∧
    existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
      (fun d p => dtreeIntCore (dupInt g des) root d p)

def treeIntInnerB (g : IntGraph) (root : Int) (des : List Bool) : Bool :=
  decide (bridgeSel g.es des g.M) &&
    existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
      (fun d p => decide (dtreeIntCore (dupInt g des) root d p))

theorem treeIntInnerB_iff (g : IntGraph) (root : Int) (des : List Bool) :
    treeIntInnerB g root des = true ↔ treeIntInner g root des := by
  simp only [treeIntInnerB, treeIntInner, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev treeIntProp (g : IntGraph) (root : Int) : Prop :=
  treeIntGate g ∧ existsBits g.M2 (treeIntInner g root)

def treeIntB (g : IntGraph) (root : Int) : Bool :=
  treeIntGateB g && existsBitsB g.M2 (treeIntInnerB g root)

theorem treeIntB_iff (g : IntGraph) (root : Int) :
    treeIntB g root = true ↔ treeIntProp g root := by
  simp only [treeIntB, treeIntProp, Bool.and_eq_true, treeIntGateB_iff]
  rw [existsBitsB_iff (h := treeIntInnerB_iff g root)]

abbrev treeEnumInner (g : EnumGraph) (root : Int) (des : List Bool) : Prop :=
  bridgeSel g.es des g.M ∧
    existsAux2 g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
      (fun d p => dtreeEnumCore (dupEnum g des) root d p)

def treeEnumInnerB (g : EnumGraph) (root : Int) (des : List Bool) : Bool :=
  decide (bridgeSel g.es des g.M) &&
    existsAux2B g.K 0 ((g.K : Int) - 1) 1 (g.K : Int)
      (fun d p => decide (dtreeEnumCore (dupEnum g des) root d p))

theorem treeEnumInnerB_iff (g : EnumGraph) (root : Int) (des : List Bool) :
    treeEnumInnerB g root des = true ↔ treeEnumInner g root des := by
  simp only [treeEnumInnerB, treeEnumInner, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev treeEnumProp (g : EnumGraph) (root : Int) : Prop :=
  treeEnumGate g ∧ existsBits (2 * g.M) (treeEnumInner g root)

def treeEnumB (g : EnumGraph) (root : Int) : Bool :=
  treeEnumGateB g && existsBitsB (2 * g.M) (treeEnumInnerB g root)

theorem treeEnumB_iff (g : EnumGraph) (root : Int) :
    treeEnumB g root = true ↔ treeEnumProp g root := by
  simp only [treeEnumB, treeEnumProp, Bool.and_eq_true, treeEnumGateB_iff]
  rw [existsBitsB_iff (h := treeEnumInnerB_iff g root)]

/-! ## `fzn_path` -/

abbrev pathIntInner (g : IntGraph) (source sink : Int)
    (des : List Bool) : Prop :=
  (bridgeSel g.es des g.M ∧
    existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
      (fun d p => dtreeIntCore (dupInt g des) source d p)) ∧
  existsAux2 g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => dtreeIntCore (swapInt (dupInt g des)) sink d p)

def pathIntInnerB (g : IntGraph) (source sink : Int)
    (des : List Bool) : Bool :=
  (decide (bridgeSel g.es des g.M) &&
    existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
      (fun d p => decide (dtreeIntCore (dupInt g des) source d p))) &&
  existsAux2B g.K 0 ((g.K : Int) - 1) 0 (g.K : Int)
    (fun d p => decide (dtreeIntCore (swapInt (dupInt g des)) sink d p))

theorem pathIntInnerB_iff (g : IntGraph) (source sink : Int)
    (des : List Bool) :
    pathIntInnerB g source sink des = true ↔
      pathIntInner g source sink des := by
  simp only [pathIntInnerB, pathIntInner, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]
  rw [existsAux2B_iff (fun d p => decide_eq_true_iff)]

abbrev pathIntProp (g : IntGraph) (source sink : Int) : Prop :=
  pathIntGate g ∧ existsBits g.M2 (pathIntInner g source sink)

def pathIntB (g : IntGraph) (source sink : Int) : Bool :=
  treeIntGateB g && existsBitsB g.M2 (pathIntInnerB g source sink)

theorem pathIntB_iff (g : IntGraph) (source sink : Int) :
    pathIntB g source sink = true ↔ pathIntProp g source sink := by
  simp only [pathIntB, pathIntProp, pathIntGate, Bool.and_eq_true,
    treeIntGateB_iff]
  rw [existsBitsB_iff (h := pathIntInnerB_iff g source sink)]

abbrev pathEnumInner (g : EnumGraph) (source sink : Int)
    (des : List Bool) : Prop :=
  bridgeSel g.es des g.M ∧
    existsAux1 g.K 0 ((g.K : Int) - 1)
      (dpathEnumCore (dupEnum g des) source sink)

def pathEnumInnerB (g : EnumGraph) (source sink : Int)
    (des : List Bool) : Bool :=
  decide (bridgeSel g.es des g.M) &&
    existsAux1B g.K 0 ((g.K : Int) - 1)
      (fun d => decide (dpathEnumCore (dupEnum g des) source sink d))

theorem pathEnumInnerB_iff (g : EnumGraph) (source sink : Int)
    (des : List Bool) :
    pathEnumInnerB g source sink des = true ↔
      pathEnumInner g source sink des := by
  simp only [pathEnumInnerB, pathEnumInner, Bool.and_eq_true,
    decide_eq_true_iff]
  rw [existsAux1B_iff (fun d => decide_eq_true_iff)]

abbrev pathEnumProp (g : EnumGraph) (source sink : Int) : Prop :=
  treeEnumGate g ∧ existsBits (2 * g.M) (pathEnumInner g source sink)

def pathEnumB (g : EnumGraph) (source sink : Int) : Bool :=
  treeEnumGateB g && existsBitsB (2 * g.M) (pathEnumInnerB g source sink)

theorem pathEnumB_iff (g : EnumGraph) (source sink : Int) :
    pathEnumB g source sink = true ↔ pathEnumProp g source sink := by
  simp only [pathEnumB, pathEnumProp, Bool.and_eq_true, treeEnumGateB_iff]
  rw [existsBitsB_iff (h := pathEnumInnerB_iff g source sink)]

/-! ## `fzn_dag` -/

abbrev dagEnumProp (g : EnumGraph) : Prop :=
  existsAux1 g.K 0 ((g.K : Int) - 1) (dagEnumCore g)

def dagEnumB (g : EnumGraph) : Bool :=
  existsAux1B g.K 0 ((g.K : Int) - 1) (fun d => decide (dagEnumCore g d))

theorem dagEnumB_iff (g : EnumGraph) :
    dagEnumB g = true ↔ dagEnumProp g := by
  simp only [dagEnumB, dagEnumProp]
  rw [existsAux1B_iff (fun d => decide_eq_true_iff)]

/-! ## `fzn_connected` / `fzn_dconnected` -/

abbrev connectedProp (g : EnumGraph) : Prop :=
  enumLen g ∧ existsRoot g.K (reachableEnumProp g)

def connectedB (g : EnumGraph) : Bool :=
  enumLenB g && existsRootB g.K (reachableEnumB g)

theorem connectedB_iff (g : EnumGraph) :
    connectedB g = true ↔ connectedProp g := by
  simp only [connectedB, connectedProp, Bool.and_eq_true, enumLenB_iff]
  rw [existsRootB_iff (h := fun r => reachableEnumB_iff g r)]

abbrev dconnectedProp (g : EnumGraph) : Prop :=
  enumLen g ∧ existsRoot g.K (dreachableEnumProp g)

def dconnectedB (g : EnumGraph) : Bool :=
  enumLenB g && existsRootB g.K (dreachableEnumB g)

theorem dconnectedB_iff (g : EnumGraph) :
    dconnectedB g = true ↔ dconnectedProp g := by
  simp only [dconnectedB, dconnectedProp, Bool.and_eq_true, enumLenB_iff]
  rw [existsRootB_iff (h := fun r => dreachableEnumB_iff g r)]

/-! ## Weights, bounded paths, Steiner trees -/

abbrev weightOk (g : IntGraph) (w : List Int) (bound : Int) : Prop :=
  req (sumOpt (List.ofFn fun e : Fin g.M =>
    weightTerm g.es w (idN e))) (fun s => s = bound)

def weightB (g : IntGraph) (w : List Int) (bound : Int) : Bool :=
  decide (weightOk g w bound)

theorem weightB_iff (g : IntGraph) (w : List Int) (bound : Int) :
    weightB g w bound = true ↔ weightOk g w bound :=
  decide_eq_true_iff

abbrev boundedPathIntProp (g : IntGraph) (w : List Int)
    (source sink bound : Int) : Prop :=
  (intLen g ∧ pathIntProp g source sink) ∧ weightOk g w bound

def boundedPathIntB (g : IntGraph) (w : List Int)
    (source sink bound : Int) : Bool :=
  (decide (intLen g) && pathIntB g source sink) && weightB g w bound

theorem boundedPathIntB_iff (g : IntGraph) (w : List Int)
    (source sink bound : Int) :
    boundedPathIntB g w source sink bound = true ↔
      boundedPathIntProp g w source sink bound := by
  simp only [boundedPathIntB, boundedPathIntProp, Bool.and_eq_true,
    decide_eq_true_iff, pathIntB_iff, weightB_iff]

abbrev boundedDpathIntProp (g : IntGraph) (w : List Int)
    (source sink bound : Int) : Prop :=
  (intLen g ∧ dpathIntProp g source sink) ∧ weightOk g w bound

def boundedDpathIntB (g : IntGraph) (w : List Int)
    (source sink bound : Int) : Bool :=
  (decide (intLen g) && dpathIntB g source sink) && weightB g w bound

theorem boundedDpathIntB_iff (g : IntGraph) (w : List Int)
    (source sink bound : Int) :
    boundedDpathIntB g w source sink bound = true ↔
      boundedDpathIntProp g w source sink bound := by
  simp only [boundedDpathIntB, boundedDpathIntProp, Bool.and_eq_true,
    decide_eq_true_iff, dpathIntB_iff, weightB_iff]

abbrev weightEnumOk (g : EnumGraph) (w : List Int) (bound : Int) : Prop :=
  req (sumOpt (List.ofFn fun e : Fin g.M =>
    weightTerm g.es w (idN e))) (fun s => s = bound)

def weightEnumB (g : EnumGraph) (w : List Int) (bound : Int) : Bool :=
  decide (weightEnumOk g w bound)

theorem weightEnumB_iff (g : EnumGraph) (w : List Int) (bound : Int) :
    weightEnumB g w bound = true ↔ weightEnumOk g w bound :=
  decide_eq_true_iff

abbrev boundedPathEnumProp (g : EnumGraph) (w : List Int)
    (source sink bound : Int) : Prop :=
  (enumLen g ∧ pathEnumProp g source sink) ∧ weightEnumOk g w bound

def boundedPathEnumB (g : EnumGraph) (w : List Int)
    (source sink bound : Int) : Bool :=
  (enumLenB g && pathEnumB g source sink) && weightEnumB g w bound

theorem boundedPathEnumB_iff (g : EnumGraph) (w : List Int)
    (source sink bound : Int) :
    boundedPathEnumB g w source sink bound = true ↔
      boundedPathEnumProp g w source sink bound := by
  simp only [boundedPathEnumB, boundedPathEnumProp, Bool.and_eq_true,
    enumLenB_iff, pathEnumB_iff, weightEnumB_iff]

abbrev boundedDpathEnumProp (g : EnumGraph) (w : List Int)
    (source sink bound : Int) : Prop :=
  (enumLen g ∧ dpathEnumProp g source sink) ∧ weightEnumOk g w bound

def boundedDpathEnumB (g : EnumGraph) (w : List Int)
    (source sink bound : Int) : Bool :=
  (enumLenB g && dpathEnumB g source sink) && weightEnumB g w bound

theorem boundedDpathEnumB_iff (g : EnumGraph) (w : List Int)
    (source sink bound : Int) :
    boundedDpathEnumB g w source sink bound = true ↔
      boundedDpathEnumProp g w source sink bound := by
  simp only [boundedDpathEnumB, boundedDpathEnumProp, Bool.and_eq_true,
    enumLenB_iff, dpathEnumB_iff, weightEnumB_iff]

/-! ## `fzn_steiner` / `fzn_dsteiner` -/

abbrev steinerInner (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) : Prop :=
  treeIntProp g r ∧ weightOk g w bound

def steinerInnerB (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) : Bool :=
  treeIntB g r && weightB g w bound

theorem steinerInnerB_iff (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) :
    steinerInnerB g w bound r = true ↔ steinerInner g w bound r := by
  simp only [steinerInnerB, steinerInner, Bool.and_eq_true,
    treeIntB_iff, weightB_iff]

abbrev steinerProp (g : IntGraph) (w : List Int) (bound : Int) : Prop :=
  intLen g ∧ existsRoot g.K (steinerInner g w bound)

def steinerB (g : IntGraph) (w : List Int) (bound : Int) : Bool :=
  decide (intLen g) && existsRootB g.K (steinerInnerB g w bound)

theorem steinerB_iff (g : IntGraph) (w : List Int) (bound : Int) :
    steinerB g w bound = true ↔ steinerProp g w bound := by
  simp only [steinerB, steinerProp, Bool.and_eq_true, decide_eq_true_iff]
  rw [existsRootB_iff (h := steinerInnerB_iff g w bound)]

abbrev dsteinerProp (g : IntGraph) (w : List Int) (root bound : Int) : Prop :=
  (intLen g ∧ dtreeIntProp g root) ∧ weightOk g w bound

def dsteinerB (g : IntGraph) (w : List Int) (root bound : Int) : Bool :=
  (decide (intLen g) && dtreeIntB g root) && weightB g w bound

theorem dsteinerB_iff (g : IntGraph) (w : List Int) (root bound : Int) :
    dsteinerB g w root bound = true ↔ dsteinerProp g w root bound := by
  simp only [dsteinerB, dsteinerProp, Bool.and_eq_true, decide_eq_true_iff,
    dtreeIntB_iff, weightB_iff]

/-! ## `fzn_wst` / `fzn_dwst` -/

abbrev wstInner (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) : Prop :=
  treeIntProp (allTrueGraph g) r ∧ weightOk g w bound

def wstInnerB (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) : Bool :=
  treeIntB (allTrueGraph g) r && weightB g w bound

theorem wstInnerB_iff (g : IntGraph) (w : List Int) (bound : Int)
    (r : Int) :
    wstInnerB g w bound r = true ↔ wstInner g w bound r := by
  simp only [wstInnerB, wstInner, Bool.and_eq_true,
    treeIntB_iff, weightB_iff]

abbrev wstProp (g : IntGraph) (w : List Int) (bound : Int) : Prop :=
  stGate g ∧ existsRoot g.K (wstInner g w bound)

def wstB (g : IntGraph) (w : List Int) (bound : Int) : Bool :=
  stGateB g && existsRootB g.K (wstInnerB g w bound)

theorem wstB_iff (g : IntGraph) (w : List Int) (bound : Int) :
    wstB g w bound = true ↔ wstProp g w bound := by
  simp only [wstB, wstProp, Bool.and_eq_true, stGateB_iff]
  rw [existsRootB_iff (h := wstInnerB_iff g w bound)]

abbrev dwstProp (g : IntGraph) (w : List Int) (root bound : Int) : Prop :=
  (stGate g ∧ dtreeIntProp (allTrueGraph g) root) ∧ weightOk g w bound

def dwstB (g : IntGraph) (w : List Int) (root bound : Int) : Bool :=
  (stGateB g && dtreeIntB (allTrueGraph g) root) && weightB g w bound

theorem dwstB_iff (g : IntGraph) (w : List Int) (root bound : Int) :
    dwstB g w root bound = true ↔ dwstProp g w root bound := by
  simp only [dwstB, dwstProp, Bool.and_eq_true, stGateB_iff,
    dtreeIntB_iff, weightB_iff]

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

/-- `fzn_subcircuit(xs)`: the values are all different; every value is
    in `1..n`; the non-fixed positions form one single cycle (or there
    are none: the empty subcircuit is allowed). -/
def subcircuitProp (xs : List Int) : Prop :=
  xs.Nodup ∧
  (List.range xs.length).all (fun i =>
    match xs[i]? with
    | some v => decide (1 ≤ v ∧ v ≤ (xs.length : Int))
    | none => false) = true ∧
    subcircuitCore xs = true

/-- Boolean twin of `subcircuitProp`. -/
def subcircuitB (xs : List Int) : Bool :=
  decide xs.Nodup &&
  (List.range xs.length).all (fun i =>
    match xs[i]? with
    | some v => decide (1 ≤ v ∧ v ≤ (xs.length : Int))
    | none => false) &&
    subcircuitCore xs

theorem subcircuitB_iff (xs : List Int) :
    subcircuitB xs = true ↔ subcircuitProp xs := by
  simp only [subcircuitB, subcircuitProp, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc]

/-! ## Argument decoders -/

/-- Decode the circuit argument. -/
private def oneIntArray' (args : List Value) : Option (List Int) :=
  match args with
  | [Value.array xs] => valueInts xs
  | _ => none

/-- Decode the common int-form prefix `N,E,from,to,ns,es` and return
    the graph together with the trailing arguments. -/
private def intFields : List Value → Option (IntGraph × List Value)
  | Value.int n :: Value.int e :: Value.array f :: Value.array t ::
      Value.array nsA :: Value.array esA :: rest =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl =>
          some (⟨n, e, fa, ta, nsl, esl⟩, rest)
      | _, _, _, _ => none
  | _ => none

/-- Decode the common enum-form prefix `from,to,ns,es` and return the
    graph together with the trailing arguments. -/
private def enumFields : List Value → Option (EnumGraph × List Value)
  | Value.array f :: Value.array t :: Value.array nsA ::
      Value.array esA :: rest =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl => some (⟨fa, ta, nsl, esl⟩, rest)
      | _, _, _, _ => none
  | _ => none

/-- Decode exactly `from,to,ns,es` (the `_enum`-only predicates). -/
private def enumGraph4Args (args : List Value) : Option EnumGraph :=
  match enumFields args with
  | some (g, []) => some g
  | _ => none

/-- Decode `fzn_subgraph`: `_int` `N,E,from,to,ns,es` or `_enum`
    `from,to,ns,es`. -/
private def subgraphArgs (args : List Value) :
    Option (Sum IntGraph EnumGraph) :=
  match intFields args with
  | some (g, []) => some (.inl g)
  | _ =>
    match enumFields args with
    | some (g, []) => some (.inr g)
    | _ => none

/-- Decode `fzn_reachable`/`fzn_dreachable`/`fzn_tree`/`fzn_dtree`:
    `N,E,from,to,root,ns,es` or `from,to,root,ns,es`.  The root
    argument comes before `ns,es` in both overloads. -/
private def rootArgs (args : List Value) :
    Option (Sum (IntGraph × Int) (EnumGraph × Int)) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.int root, Value.array nsA, Value.array esA] =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl =>
          some (.inl (⟨n, e, fa, ta, nsl, esl⟩, root))
      | _, _, _, _ => none
  | [Value.array f, Value.array t, Value.int root,
     Value.array nsA, Value.array esA] =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl =>
          some (.inr (⟨fa, ta, nsl, esl⟩, root))
      | _, _, _, _ => none
  | _ => none

/-- Decode `fzn_path`/`fzn_dpath`:
    `N,E,from,to,source,sink,ns,es` or `from,to,source,sink,ns,es`.
    The endpoint arguments come before `ns,es` in both overloads. -/
private def pathArgs (args : List Value) :
    Option (Sum (IntGraph × Int × Int) (EnumGraph × Int × Int)) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.int source, Value.int sink, Value.array nsA, Value.array esA] =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl =>
          some (.inl (⟨n, e, fa, ta, nsl, esl⟩, source, sink))
      | _, _, _, _ => none
  | [Value.array f, Value.array t, Value.int source, Value.int sink,
     Value.array nsA, Value.array esA] =>
      match valueInts f, valueInts t, valueBools nsA, valueBools esA with
      | some fa, some ta, some nsl, some esl =>
          some (.inr (⟨fa, ta, nsl, esl⟩, source, sink))
      | _, _, _, _ => none
  | _ => none

/-- Decode `fzn_bounded_path`/`fzn_bounded_dpath`:
    `N,E,from,to,w,source,sink,ns,es,bound` or
    `from,to,w,source,sink,ns,es,bound`. -/
private def boundedPathArgs (args : List Value) :
    Option (Sum (IntGraph × List Int × Int × Int × Int)
      (EnumGraph × List Int × Int × Int × Int)) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.array wA, Value.int source, Value.int sink,
     Value.array nsA, Value.array esA, Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools nsA,
        valueBools esA with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (.inl (⟨n, e, fa, ta, nsl, esl⟩, wl, source, sink, bound))
      | _, _, _, _, _ => none
  | [Value.array f, Value.array t, Value.array wA, Value.int source,
     Value.int sink, Value.array nsA, Value.array esA, Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools nsA,
        valueBools esA with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (.inr (⟨fa, ta, nsl, esl⟩, wl, source, sink, bound))
      | _, _, _, _, _ => none
  | _ => none

/-- Decode `fzn_steiner`: `N,E,from,to,w,ns,es,bound`. -/
private def steinerArgs (args : List Value) :
    Option (IntGraph × List Int × Int) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.array wA, Value.array nsA, Value.array esA, Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools nsA,
        valueBools esA with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (⟨n, e, fa, ta, nsl, esl⟩, wl, bound)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode `fzn_dsteiner`: `N,E,from,to,w,root,ns,es,bound`. -/
private def dsteinerArgs (args : List Value) :
    Option (IntGraph × List Int × Int × Int) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.array wA, Value.int root, Value.array nsA, Value.array esA,
     Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools nsA,
        valueBools esA with
      | some fa, some ta, some wl, some nsl, some esl =>
          some (⟨n, e, fa, ta, nsl, esl⟩, wl, root, bound)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode `fzn_wst`: `N,E,from,to,w,es,bound` (no `ns` argument;
    the node array is `[true | n ∈ 1..N]` inside the relation). -/
private def wstArgs (args : List Value) :
    Option (IntGraph × List Int × Int) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.array wA, Value.array esA, Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools esA with
      | some fa, some ta, some wl, some esl =>
          some (⟨n, e, fa, ta, [], esl⟩, wl, bound)
      | _, _, _, _ => none
  | _ => none

/-- Decode `fzn_dwst`: `N,E,from,to,w,root,es,bound` (no `ns`). -/
private def dwstArgs (args : List Value) :
    Option (IntGraph × List Int × Int × Int) :=
  match args with
  | [Value.int n, Value.int e, Value.array f, Value.array t,
     Value.array wA, Value.int root, Value.array esA, Value.int bound] =>
      match valueInts f, valueInts t, valueInts wA, valueBools esA with
      | some fa, some ta, some wl, some esl =>
          some (⟨n, e, fa, ta, [], esl⟩, wl, root, bound)
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
    match subgraphArgs args with
    | some (.inl g) => subgraphIntProp g
    | some (.inr g) => subgraphEnumProp g
    | none => False
  | "fzn_dag" => fun args =>
    match enumGraph4Args args with
    | some g => dagEnumProp g
    | none => False
  | "fzn_connected" => fun args =>
    match enumGraph4Args args with
    | some g => connectedProp g
    | none => False
  | "fzn_dconnected" => fun args =>
    match enumGraph4Args args with
    | some g => dconnectedProp g
    | none => False
  | "fzn_reachable" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => reachableIntProp g root
    | some (.inr (g, root)) => reachableEnumProp g root
    | none => False
  | "fzn_dreachable" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => dreachableIntProp g root
    | some (.inr (g, root)) => dreachableEnumProp g root
    | none => False
  | "fzn_tree" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => treeIntProp g root
    | some (.inr (g, root)) => treeEnumProp g root
    | none => False
  | "fzn_dtree" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => dtreeIntProp g root
    | some (.inr (g, root)) => dtreeEnumProp g root
    | none => False
  | "fzn_path" => fun args =>
    match pathArgs args with
    | some (.inl (g, source, sink)) => pathIntProp g source sink
    | some (.inr (g, source, sink)) => pathEnumProp g source sink
    | none => False
  | "fzn_dpath" => fun args =>
    match pathArgs args with
    | some (.inl (g, source, sink)) => dpathIntProp g source sink
    | some (.inr (g, source, sink)) => dpathEnumProp g source sink
    | none => False
  | "fzn_bounded_path" => fun args =>
    match boundedPathArgs args with
    | some (.inl (g, w, source, sink, bound)) =>
        boundedPathIntProp g w source sink bound
    | some (.inr (g, w, source, sink, bound)) =>
        boundedPathEnumProp g w source sink bound
    | none => False
  | "fzn_bounded_dpath" => fun args =>
    match boundedPathArgs args with
    | some (.inl (g, w, source, sink, bound)) =>
        boundedDpathIntProp g w source sink bound
    | some (.inr (g, w, source, sink, bound)) =>
        boundedDpathEnumProp g w source sink bound
    | none => False
  | "fzn_steiner" => fun args =>
    match steinerArgs args with
    | some (g, w, bound) => steinerProp g w bound
    | none => False
  | "fzn_dsteiner" => fun args =>
    match dsteinerArgs args with
    | some (g, w, root, bound) => dsteinerProp g w root bound
    | none => False
  | "fzn_wst" => fun args =>
    match wstArgs args with
    | some (g, w, bound) => wstProp g w bound
    | none => False
  | "fzn_dwst" => fun args =>
    match dwstArgs args with
    | some (g, w, root, bound) => dwstProp g w root bound
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
    match subgraphArgs args with
    | some (.inl g) => subgraphIntB g
    | some (.inr g) => subgraphEnumB g
    | none => false
  | "fzn_dag" => fun args =>
    match enumGraph4Args args with
    | some g => dagEnumB g
    | none => false
  | "fzn_connected" => fun args =>
    match enumGraph4Args args with
    | some g => connectedB g
    | none => false
  | "fzn_dconnected" => fun args =>
    match enumGraph4Args args with
    | some g => dconnectedB g
    | none => false
  | "fzn_reachable" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => reachableIntB g root
    | some (.inr (g, root)) => reachableEnumB g root
    | none => false
  | "fzn_dreachable" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => dreachableIntB g root
    | some (.inr (g, root)) => dreachableEnumB g root
    | none => false
  | "fzn_tree" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => treeIntB g root
    | some (.inr (g, root)) => treeEnumB g root
    | none => false
  | "fzn_dtree" => fun args =>
    match rootArgs args with
    | some (.inl (g, root)) => dtreeIntB g root
    | some (.inr (g, root)) => dtreeEnumB g root
    | none => false
  | "fzn_path" => fun args =>
    match pathArgs args with
    | some (.inl (g, source, sink)) => pathIntB g source sink
    | some (.inr (g, source, sink)) => pathEnumB g source sink
    | none => false
  | "fzn_dpath" => fun args =>
    match pathArgs args with
    | some (.inl (g, source, sink)) => dpathIntB g source sink
    | some (.inr (g, source, sink)) => dpathEnumB g source sink
    | none => false
  | "fzn_bounded_path" => fun args =>
    match boundedPathArgs args with
    | some (.inl (g, w, source, sink, bound)) =>
        boundedPathIntB g w source sink bound
    | some (.inr (g, w, source, sink, bound)) =>
        boundedPathEnumB g w source sink bound
    | none => false
  | "fzn_bounded_dpath" => fun args =>
    match boundedPathArgs args with
    | some (.inl (g, w, source, sink, bound)) =>
        boundedDpathIntB g w source sink bound
    | some (.inr (g, w, source, sink, bound)) =>
        boundedDpathEnumB g w source sink bound
    | none => false
  | "fzn_steiner" => fun args =>
    match steinerArgs args with
    | some (g, w, bound) => steinerB g w bound
    | none => false
  | "fzn_dsteiner" => fun args =>
    match dsteinerArgs args with
    | some (g, w, root, bound) => dsteinerB g w root bound
    | none => false
  | "fzn_wst" => fun args =>
    match wstArgs args with
    | some (g, w, bound) => wstB g w bound
    | none => false
  | "fzn_dwst" => fun args =>
    match dwstArgs args with
    | some (g, w, root, bound) => dwstB g w root bound
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
  | some xs => simp only [circuitB_iff]

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
  | some xs => simp only [subcircuitB_iff]

theorem fzn_subgraph_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_subgraph") args = true ↔
      graphInterp (Ident.mk "fzn_subgraph") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_subgraph") args
      = match subgraphArgs args with
      | some (.inl g) => subgraphIntB g
      | some (.inr g) => subgraphEnumB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_subgraph") args
      = match subgraphArgs args with
      | some (.inl g) => subgraphIntProp g
      | some (.inr g) => subgraphEnumProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : subgraphArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl g => simp only [subgraphIntB_iff]
    | inr g => simp only [subgraphEnumB_iff]

theorem fzn_dag_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dag") args = true ↔
      graphInterp (Ident.mk "fzn_dag") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dag") args
      = match enumGraph4Args args with
      | some g => dagEnumB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dag") args
      = match enumGraph4Args args with
      | some g => dagEnumProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : enumGraph4Args args with
  | none => simp
  | some g => simp only [dagEnumB_iff]

theorem fzn_connected_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_connected") args = true ↔
      graphInterp (Ident.mk "fzn_connected") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_connected") args
      = match enumGraph4Args args with
      | some g => connectedB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_connected") args
      = match enumGraph4Args args with
      | some g => connectedProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : enumGraph4Args args with
  | none => simp
  | some g => simp only [connectedB_iff]

theorem fzn_dconnected_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dconnected") args = true ↔
      graphInterp (Ident.mk "fzn_dconnected") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dconnected") args
      = match enumGraph4Args args with
      | some g => dconnectedB g
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dconnected") args
      = match enumGraph4Args args with
      | some g => dconnectedProp g
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : enumGraph4Args args with
  | none => simp
  | some g => simp only [dconnectedB_iff]

theorem fzn_reachable_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_reachable") args = true ↔
      graphInterp (Ident.mk "fzn_reachable") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_reachable") args
      = match rootArgs args with
      | some (.inl (g, root)) => reachableIntB g root
      | some (.inr (g, root)) => reachableEnumB g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_reachable") args
      = match rootArgs args with
      | some (.inl (g, root)) => reachableIntProp g root
      | some (.inr (g, root)) => reachableEnumProp g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : rootArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gr =>
      obtain ⟨g, root⟩ := gr
      simp only [reachableIntB_iff]
    | inr gr =>
      obtain ⟨g, root⟩ := gr
      simp only [reachableEnumB_iff]

theorem fzn_dreachable_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dreachable") args = true ↔
      graphInterp (Ident.mk "fzn_dreachable") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dreachable") args
      = match rootArgs args with
      | some (.inl (g, root)) => dreachableIntB g root
      | some (.inr (g, root)) => dreachableEnumB g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dreachable") args
      = match rootArgs args with
      | some (.inl (g, root)) => dreachableIntProp g root
      | some (.inr (g, root)) => dreachableEnumProp g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : rootArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gr =>
      obtain ⟨g, root⟩ := gr
      simp only [dreachableIntB_iff]
    | inr gr =>
      obtain ⟨g, root⟩ := gr
      simp only [dreachableEnumB_iff]

theorem fzn_tree_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_tree") args = true ↔
      graphInterp (Ident.mk "fzn_tree") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_tree") args
      = match rootArgs args with
      | some (.inl (g, root)) => treeIntB g root
      | some (.inr (g, root)) => treeEnumB g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_tree") args
      = match rootArgs args with
      | some (.inl (g, root)) => treeIntProp g root
      | some (.inr (g, root)) => treeEnumProp g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : rootArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gr =>
      obtain ⟨g, root⟩ := gr
      simp only [treeIntB_iff]
    | inr gr =>
      obtain ⟨g, root⟩ := gr
      simp only [treeEnumB_iff]

theorem fzn_dtree_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dtree") args = true ↔
      graphInterp (Ident.mk "fzn_dtree") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dtree") args
      = match rootArgs args with
      | some (.inl (g, root)) => dtreeIntB g root
      | some (.inr (g, root)) => dtreeEnumB g root
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dtree") args
      = match rootArgs args with
      | some (.inl (g, root)) => dtreeIntProp g root
      | some (.inr (g, root)) => dtreeEnumProp g root
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : rootArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gr =>
      obtain ⟨g, root⟩ := gr
      simp only [dtreeIntB_iff]
    | inr gr =>
      obtain ⟨g, root⟩ := gr
      simp only [dtreeEnumB_iff]

theorem fzn_path_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_path") args = true ↔
      graphInterp (Ident.mk "fzn_path") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_path") args
      = match pathArgs args with
      | some (.inl (g, source, sink)) => pathIntB g source sink
      | some (.inr (g, source, sink)) => pathEnumB g source sink
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_path") args
      = match pathArgs args with
      | some (.inl (g, source, sink)) => pathIntProp g source sink
      | some (.inr (g, source, sink)) => pathEnumProp g source sink
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : pathArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gs =>
      obtain ⟨g, source, sink⟩ := gs
      simp only [pathIntB_iff]
    | inr gs =>
      obtain ⟨g, source, sink⟩ := gs
      simp only [pathEnumB_iff]

theorem fzn_dpath_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dpath") args = true ↔
      graphInterp (Ident.mk "fzn_dpath") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dpath") args
      = match pathArgs args with
      | some (.inl (g, source, sink)) => dpathIntB g source sink
      | some (.inr (g, source, sink)) => dpathEnumB g source sink
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dpath") args
      = match pathArgs args with
      | some (.inl (g, source, sink)) => dpathIntProp g source sink
      | some (.inr (g, source, sink)) => dpathEnumProp g source sink
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : pathArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gs =>
      obtain ⟨g, source, sink⟩ := gs
      simp only [dpathIntB_iff]
    | inr gs =>
      obtain ⟨g, source, sink⟩ := gs
      simp only [dpathEnumB_iff]

theorem fzn_bounded_path_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_bounded_path") args = true ↔
      graphInterp (Ident.mk "fzn_bounded_path") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_bounded_path") args
      = match boundedPathArgs args with
      | some (.inl (g, w, source, sink, bound)) =>
          boundedPathIntB g w source sink bound
      | some (.inr (g, w, source, sink, bound)) =>
          boundedPathEnumB g w source sink bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_bounded_path") args
      = match boundedPathArgs args with
      | some (.inl (g, w, source, sink, bound)) =>
          boundedPathIntProp g w source sink bound
      | some (.inr (g, w, source, sink, bound)) =>
          boundedPathEnumProp g w source sink bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boundedPathArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gs =>
      obtain ⟨g, w, source, sink, bound⟩ := gs
      simp only [boundedPathIntB_iff]
    | inr gs =>
      obtain ⟨g, w, source, sink, bound⟩ := gs
      simp only [boundedPathEnumB_iff]

theorem fzn_bounded_dpath_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_bounded_dpath") args = true ↔
      graphInterp (Ident.mk "fzn_bounded_dpath") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_bounded_dpath") args
      = match boundedPathArgs args with
      | some (.inl (g, w, source, sink, bound)) =>
          boundedDpathIntB g w source sink bound
      | some (.inr (g, w, source, sink, bound)) =>
          boundedDpathEnumB g w source sink bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_bounded_dpath") args
      = match boundedPathArgs args with
      | some (.inl (g, w, source, sink, bound)) =>
          boundedDpathIntProp g w source sink bound
      | some (.inr (g, w, source, sink, bound)) =>
          boundedDpathEnumProp g w source sink bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boundedPathArgs args with
  | none => simp
  | some s =>
    cases s with
    | inl gs =>
      obtain ⟨g, w, source, sink, bound⟩ := gs
      simp only [boundedDpathIntB_iff]
    | inr gs =>
      obtain ⟨g, w, source, sink, bound⟩ := gs
      simp only [boundedDpathEnumB_iff]

theorem fzn_steiner_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_steiner") args = true ↔
      graphInterp (Ident.mk "fzn_steiner") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_steiner") args
      = match steinerArgs args with
      | some (g, w, bound) => steinerB g w bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_steiner") args
      = match steinerArgs args with
      | some (g, w, bound) => steinerProp g w bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : steinerArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, bound⟩ := p
    simp only [steinerB_iff]

theorem fzn_dsteiner_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dsteiner") args = true ↔
      graphInterp (Ident.mk "fzn_dsteiner") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dsteiner") args
      = match dsteinerArgs args with
      | some (g, w, root, bound) => dsteinerB g w root bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dsteiner") args
      = match dsteinerArgs args with
      | some (g, w, root, bound) => dsteinerProp g w root bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : dsteinerArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, root, bound⟩ := p
    simp only [dsteinerB_iff]

theorem fzn_wst_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_wst") args = true ↔
      graphInterp (Ident.mk "fzn_wst") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_wst") args
      = match wstArgs args with
      | some (g, w, bound) => wstB g w bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_wst") args
      = match wstArgs args with
      | some (g, w, bound) => wstProp g w bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : wstArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, bound⟩ := p
    simp only [wstB_iff]

theorem fzn_dwst_iff (args : List Value) :
    graphInterpB (Ident.mk "fzn_dwst") args = true ↔
      graphInterp (Ident.mk "fzn_dwst") args := by
  have hB : ∀ args, graphInterpB (Ident.mk "fzn_dwst") args
      = match dwstArgs args with
      | some (g, w, root, bound) => dwstB g w root bound
      | none => false
      := fun _ => rfl
  have hI : ∀ args, graphInterp (Ident.mk "fzn_dwst") args
      = match dwstArgs args with
      | some (g, w, root, bound) => dwstProp g w root bound
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : dwstArgs args with
  | none => simp
  | some p =>
    obtain ⟨g, w, root, bound⟩ := p
    simp only [dwstB_iff]

/-! ## Decodability gates

`graphDecodes` is the Boolean decodability gate of the family: the `isSome`
of the very decoder `graphInterp` uses, and `true` outside the family.
`graphDecodes_agree` states that the gate cannot distinguish two argument
lists which agree on the shape information that is statically known from a
well-typed call (`ArgsAgree`): constructor tags and array lengths, plus the
exact values of the `par` arguments.  Every decoder in this family inspects
only constructor tags and routes array reads through `valueInts`/`valueBools`,
so the shape part of `ArgsAgree` already suffices; no `par` hypothesis is
needed. -/

/-- The `fzn_circuit`/`fzn_subcircuit` decoder accepts exactly the same
    argument shapes. -/
private theorem oneIntArray'_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (oneIntArray' vs).isSome = (oneIntArray' ws).isSome := by
  cases h with
  | nil => rfl
  | cons hv htail =>
    cases hv with
    | bool => rfl
    | int => rfl
    | setOfInt => rfl
    | array harr =>
      cases htail with
      | nil => exact valueInts_isSome_sameShape harr
      | cons _ _ => rfl

/-- The `enumGraph4Args` decoder accepts exactly the same argument shapes. -/
private theorem enumGraph4Args_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (enumGraph4Args vs).isSome = (enumGraph4Args ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | @array f1 f1' hf1 =>
      cases t0 with
      | nil => rfl
      | cons e3 t0' =>
        cases e3 with
        | @array t1 t1' ht1 =>
          cases t0' with
          | nil => rfl
          | cons e2 t0'' =>
            cases e2 with
            | @array nsA1 nsA1' hnsA1 =>
              cases t0'' with
              | nil => rfl
              | cons e1 t0''' =>
                cases e1 with
                | @array esA1 esA1' hesA1 =>
                  cases t0''' with
                  | nil =>
                    simp only [enumGraph4Args, enumFields]
                    have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                    have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                    have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                    have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                    cases hc_f1 : valueInts f1 with
                    | none =>
                      cases hc_f1' : valueInts f1' with
                      | none => rfl
                      | some _ => simp [hc_f1, hc_f1'] at hx_f1
                    | some _ =>
                      cases hc_f1' : valueInts f1' with
                      | none => simp [hc_f1, hc_f1'] at hx_f1
                      | some _ =>
                        cases hc_t1 : valueInts t1 with
                        | none =>
                          cases hc_t1' : valueInts t1' with
                          | none => rfl
                          | some _ => simp [hc_t1, hc_t1'] at hx_t1
                        | some _ =>
                          cases hc_t1' : valueInts t1' with
                          | none => simp [hc_t1, hc_t1'] at hx_t1
                          | some _ =>
                            cases hc_nsA1 : valueBools nsA1 with
                            | none =>
                              cases hc_nsA1' : valueBools nsA1' with
                              | none => rfl
                              | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                            | some _ =>
                              cases hc_nsA1' : valueBools nsA1' with
                              | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                              | some _ =>
                                cases hc_esA1 : valueBools esA1 with
                                | none =>
                                  cases hc_esA1' : valueBools esA1' with
                                  | none => rfl
                                  | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                | some _ =>
                                  cases hc_esA1' : valueBools esA1' with
                                  | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                  | some _ =>
                                    rfl
                  | cons _ _ =>
                    simp only [enumGraph4Args, enumFields]
                    have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                    have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                    have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                    have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                    cases hc_f1 : valueInts f1 with
                    | none =>
                      cases hc_f1' : valueInts f1' with
                      | none => rfl
                      | some _ => simp [hc_f1, hc_f1'] at hx_f1
                    | some _ =>
                      cases hc_f1' : valueInts f1' with
                      | none => simp [hc_f1, hc_f1'] at hx_f1
                      | some _ =>
                        cases hc_t1 : valueInts t1 with
                        | none =>
                          cases hc_t1' : valueInts t1' with
                          | none => rfl
                          | some _ => simp [hc_t1, hc_t1'] at hx_t1
                        | some _ =>
                          cases hc_t1' : valueInts t1' with
                          | none => simp [hc_t1, hc_t1'] at hx_t1
                          | some _ =>
                            cases hc_nsA1 : valueBools nsA1 with
                            | none =>
                              cases hc_nsA1' : valueBools nsA1' with
                              | none => rfl
                              | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                            | some _ =>
                              cases hc_nsA1' : valueBools nsA1' with
                              | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                              | some _ =>
                                cases hc_esA1 : valueBools esA1 with
                                | none =>
                                  cases hc_esA1' : valueBools esA1' with
                                  | none => rfl
                                  | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                | some _ =>
                                  cases hc_esA1' : valueBools esA1' with
                                  | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                  | some _ =>
                                    rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
    | int => rfl
    | bool => rfl
    | setOfInt => rfl

/-- The `subgraphArgs` decoder accepts exactly the same argument shapes. -/
private theorem subgraphArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (subgraphArgs vs).isSome = (subgraphArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e5 t0' =>
        cases e5 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e4 t0'' =>
            cases e4 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e3 t0''' =>
                cases e3 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e2 t0'''' =>
                    cases e2 with
                    | @array nsA1 nsA1' hnsA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e1 t0''''' =>
                        cases e1 with
                        | @array esA1 esA1' hesA1 =>
                          cases t0''''' with
                          | nil =>
                            simp only [subgraphArgs, intFields, enumFields]
                            have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                            have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                            have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                            have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                            cases hc_f1 : valueInts f1 with
                            | none =>
                              cases hc_f1' : valueInts f1' with
                              | none => rfl
                              | some _ => simp [hc_f1, hc_f1'] at hx_f1
                            | some _ =>
                              cases hc_f1' : valueInts f1' with
                              | none => simp [hc_f1, hc_f1'] at hx_f1
                              | some _ =>
                                cases hc_t1 : valueInts t1 with
                                | none =>
                                  cases hc_t1' : valueInts t1' with
                                  | none => rfl
                                  | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                | some _ =>
                                  cases hc_t1' : valueInts t1' with
                                  | none => simp [hc_t1, hc_t1'] at hx_t1
                                  | some _ =>
                                    cases hc_nsA1 : valueBools nsA1 with
                                    | none =>
                                      cases hc_nsA1' : valueBools nsA1' with
                                      | none => rfl
                                      | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                    | some _ =>
                                      cases hc_nsA1' : valueBools nsA1' with
                                      | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                      | some _ =>
                                        cases hc_esA1 : valueBools esA1 with
                                        | none =>
                                          cases hc_esA1' : valueBools esA1' with
                                          | none => rfl
                                          | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                        | some _ =>
                                          cases hc_esA1' : valueBools esA1' with
                                          | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                          | some _ =>
                                            rfl
                          | cons _ _ =>
                            simp only [subgraphArgs, intFields, enumFields]
                            have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                            have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                            have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                            have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                            cases hc_f1 : valueInts f1 with
                            | none =>
                              cases hc_f1' : valueInts f1' with
                              | none => rfl
                              | some _ => simp [hc_f1, hc_f1'] at hx_f1
                            | some _ =>
                              cases hc_f1' : valueInts f1' with
                              | none => simp [hc_f1, hc_f1'] at hx_f1
                              | some _ =>
                                cases hc_t1 : valueInts t1 with
                                | none =>
                                  cases hc_t1' : valueInts t1' with
                                  | none => rfl
                                  | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                | some _ =>
                                  cases hc_t1' : valueInts t1' with
                                  | none => simp [hc_t1, hc_t1'] at hx_t1
                                  | some _ =>
                                    cases hc_nsA1 : valueBools nsA1 with
                                    | none =>
                                      cases hc_nsA1' : valueBools nsA1' with
                                      | none => rfl
                                      | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                    | some _ =>
                                      cases hc_nsA1' : valueBools nsA1' with
                                      | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                      | some _ =>
                                        cases hc_esA1 : valueBools esA1 with
                                        | none =>
                                          cases hc_esA1' : valueBools esA1' with
                                          | none => rfl
                                          | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                        | some _ =>
                                          cases hc_esA1' : valueBools esA1' with
                                          | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                          | some _ =>
                                            rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | @array f2 f2' hf2 =>
      cases t0 with
      | nil => rfl
      | cons e3 t0' =>
        cases e3 with
        | @array t2 t2' ht2 =>
          cases t0' with
          | nil => rfl
          | cons e2 t0'' =>
            cases e2 with
            | @array nsA2 nsA2' hnsA2 =>
              cases t0'' with
              | nil => rfl
              | cons e1 t0''' =>
                cases e1 with
                | @array esA2 esA2' hesA2 =>
                  cases t0''' with
                  | nil =>
                    simp only [subgraphArgs, intFields, enumFields]
                    have hx_f2 : (valueInts f2).isSome = (valueInts f2').isSome := valueInts_isSome_sameShape hf2
                    have hx_t2 : (valueInts t2).isSome = (valueInts t2').isSome := valueInts_isSome_sameShape ht2
                    have hx_nsA2 : (valueBools nsA2).isSome = (valueBools nsA2').isSome := valueBools_isSome_sameShape hnsA2
                    have hx_esA2 : (valueBools esA2).isSome = (valueBools esA2').isSome := valueBools_isSome_sameShape hesA2
                    cases hc_f2 : valueInts f2 with
                    | none =>
                      cases hc_f2' : valueInts f2' with
                      | none => rfl
                      | some _ => simp [hc_f2, hc_f2'] at hx_f2
                    | some _ =>
                      cases hc_f2' : valueInts f2' with
                      | none => simp [hc_f2, hc_f2'] at hx_f2
                      | some _ =>
                        cases hc_t2 : valueInts t2 with
                        | none =>
                          cases hc_t2' : valueInts t2' with
                          | none => rfl
                          | some _ => simp [hc_t2, hc_t2'] at hx_t2
                        | some _ =>
                          cases hc_t2' : valueInts t2' with
                          | none => simp [hc_t2, hc_t2'] at hx_t2
                          | some _ =>
                            cases hc_nsA2 : valueBools nsA2 with
                            | none =>
                              cases hc_nsA2' : valueBools nsA2' with
                              | none => rfl
                              | some _ => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                            | some _ =>
                              cases hc_nsA2' : valueBools nsA2' with
                              | none => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                              | some _ =>
                                cases hc_esA2 : valueBools esA2 with
                                | none =>
                                  cases hc_esA2' : valueBools esA2' with
                                  | none => rfl
                                  | some _ => simp [hc_esA2, hc_esA2'] at hx_esA2
                                | some _ =>
                                  cases hc_esA2' : valueBools esA2' with
                                  | none => simp [hc_esA2, hc_esA2'] at hx_esA2
                                  | some _ =>
                                    rfl
                  | cons _ _ =>
                    simp only [subgraphArgs, intFields, enumFields]
                    have hx_f2 : (valueInts f2).isSome = (valueInts f2').isSome := valueInts_isSome_sameShape hf2
                    have hx_t2 : (valueInts t2).isSome = (valueInts t2').isSome := valueInts_isSome_sameShape ht2
                    have hx_nsA2 : (valueBools nsA2).isSome = (valueBools nsA2').isSome := valueBools_isSome_sameShape hnsA2
                    have hx_esA2 : (valueBools esA2).isSome = (valueBools esA2').isSome := valueBools_isSome_sameShape hesA2
                    cases hc_f2 : valueInts f2 with
                    | none =>
                      cases hc_f2' : valueInts f2' with
                      | none => rfl
                      | some _ => simp [hc_f2, hc_f2'] at hx_f2
                    | some _ =>
                      cases hc_f2' : valueInts f2' with
                      | none => simp [hc_f2, hc_f2'] at hx_f2
                      | some _ =>
                        cases hc_t2 : valueInts t2 with
                        | none =>
                          cases hc_t2' : valueInts t2' with
                          | none => rfl
                          | some _ => simp [hc_t2, hc_t2'] at hx_t2
                        | some _ =>
                          cases hc_t2' : valueInts t2' with
                          | none => simp [hc_t2, hc_t2'] at hx_t2
                          | some _ =>
                            cases hc_nsA2 : valueBools nsA2 with
                            | none =>
                              cases hc_nsA2' : valueBools nsA2' with
                              | none => rfl
                              | some _ => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                            | some _ =>
                              cases hc_nsA2' : valueBools nsA2' with
                              | none => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                              | some _ =>
                                cases hc_esA2 : valueBools esA2 with
                                | none =>
                                  cases hc_esA2' : valueBools esA2' with
                                  | none => rfl
                                  | some _ => simp [hc_esA2, hc_esA2'] at hx_esA2
                                | some _ =>
                                  cases hc_esA2' : valueBools esA2' with
                                  | none => simp [hc_esA2, hc_esA2'] at hx_esA2
                                  | some _ =>
                                    rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
    | bool => rfl
    | setOfInt => rfl

/-- The `rootArgs` decoder accepts exactly the same argument shapes. -/
private theorem rootArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (rootArgs vs).isSome = (rootArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e6 t0' =>
        cases e6 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e5 t0'' =>
            cases e5 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e4 t0''' =>
                cases e4 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e3 t0'''' =>
                    cases e3 with
                    | int =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e2 t0''''' =>
                        cases e2 with
                        | @array nsA1 nsA1' hnsA1 =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e1 t0'''''' =>
                            cases e1 with
                            | @array esA1 esA1' hesA1 =>
                              cases t0'''''' with
                              | nil =>
                                simp only [rootArgs]
                                have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                                have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                cases hc_f1 : valueInts f1 with
                                | none =>
                                  cases hc_f1' : valueInts f1' with
                                  | none => rfl
                                  | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                | some _ =>
                                  cases hc_f1' : valueInts f1' with
                                  | none => simp [hc_f1, hc_f1'] at hx_f1
                                  | some _ =>
                                    cases hc_t1 : valueInts t1 with
                                    | none =>
                                      cases hc_t1' : valueInts t1' with
                                      | none => rfl
                                      | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                    | some _ =>
                                      cases hc_t1' : valueInts t1' with
                                      | none => simp [hc_t1, hc_t1'] at hx_t1
                                      | some _ =>
                                        cases hc_nsA1 : valueBools nsA1 with
                                        | none =>
                                          cases hc_nsA1' : valueBools nsA1' with
                                          | none => rfl
                                          | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                        | some _ =>
                                          cases hc_nsA1' : valueBools nsA1' with
                                          | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                          | some _ =>
                                            cases hc_esA1 : valueBools esA1 with
                                            | none =>
                                              cases hc_esA1' : valueBools esA1' with
                                              | none => rfl
                                              | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                            | some _ =>
                                              cases hc_esA1' : valueBools esA1' with
                                              | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                              | some _ =>
                                                rfl
                              | cons _ _ =>
                                rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | setOfInt => rfl
                    | array => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | @array f2 f2' hf2 =>
      cases t0 with
      | nil => rfl
      | cons e4 t0' =>
        cases e4 with
        | @array t2 t2' ht2 =>
          cases t0' with
          | nil => rfl
          | cons e3 t0'' =>
            cases e3 with
            | int =>
              cases t0'' with
              | nil => rfl
              | cons e2 t0''' =>
                cases e2 with
                | @array nsA2 nsA2' hnsA2 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e1 t0'''' =>
                    cases e1 with
                    | @array esA2 esA2' hesA2 =>
                      cases t0'''' with
                      | nil =>
                        simp only [rootArgs]
                        have hx_f2 : (valueInts f2).isSome = (valueInts f2').isSome := valueInts_isSome_sameShape hf2
                        have hx_t2 : (valueInts t2).isSome = (valueInts t2').isSome := valueInts_isSome_sameShape ht2
                        have hx_nsA2 : (valueBools nsA2).isSome = (valueBools nsA2').isSome := valueBools_isSome_sameShape hnsA2
                        have hx_esA2 : (valueBools esA2).isSome = (valueBools esA2').isSome := valueBools_isSome_sameShape hesA2
                        cases hc_f2 : valueInts f2 with
                        | none =>
                          cases hc_f2' : valueInts f2' with
                          | none => rfl
                          | some _ => simp [hc_f2, hc_f2'] at hx_f2
                        | some _ =>
                          cases hc_f2' : valueInts f2' with
                          | none => simp [hc_f2, hc_f2'] at hx_f2
                          | some _ =>
                            cases hc_t2 : valueInts t2 with
                            | none =>
                              cases hc_t2' : valueInts t2' with
                              | none => rfl
                              | some _ => simp [hc_t2, hc_t2'] at hx_t2
                            | some _ =>
                              cases hc_t2' : valueInts t2' with
                              | none => simp [hc_t2, hc_t2'] at hx_t2
                              | some _ =>
                                cases hc_nsA2 : valueBools nsA2 with
                                | none =>
                                  cases hc_nsA2' : valueBools nsA2' with
                                  | none => rfl
                                  | some _ => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                | some _ =>
                                  cases hc_nsA2' : valueBools nsA2' with
                                  | none => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                  | some _ =>
                                    cases hc_esA2 : valueBools esA2 with
                                    | none =>
                                      cases hc_esA2' : valueBools esA2' with
                                      | none => rfl
                                      | some _ => simp [hc_esA2, hc_esA2'] at hx_esA2
                                    | some _ =>
                                      cases hc_esA2' : valueBools esA2' with
                                      | none => simp [hc_esA2, hc_esA2'] at hx_esA2
                                      | some _ =>
                                        rfl
                      | cons _ _ =>
                        rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | setOfInt => rfl
            | array => rfl
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
    | bool => rfl
    | setOfInt => rfl

/-- The `pathArgs` decoder accepts exactly the same argument shapes. -/
private theorem pathArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (pathArgs vs).isSome = (pathArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e7 t0' =>
        cases e7 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e6 t0'' =>
            cases e6 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e5 t0''' =>
                cases e5 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e4 t0'''' =>
                    cases e4 with
                    | int =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e3 t0''''' =>
                        cases e3 with
                        | int =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e2 t0'''''' =>
                            cases e2 with
                            | @array nsA1 nsA1' hnsA1 =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e1 t0''''''' =>
                                cases e1 with
                                | @array esA1 esA1' hesA1 =>
                                  cases t0''''''' with
                                  | nil =>
                                    simp only [pathArgs]
                                    have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                    have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                    have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                                    have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                    cases hc_f1 : valueInts f1 with
                                    | none =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => rfl
                                      | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                    | some _ =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => simp [hc_f1, hc_f1'] at hx_f1
                                      | some _ =>
                                        cases hc_t1 : valueInts t1 with
                                        | none =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => rfl
                                          | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                        | some _ =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => simp [hc_t1, hc_t1'] at hx_t1
                                          | some _ =>
                                            cases hc_nsA1 : valueBools nsA1 with
                                            | none =>
                                              cases hc_nsA1' : valueBools nsA1' with
                                              | none => rfl
                                              | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                            | some _ =>
                                              cases hc_nsA1' : valueBools nsA1' with
                                              | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                              | some _ =>
                                                cases hc_esA1 : valueBools esA1 with
                                                | none =>
                                                  cases hc_esA1' : valueBools esA1' with
                                                  | none => rfl
                                                  | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                | some _ =>
                                                  cases hc_esA1' : valueBools esA1' with
                                                  | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                  | some _ =>
                                                    rfl
                                  | cons _ _ =>
                                    rfl
                                | bool => rfl
                                | int => rfl
                                | setOfInt => rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | setOfInt => rfl
                        | array => rfl
                    | bool => rfl
                    | setOfInt => rfl
                    | array => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | @array f2 f2' hf2 =>
      cases t0 with
      | nil => rfl
      | cons e5 t0' =>
        cases e5 with
        | @array t2 t2' ht2 =>
          cases t0' with
          | nil => rfl
          | cons e4 t0'' =>
            cases e4 with
            | int =>
              cases t0'' with
              | nil => rfl
              | cons e3 t0''' =>
                cases e3 with
                | int =>
                  cases t0''' with
                  | nil => rfl
                  | cons e2 t0'''' =>
                    cases e2 with
                    | @array nsA2 nsA2' hnsA2 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e1 t0''''' =>
                        cases e1 with
                        | @array esA2 esA2' hesA2 =>
                          cases t0''''' with
                          | nil =>
                            simp only [pathArgs]
                            have hx_f2 : (valueInts f2).isSome = (valueInts f2').isSome := valueInts_isSome_sameShape hf2
                            have hx_t2 : (valueInts t2).isSome = (valueInts t2').isSome := valueInts_isSome_sameShape ht2
                            have hx_nsA2 : (valueBools nsA2).isSome = (valueBools nsA2').isSome := valueBools_isSome_sameShape hnsA2
                            have hx_esA2 : (valueBools esA2).isSome = (valueBools esA2').isSome := valueBools_isSome_sameShape hesA2
                            cases hc_f2 : valueInts f2 with
                            | none =>
                              cases hc_f2' : valueInts f2' with
                              | none => rfl
                              | some _ => simp [hc_f2, hc_f2'] at hx_f2
                            | some _ =>
                              cases hc_f2' : valueInts f2' with
                              | none => simp [hc_f2, hc_f2'] at hx_f2
                              | some _ =>
                                cases hc_t2 : valueInts t2 with
                                | none =>
                                  cases hc_t2' : valueInts t2' with
                                  | none => rfl
                                  | some _ => simp [hc_t2, hc_t2'] at hx_t2
                                | some _ =>
                                  cases hc_t2' : valueInts t2' with
                                  | none => simp [hc_t2, hc_t2'] at hx_t2
                                  | some _ =>
                                    cases hc_nsA2 : valueBools nsA2 with
                                    | none =>
                                      cases hc_nsA2' : valueBools nsA2' with
                                      | none => rfl
                                      | some _ => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                    | some _ =>
                                      cases hc_nsA2' : valueBools nsA2' with
                                      | none => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                      | some _ =>
                                        cases hc_esA2 : valueBools esA2 with
                                        | none =>
                                          cases hc_esA2' : valueBools esA2' with
                                          | none => rfl
                                          | some _ => simp [hc_esA2, hc_esA2'] at hx_esA2
                                        | some _ =>
                                          cases hc_esA2' : valueBools esA2' with
                                          | none => simp [hc_esA2, hc_esA2'] at hx_esA2
                                          | some _ =>
                                            rfl
                          | cons _ _ =>
                            rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | setOfInt => rfl
                | array => rfl
            | bool => rfl
            | setOfInt => rfl
            | array => rfl
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
    | bool => rfl
    | setOfInt => rfl

/-- The `boundedPathArgs` decoder accepts exactly the same argument shapes. -/
private theorem boundedPathArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (boundedPathArgs vs).isSome = (boundedPathArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e9 t0' =>
        cases e9 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e8 t0'' =>
            cases e8 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e7 t0''' =>
                cases e7 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e6 t0'''' =>
                    cases e6 with
                    | @array wA1 wA1' hwA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e5 t0''''' =>
                        cases e5 with
                        | int =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e4 t0'''''' =>
                            cases e4 with
                            | int =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e3 t0''''''' =>
                                cases e3 with
                                | @array nsA1 nsA1' hnsA1 =>
                                  cases t0''''''' with
                                  | nil => rfl
                                  | cons e2 t0'''''''' =>
                                    cases e2 with
                                    | @array esA1 esA1' hesA1 =>
                                      cases t0'''''''' with
                                      | nil => rfl
                                      | cons e1 t0''''''''' =>
                                        cases e1 with
                                        | int =>
                                          cases t0''''''''' with
                                          | nil =>
                                            simp only [boundedPathArgs]
                                            have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                            have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                            have hx_wA1 : (valueInts wA1).isSome = (valueInts wA1').isSome := valueInts_isSome_sameShape hwA1
                                            have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                                            have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                            cases hc_f1 : valueInts f1 with
                                            | none =>
                                              cases hc_f1' : valueInts f1' with
                                              | none => rfl
                                              | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                            | some _ =>
                                              cases hc_f1' : valueInts f1' with
                                              | none => simp [hc_f1, hc_f1'] at hx_f1
                                              | some _ =>
                                                cases hc_t1 : valueInts t1 with
                                                | none =>
                                                  cases hc_t1' : valueInts t1' with
                                                  | none => rfl
                                                  | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                                | some _ =>
                                                  cases hc_t1' : valueInts t1' with
                                                  | none => simp [hc_t1, hc_t1'] at hx_t1
                                                  | some _ =>
                                                    cases hc_wA1 : valueInts wA1 with
                                                    | none =>
                                                      cases hc_wA1' : valueInts wA1' with
                                                      | none => rfl
                                                      | some _ => simp [hc_wA1, hc_wA1'] at hx_wA1
                                                    | some _ =>
                                                      cases hc_wA1' : valueInts wA1' with
                                                      | none => simp [hc_wA1, hc_wA1'] at hx_wA1
                                                      | some _ =>
                                                        cases hc_nsA1 : valueBools nsA1 with
                                                        | none =>
                                                          cases hc_nsA1' : valueBools nsA1' with
                                                          | none => rfl
                                                          | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                        | some _ =>
                                                          cases hc_nsA1' : valueBools nsA1' with
                                                          | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                          | some _ =>
                                                            cases hc_esA1 : valueBools esA1 with
                                                            | none =>
                                                              cases hc_esA1' : valueBools esA1' with
                                                              | none => rfl
                                                              | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                            | some _ =>
                                                              cases hc_esA1' : valueBools esA1' with
                                                              | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                              | some _ =>
                                                                rfl
                                          | cons _ _ =>
                                            rfl
                                        | bool => rfl
                                        | setOfInt => rfl
                                        | array => rfl
                                    | bool => rfl
                                    | int => rfl
                                    | setOfInt => rfl
                                | bool => rfl
                                | int => rfl
                                | setOfInt => rfl
                            | bool => rfl
                            | setOfInt => rfl
                            | array => rfl
                        | bool => rfl
                        | setOfInt => rfl
                        | array => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | @array f2 f2' hf2 =>
      cases t0 with
      | nil => rfl
      | cons e7 t0' =>
        cases e7 with
        | @array t2 t2' ht2 =>
          cases t0' with
          | nil => rfl
          | cons e6 t0'' =>
            cases e6 with
            | @array wA2 wA2' hwA2 =>
              cases t0'' with
              | nil => rfl
              | cons e5 t0''' =>
                cases e5 with
                | int =>
                  cases t0''' with
                  | nil => rfl
                  | cons e4 t0'''' =>
                    cases e4 with
                    | int =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e3 t0''''' =>
                        cases e3 with
                        | @array nsA2 nsA2' hnsA2 =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e2 t0'''''' =>
                            cases e2 with
                            | @array esA2 esA2' hesA2 =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e1 t0''''''' =>
                                cases e1 with
                                | int =>
                                  cases t0''''''' with
                                  | nil =>
                                    simp only [boundedPathArgs]
                                    have hx_f2 : (valueInts f2).isSome = (valueInts f2').isSome := valueInts_isSome_sameShape hf2
                                    have hx_t2 : (valueInts t2).isSome = (valueInts t2').isSome := valueInts_isSome_sameShape ht2
                                    have hx_wA2 : (valueInts wA2).isSome = (valueInts wA2').isSome := valueInts_isSome_sameShape hwA2
                                    have hx_nsA2 : (valueBools nsA2).isSome = (valueBools nsA2').isSome := valueBools_isSome_sameShape hnsA2
                                    have hx_esA2 : (valueBools esA2).isSome = (valueBools esA2').isSome := valueBools_isSome_sameShape hesA2
                                    cases hc_f2 : valueInts f2 with
                                    | none =>
                                      cases hc_f2' : valueInts f2' with
                                      | none => rfl
                                      | some _ => simp [hc_f2, hc_f2'] at hx_f2
                                    | some _ =>
                                      cases hc_f2' : valueInts f2' with
                                      | none => simp [hc_f2, hc_f2'] at hx_f2
                                      | some _ =>
                                        cases hc_t2 : valueInts t2 with
                                        | none =>
                                          cases hc_t2' : valueInts t2' with
                                          | none => rfl
                                          | some _ => simp [hc_t2, hc_t2'] at hx_t2
                                        | some _ =>
                                          cases hc_t2' : valueInts t2' with
                                          | none => simp [hc_t2, hc_t2'] at hx_t2
                                          | some _ =>
                                            cases hc_wA2 : valueInts wA2 with
                                            | none =>
                                              cases hc_wA2' : valueInts wA2' with
                                              | none => rfl
                                              | some _ => simp [hc_wA2, hc_wA2'] at hx_wA2
                                            | some _ =>
                                              cases hc_wA2' : valueInts wA2' with
                                              | none => simp [hc_wA2, hc_wA2'] at hx_wA2
                                              | some _ =>
                                                cases hc_nsA2 : valueBools nsA2 with
                                                | none =>
                                                  cases hc_nsA2' : valueBools nsA2' with
                                                  | none => rfl
                                                  | some _ => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                                | some _ =>
                                                  cases hc_nsA2' : valueBools nsA2' with
                                                  | none => simp [hc_nsA2, hc_nsA2'] at hx_nsA2
                                                  | some _ =>
                                                    cases hc_esA2 : valueBools esA2 with
                                                    | none =>
                                                      cases hc_esA2' : valueBools esA2' with
                                                      | none => rfl
                                                      | some _ => simp [hc_esA2, hc_esA2'] at hx_esA2
                                                    | some _ =>
                                                      cases hc_esA2' : valueBools esA2' with
                                                      | none => simp [hc_esA2, hc_esA2'] at hx_esA2
                                                      | some _ =>
                                                        rfl
                                  | cons _ _ =>
                                    rfl
                                | bool => rfl
                                | setOfInt => rfl
                                | array => rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | setOfInt => rfl
                    | array => rfl
                | bool => rfl
                | setOfInt => rfl
                | array => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | int => rfl
        | setOfInt => rfl
    | bool => rfl
    | setOfInt => rfl

/-- The `steinerArgs` decoder accepts exactly the same argument shapes. -/
private theorem steinerArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (steinerArgs vs).isSome = (steinerArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e7 t0' =>
        cases e7 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e6 t0'' =>
            cases e6 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e5 t0''' =>
                cases e5 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e4 t0'''' =>
                    cases e4 with
                    | @array wA1 wA1' hwA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e3 t0''''' =>
                        cases e3 with
                        | @array nsA1 nsA1' hnsA1 =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e2 t0'''''' =>
                            cases e2 with
                            | @array esA1 esA1' hesA1 =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e1 t0''''''' =>
                                cases e1 with
                                | int =>
                                  cases t0''''''' with
                                  | nil =>
                                    simp only [steinerArgs]
                                    have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                    have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                    have hx_wA1 : (valueInts wA1).isSome = (valueInts wA1').isSome := valueInts_isSome_sameShape hwA1
                                    have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                                    have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                    cases hc_f1 : valueInts f1 with
                                    | none =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => rfl
                                      | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                    | some _ =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => simp [hc_f1, hc_f1'] at hx_f1
                                      | some _ =>
                                        cases hc_t1 : valueInts t1 with
                                        | none =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => rfl
                                          | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                        | some _ =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => simp [hc_t1, hc_t1'] at hx_t1
                                          | some _ =>
                                            cases hc_wA1 : valueInts wA1 with
                                            | none =>
                                              cases hc_wA1' : valueInts wA1' with
                                              | none => rfl
                                              | some _ => simp [hc_wA1, hc_wA1'] at hx_wA1
                                            | some _ =>
                                              cases hc_wA1' : valueInts wA1' with
                                              | none => simp [hc_wA1, hc_wA1'] at hx_wA1
                                              | some _ =>
                                                cases hc_nsA1 : valueBools nsA1 with
                                                | none =>
                                                  cases hc_nsA1' : valueBools nsA1' with
                                                  | none => rfl
                                                  | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                | some _ =>
                                                  cases hc_nsA1' : valueBools nsA1' with
                                                  | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                  | some _ =>
                                                    cases hc_esA1 : valueBools esA1 with
                                                    | none =>
                                                      cases hc_esA1' : valueBools esA1' with
                                                      | none => rfl
                                                      | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                    | some _ =>
                                                      cases hc_esA1' : valueBools esA1' with
                                                      | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                      | some _ =>
                                                        rfl
                                  | cons _ _ =>
                                    rfl
                                | bool => rfl
                                | setOfInt => rfl
                                | array => rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | bool => rfl
    | setOfInt => rfl
    | array => rfl

/-- The `dsteinerArgs` decoder accepts exactly the same argument shapes. -/
private theorem dsteinerArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (dsteinerArgs vs).isSome = (dsteinerArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e8 t0' =>
        cases e8 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e7 t0'' =>
            cases e7 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e6 t0''' =>
                cases e6 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e5 t0'''' =>
                    cases e5 with
                    | @array wA1 wA1' hwA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e4 t0''''' =>
                        cases e4 with
                        | int =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e3 t0'''''' =>
                            cases e3 with
                            | @array nsA1 nsA1' hnsA1 =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e2 t0''''''' =>
                                cases e2 with
                                | @array esA1 esA1' hesA1 =>
                                  cases t0''''''' with
                                  | nil => rfl
                                  | cons e1 t0'''''''' =>
                                    cases e1 with
                                    | int =>
                                      cases t0'''''''' with
                                      | nil =>
                                        simp only [dsteinerArgs]
                                        have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                        have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                        have hx_wA1 : (valueInts wA1).isSome = (valueInts wA1').isSome := valueInts_isSome_sameShape hwA1
                                        have hx_nsA1 : (valueBools nsA1).isSome = (valueBools nsA1').isSome := valueBools_isSome_sameShape hnsA1
                                        have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                        cases hc_f1 : valueInts f1 with
                                        | none =>
                                          cases hc_f1' : valueInts f1' with
                                          | none => rfl
                                          | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                        | some _ =>
                                          cases hc_f1' : valueInts f1' with
                                          | none => simp [hc_f1, hc_f1'] at hx_f1
                                          | some _ =>
                                            cases hc_t1 : valueInts t1 with
                                            | none =>
                                              cases hc_t1' : valueInts t1' with
                                              | none => rfl
                                              | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                            | some _ =>
                                              cases hc_t1' : valueInts t1' with
                                              | none => simp [hc_t1, hc_t1'] at hx_t1
                                              | some _ =>
                                                cases hc_wA1 : valueInts wA1 with
                                                | none =>
                                                  cases hc_wA1' : valueInts wA1' with
                                                  | none => rfl
                                                  | some _ => simp [hc_wA1, hc_wA1'] at hx_wA1
                                                | some _ =>
                                                  cases hc_wA1' : valueInts wA1' with
                                                  | none => simp [hc_wA1, hc_wA1'] at hx_wA1
                                                  | some _ =>
                                                    cases hc_nsA1 : valueBools nsA1 with
                                                    | none =>
                                                      cases hc_nsA1' : valueBools nsA1' with
                                                      | none => rfl
                                                      | some _ => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                    | some _ =>
                                                      cases hc_nsA1' : valueBools nsA1' with
                                                      | none => simp [hc_nsA1, hc_nsA1'] at hx_nsA1
                                                      | some _ =>
                                                        cases hc_esA1 : valueBools esA1 with
                                                        | none =>
                                                          cases hc_esA1' : valueBools esA1' with
                                                          | none => rfl
                                                          | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                        | some _ =>
                                                          cases hc_esA1' : valueBools esA1' with
                                                          | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                          | some _ =>
                                                            rfl
                                      | cons _ _ =>
                                        rfl
                                    | bool => rfl
                                    | setOfInt => rfl
                                    | array => rfl
                                | bool => rfl
                                | int => rfl
                                | setOfInt => rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | setOfInt => rfl
                        | array => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | bool => rfl
    | setOfInt => rfl
    | array => rfl

/-- The `wstArgs` decoder accepts exactly the same argument shapes. -/
private theorem wstArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (wstArgs vs).isSome = (wstArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e6 t0' =>
        cases e6 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e5 t0'' =>
            cases e5 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e4 t0''' =>
                cases e4 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e3 t0'''' =>
                    cases e3 with
                    | @array wA1 wA1' hwA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e2 t0''''' =>
                        cases e2 with
                        | @array esA1 esA1' hesA1 =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e1 t0'''''' =>
                            cases e1 with
                            | int =>
                              cases t0'''''' with
                              | nil =>
                                simp only [wstArgs]
                                have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                have hx_wA1 : (valueInts wA1).isSome = (valueInts wA1').isSome := valueInts_isSome_sameShape hwA1
                                have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                cases hc_f1 : valueInts f1 with
                                | none =>
                                  cases hc_f1' : valueInts f1' with
                                  | none => rfl
                                  | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                | some _ =>
                                  cases hc_f1' : valueInts f1' with
                                  | none => simp [hc_f1, hc_f1'] at hx_f1
                                  | some _ =>
                                    cases hc_t1 : valueInts t1 with
                                    | none =>
                                      cases hc_t1' : valueInts t1' with
                                      | none => rfl
                                      | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                    | some _ =>
                                      cases hc_t1' : valueInts t1' with
                                      | none => simp [hc_t1, hc_t1'] at hx_t1
                                      | some _ =>
                                        cases hc_wA1 : valueInts wA1 with
                                        | none =>
                                          cases hc_wA1' : valueInts wA1' with
                                          | none => rfl
                                          | some _ => simp [hc_wA1, hc_wA1'] at hx_wA1
                                        | some _ =>
                                          cases hc_wA1' : valueInts wA1' with
                                          | none => simp [hc_wA1, hc_wA1'] at hx_wA1
                                          | some _ =>
                                            cases hc_esA1 : valueBools esA1 with
                                            | none =>
                                              cases hc_esA1' : valueBools esA1' with
                                              | none => rfl
                                              | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                            | some _ =>
                                              cases hc_esA1' : valueBools esA1' with
                                              | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                              | some _ =>
                                                rfl
                              | cons _ _ =>
                                rfl
                            | bool => rfl
                            | setOfInt => rfl
                            | array => rfl
                        | bool => rfl
                        | int => rfl
                        | setOfInt => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | bool => rfl
    | setOfInt => rfl
    | array => rfl

/-- The `dwstArgs` decoder accepts exactly the same argument shapes. -/
private theorem dwstArgs_isSome_agree_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    (dwstArgs vs).isSome = (dwstArgs ws).isSome := by
  cases h with
  | nil => rfl
  | cons e0 t0 =>
    cases e0 with
    | int =>
      cases t0 with
      | nil => rfl
      | cons e7 t0' =>
        cases e7 with
        | int =>
          cases t0' with
          | nil => rfl
          | cons e6 t0'' =>
            cases e6 with
            | @array f1 f1' hf1 =>
              cases t0'' with
              | nil => rfl
              | cons e5 t0''' =>
                cases e5 with
                | @array t1 t1' ht1 =>
                  cases t0''' with
                  | nil => rfl
                  | cons e4 t0'''' =>
                    cases e4 with
                    | @array wA1 wA1' hwA1 =>
                      cases t0'''' with
                      | nil => rfl
                      | cons e3 t0''''' =>
                        cases e3 with
                        | int =>
                          cases t0''''' with
                          | nil => rfl
                          | cons e2 t0'''''' =>
                            cases e2 with
                            | @array esA1 esA1' hesA1 =>
                              cases t0'''''' with
                              | nil => rfl
                              | cons e1 t0''''''' =>
                                cases e1 with
                                | int =>
                                  cases t0''''''' with
                                  | nil =>
                                    simp only [dwstArgs]
                                    have hx_f1 : (valueInts f1).isSome = (valueInts f1').isSome := valueInts_isSome_sameShape hf1
                                    have hx_t1 : (valueInts t1).isSome = (valueInts t1').isSome := valueInts_isSome_sameShape ht1
                                    have hx_wA1 : (valueInts wA1).isSome = (valueInts wA1').isSome := valueInts_isSome_sameShape hwA1
                                    have hx_esA1 : (valueBools esA1).isSome = (valueBools esA1').isSome := valueBools_isSome_sameShape hesA1
                                    cases hc_f1 : valueInts f1 with
                                    | none =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => rfl
                                      | some _ => simp [hc_f1, hc_f1'] at hx_f1
                                    | some _ =>
                                      cases hc_f1' : valueInts f1' with
                                      | none => simp [hc_f1, hc_f1'] at hx_f1
                                      | some _ =>
                                        cases hc_t1 : valueInts t1 with
                                        | none =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => rfl
                                          | some _ => simp [hc_t1, hc_t1'] at hx_t1
                                        | some _ =>
                                          cases hc_t1' : valueInts t1' with
                                          | none => simp [hc_t1, hc_t1'] at hx_t1
                                          | some _ =>
                                            cases hc_wA1 : valueInts wA1 with
                                            | none =>
                                              cases hc_wA1' : valueInts wA1' with
                                              | none => rfl
                                              | some _ => simp [hc_wA1, hc_wA1'] at hx_wA1
                                            | some _ =>
                                              cases hc_wA1' : valueInts wA1' with
                                              | none => simp [hc_wA1, hc_wA1'] at hx_wA1
                                              | some _ =>
                                                cases hc_esA1 : valueBools esA1 with
                                                | none =>
                                                  cases hc_esA1' : valueBools esA1' with
                                                  | none => rfl
                                                  | some _ => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                | some _ =>
                                                  cases hc_esA1' : valueBools esA1' with
                                                  | none => simp [hc_esA1, hc_esA1'] at hx_esA1
                                                  | some _ =>
                                                    rfl
                                  | cons _ _ =>
                                    rfl
                                | bool => rfl
                                | setOfInt => rfl
                                | array => rfl
                            | bool => rfl
                            | int => rfl
                            | setOfInt => rfl
                        | bool => rfl
                        | setOfInt => rfl
                        | array => rfl
                    | bool => rfl
                    | int => rfl
                    | setOfInt => rfl
                | bool => rfl
                | int => rfl
                | setOfInt => rfl
            | bool => rfl
            | int => rfl
            | setOfInt => rfl
        | bool => rfl
        | setOfInt => rfl
        | array => rfl
    | bool => rfl
    | setOfInt => rfl
    | array => rfl

/-- The `oneIntArray'` decoder accepts exactly the same argument shapes. -/
theorem oneIntArray'_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (oneIntArray' vs).isSome = (oneIntArray' ws).isSome :=
  oneIntArray'_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `subgraphArgs` decoder accepts exactly the same argument shapes. -/
theorem subgraphArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (subgraphArgs vs).isSome = (subgraphArgs ws).isSome :=
  subgraphArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `enumGraph4Args` decoder accepts exactly the same argument shapes. -/
theorem enumGraph4Args_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (enumGraph4Args vs).isSome = (enumGraph4Args ws).isSome :=
  enumGraph4Args_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `rootArgs` decoder accepts exactly the same argument shapes. -/
theorem rootArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (rootArgs vs).isSome = (rootArgs ws).isSome :=
  rootArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `pathArgs` decoder accepts exactly the same argument shapes. -/
theorem pathArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (pathArgs vs).isSome = (pathArgs ws).isSome :=
  pathArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `boundedPathArgs` decoder accepts exactly the same argument shapes. -/
theorem boundedPathArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (boundedPathArgs vs).isSome = (boundedPathArgs ws).isSome :=
  boundedPathArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `steinerArgs` decoder accepts exactly the same argument shapes. -/
theorem steinerArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (steinerArgs vs).isSome = (steinerArgs ws).isSome :=
  steinerArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `dsteinerArgs` decoder accepts exactly the same argument shapes. -/
theorem dsteinerArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (dsteinerArgs vs).isSome = (dsteinerArgs ws).isSome :=
  dsteinerArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `wstArgs` decoder accepts exactly the same argument shapes. -/
theorem wstArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (wstArgs vs).isSome = (wstArgs ws).isSome :=
  wstArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- The `dwstArgs` decoder accepts exactly the same argument shapes. -/
theorem dwstArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (dwstArgs vs).isSome = (dwstArgs ws).isSome :=
  dwstArgs_isSome_agree_sameShape (ArgsAgree.sameShape h)

/-- Boolean decodability gate of the `graph` family.  Neutral (`true`)
    outside the family. -/
def graphDecodes (n : String) (args : List Value) : Bool :=
  match n with
  | "fzn_circuit" => (oneIntArray' args).isSome
  | "fzn_subcircuit" => (oneIntArray' args).isSome
  | "fzn_subgraph" => (subgraphArgs args).isSome
  | "fzn_dag" => (enumGraph4Args args).isSome
  | "fzn_connected" => (enumGraph4Args args).isSome
  | "fzn_dconnected" => (enumGraph4Args args).isSome
  | "fzn_reachable" => (rootArgs args).isSome
  | "fzn_dreachable" => (rootArgs args).isSome
  | "fzn_tree" => (rootArgs args).isSome
  | "fzn_dtree" => (rootArgs args).isSome
  | "fzn_path" => (pathArgs args).isSome
  | "fzn_dpath" => (pathArgs args).isSome
  | "fzn_bounded_path" => (boundedPathArgs args).isSome
  | "fzn_bounded_dpath" => (boundedPathArgs args).isSome
  | "fzn_steiner" => (steinerArgs args).isSome
  | "fzn_dsteiner" => (dsteinerArgs args).isSome
  | "fzn_wst" => (wstArgs args).isSome
  | "fzn_dwst" => (dwstArgs args).isSome
  | _ => true

/-- The decodability gate is invariant under `ArgsAgree`. -/
theorem graphDecodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String) :
    graphDecodes n vs = graphDecodes n ws := by
  unfold graphDecodes
  split
  · exact oneIntArray'_isSome_agree h
  · exact oneIntArray'_isSome_agree h
  · exact subgraphArgs_isSome_agree h
  · exact enumGraph4Args_isSome_agree h
  · exact enumGraph4Args_isSome_agree h
  · exact enumGraph4Args_isSome_agree h
  · exact rootArgs_isSome_agree h
  · exact rootArgs_isSome_agree h
  · exact rootArgs_isSome_agree h
  · exact rootArgs_isSome_agree h
  · exact pathArgs_isSome_agree h
  · exact pathArgs_isSome_agree h
  · exact boundedPathArgs_isSome_agree h
  · exact boundedPathArgs_isSome_agree h
  · exact steinerArgs_isSome_agree h
  · exact dsteinerArgs_isSome_agree h
  · exact wstArgs_isSome_agree h
  · exact dwstArgs_isSome_agree h
  · rfl

end LeanFzn.Semantics.Globals.Graph

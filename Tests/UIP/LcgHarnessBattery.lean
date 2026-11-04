/-
File: Tests/UIP/LcgHarnessBattery.lean

Purpose (PLAN tasks E0/R0; TEST-ONLY, UNCERTIFIED): the FlatZinc source
generators, the built-in instance battery and the fuzz generator of the E0
harness, split out of `LcgHarnessRunner` (which defines `main`) so that the
R0 prototype runner (`Tests.UIP.LcgProtoRunner`) can reuse exactly the same
instances. No logic change.
-/

import Tests.UIP.LcgHarness
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open T1Oracle LcgHarness

namespace LcgHarness

/-! ## Source generators -/

def intVars (pre : String) (n lo hi : Nat) : String :=
  String.join ((List.range n).map fun i => s!"var {lo}..{hi}: {pre}{i};\n")

def neC (a b : String) : String := s!"constraint int_ne({a}, {b});\n"

/-- n pigeons, m holes, pairwise `int_ne`. UNSAT iff n > m. -/
def pigeon (n m : Nat) : String :=
  intVars "p" n 1 m ++
  String.join ((List.range n).flatMap fun i => ((List.range n).filter (· > i)).map
    fun j => neC s!"p{i}" s!"p{j}") ++ "solve satisfy;\n"

/-- n pigeons, m holes, one `all_different`. -/
def pigeonAD (n m : Nat) : String :=
  intVars "p" n 1 m ++
  s!"constraint all_different([{", ".intercalate ((List.range n).map fun i => s!"p{i}")}]);\n" ++
  "solve satisfy;\n"

/-- k-colouring of a graph given by an edge list over `n` vertices. -/
def coloring (n k : Nat) (edges : List (Nat × Nat)) : String :=
  intVars "c" n 1 k ++
  String.join (edges.map fun e => neC s!"c{e.1}" s!"c{e.2}") ++ "solve satisfy;\n"

def cycleEdges (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (i, (i + 1) % n)

def completeEdges (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (· > i)).map fun j => (i, j)

/-- Grotzsch graph (Mycielskian of C5): 11 vertices, 4-chromatic, triangle-free. -/
def grotzschEdges : List (Nat × Nat) :=
  -- C5 on 0..4, shadows 5..9 (shadow of i is 5+i), apex 10
  cycleEdges 5 ++
  (List.range 5).flatMap (fun i => [(i, 5 + (i + 1) % 5), (5 + i, (i + 1) % 5)]) ++
  (List.range 5).map (fun i => (5 + i, 10))

/-- Petersen graph, 3-colourable. -/
def petersenEdges : List (Nat × Nat) :=
  cycleEdges 5 ++ (List.range 5).map (fun i => (i, 5 + i)) ++
  (List.range 5).map (fun i => (5 + i, 5 + (i + 2) % 5))

/-- Deterministic pseudo-random graph (LCG) with `e` distinct edges. -/
def randomEdges (n e seed : Nat) : List (Nat × Nat) :=
  let rec go (fuel s : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        if acc.length ≥ e then acc else
        let s1 := (s * 1103515245 + 12345) % 2147483648
        let s2 := (s1 * 1103515245 + 12345) % 2147483648
        let a := (s1 / 16) % n
        let b := (s2 / 16) % n
        let lo := min a b
        let hi := max a b
        if lo == hi || acc.contains (lo, hi) then go fuel s2 acc
        else go fuel s2 ((lo, hi) :: acc)
  go (50 * e + 100) seed []

/-- chain `x0 < x1 < ... < x_{n-1}` over `1..d` plus `x_i /= x_{i+2}` (redundant). -/
def chainLt (n d : Nat) : String :=
  intVars "x" n 1 d ++
  String.join ((List.range (n - 1)).map fun i => s!"constraint int_lt(x{i}, x{i+1});\n") ++
  "solve satisfy;\n"

/-- `x_i <= x_{i+1}` chain closed by `x_{n-1} < x_0`: UNSAT (cyclic order). -/
def cycleLe (n d : Nat) : String :=
  intVars "x" n 1 d ++
  String.join ((List.range (n - 1)).map fun i => s!"constraint int_le(x{i}, x{i+1});\n") ++
  s!"constraint int_lt(x{n-1}, x0);\nsolve satisfy;\n"

/-- all-different of `n` vars over `0..d` with a linear lower bound `sum >= b`. -/
def sumAD (n d b : Nat) : String :=
  intVars "x" n 0 d ++
  s!"constraint all_different([{", ".intercalate ((List.range n).map fun i => s!"x{i}")}]);\n" ++
  s!"constraint int_lin_le([{", ".intercalate ((List.range n).map fun _ => "-1")}], [{", ".intercalate ((List.range n).map fun i => s!"x{i}")}], -{b});\n" ++
  "solve satisfy;\n"

/-- Latin-square-ish: an n x n grid over 1..n, rows and columns all_different,
with the first row pinned to be increasing via `int_lt` (symmetry), and `extra`
extra clue pins `x00 = 1`. -/
def latin (n : Nat) (pin : Bool) : String :=
  String.join ((List.range (n * n)).map fun i => s!"var 1..{n}: g{i};\n") ++
  String.join ((List.range n).map fun r =>
    s!"constraint all_different([{", ".intercalate ((List.range n).map fun c => s!"g{r * n + c}")}]);\n") ++
  String.join ((List.range n).map fun c =>
    s!"constraint all_different([{", ".intercalate ((List.range n).map fun r => s!"g{r * n + c}")}]);\n") ++
  (if pin then "constraint int_eq(g0, 1);\nconstraint int_lt(g0, g1);\n" else "") ++
  "solve satisfy;\n"

def srcPlus : String :=
  "var 1..6: x;\nvar 1..6: y;\nvar 1..6: z;\nconstraint int_plus(x, y, z);\n\
   constraint int_lt(x, y);\nconstraint int_ne(z, 3);\nconstraint int_ne(z, 4);\n\
   constraint int_ne(y, 2);\nsolve satisfy;\n"

def srcPlusUnsat : String :=
  "var 1..6: x;\nvar 1..6: y;\nvar 1..6: z;\nconstraint int_plus(x, y, z);\n\
   constraint int_lt(x, y);\nconstraint int_lt(y, z);\nconstraint int_ne(x, 1);\n\
   constraint int_ne(x, 2);\nconstraint int_le(z, 5);\nsolve satisfy;\n"

def srcBoolSat : String :=
  "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: d;\nvar bool: e;\n\
   constraint bool_and(a, b, c);\nconstraint bool_or(c, d, e);\n\
   constraint bool_not(e, a);\nconstraint bool_not(d, b);\nsolve satisfy;\n"

def srcBoolUnsat : String :=
  "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: d;\n\
   constraint bool_and(a, b, c);\nconstraint bool_not(c, d);\n\
   constraint bool_or(a, b, d);\nconstraint bool_not(a, b);\nsolve satisfy;\n"

/-- Mixed: ints guarded by bools through order; non-unit linear + ne. -/
def srcMixed : String :=
  "var 0..4: x;\nvar 0..4: y;\nvar 0..4: z;\nvar bool: p;\nvar bool: q;\n\
   constraint int_lin_le([1, 1, 1], [x, y, z], 5);\nconstraint int_lin_le([-1, -1, -1], [x, y, z], -5);\n\
   constraint int_ne(x, y);\nconstraint int_ne(y, z);\nconstraint int_le(x, z);\n\
   constraint bool_not(p, q);\nconstraint int_lt(x, 2);\nsolve satisfy;\n"


/-- Deterministic pseudo-random stream (LCG). -/
def lcgNext (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Random 3-SAT over `n` Boolean vars with `m` clauses, encoded with
`bool_not` (negated copies), `bool_or` (clause chains) and the pinned shape
`bool_or(x,y,true)`. Variables in a clause are distinct. -/
def sat3 (n m seed : Nat) : String :=
  let decls := String.join ((List.range n).map fun i => s!"var bool: x{i};\nvar bool: n{i};\n") ++
    String.join ((List.range m).map fun j => s!"var bool: t{j};\n")
  let nots := String.join ((List.range n).map fun i => s!"constraint bool_not(x{i}, n{i});\n")
  let rec clauses (k s : Nat) (acc : String) : String :=
    match k with
    | 0 => acc
    | k + 1 =>
        let s1 := lcgNext s
        let s2 := lcgNext s1
        let s3 := lcgNext s2
        let a := (s1 / 16) % n
        let b0 := (s2 / 16) % n
        let b := if b0 == a then (b0 + 1) % n else b0
        let c0 := (s3 / 16) % n
        let c1 := if c0 == a || c0 == b then (c0 + 1) % n else c0
        let c := if c1 == a || c1 == b then (c1 + 1) % n else c1
        let sg := lcgNext s3
        let lit (v bit : Nat) : String := if (sg / (2 ^ bit)) % 2 == 0 then s!"x{v}" else s!"n{v}"
        let t := s!"t{m - (k + 1)}"
        let body := s!"constraint bool_or({lit a 4}, {lit b 5}, {t});\nconstraint bool_or({t}, {lit c 6}, true);\n"
        clauses k sg (acc ++ body)
  decls ++ nots ++ clauses m seed "" ++ "solve satisfy;\n"

/-- Arithmetic chain: `x_{i} + x_{i+1} = s_i` with `s_i` bounded and the
chain closed, over `1..d`: arithmetic conflicts at positive levels. -/
def plusChain (n d cap : Nat) : String :=
  intVars "x" n 1 d ++
  String.join ((List.range (n - 1)).map fun i => s!"var 2..{2*d}: s{i};\n") ++
  String.join ((List.range (n - 1)).map fun i => s!"constraint int_plus(x{i}, x{i+1}, s{i});\n") ++
  String.join ((List.range (n - 1)).map fun i => s!"constraint int_le(s{i}, {cap});\n") ++
  String.join ((List.range (n - 1)).map fun i => s!"constraint int_ne(x{i}, x{i+1});\n") ++
  s!"constraint int_lin_le([-1, -1, -1], [x0, x1, x{n-1}], -{cap + 1});\n" ++
  "solve satisfy;\n"

/-- PLAN G1-B: dense `bool2int` channels. Every source is a free Boolean and
every target is a 0/1 view widened by `i % 3` (so 2 and 3 are unpinned
removals); the last channel's target is the raw singleton `[1]`, which pins
its source from the target side. Compiled through the source parser and run
by the LCG route with its oracle cross-check. -/
def bool2intChains (n : Nat) : String :=
  String.join ((List.range n).map fun i =>
    if i == n - 1 then s!"var bool: c{i};\nvar 1..1: t{i};\n"
    else s!"var bool: c{i};\nvar 0..{1 + i % 3}: t{i};\n") ++
  String.join ((List.range n).map fun i =>
    s!"constraint bool2int(c{i}, t{i});\n") ++
  "solve satisfy;\n"

/-- PLAN G1-B: a `bool2int` channel whose target cannot read 0 or 1
(`[2..2]`): both the channel propagator and the leaf check reject it. -/
def bool2intUnsat : String :=
  "var bool: cu;\nvar 2..2: tu;\nconstraint bool2int(cu, tu);\nsolve satisfy;\n"


/-- Random small CSP (FlatZinc text) from a seed: 3..6 int vars over small
domains (some negative), 3..9 constraints from the compiled fragment
(`int_ne/le/lt/plus/times/min/max/abs`, `int_lin_le`, `int_lin_eq`,
`int_lin_ne`, `int_le_reif`, `int_lin_le_reif` (PLAN L0c arms), `all_different`). -/
def fuzzSrc (seed : Nat) : String :=
  let r0 := lcgNext (seed * 7919 + 13)
  let nextR (s : Nat) : Nat × Nat := let t := lcgNext s; ((t / 16) % 1000003, t)
  let (a, r1) := nextR r0
  let n := 3 + a % 4
  let rec decls (k : Nat) (s : Nat) (acc : String) : String × Nat :=
    match k with
    | 0 => (acc, s)
    | k + 1 =>
        let (u, s1) := nextR s
        let (w, s2) := nextR s1
        let lo : Int := Int.ofNat (u % 4) - 2
        let hi : Int := lo + Int.ofNat (2 + w % 4)
        decls k s2 (acc ++ s!"var {lo}..{hi}: v{n - (k + 1)};\n")
  let (ds, r2) := decls n r1 ""
  let (b, r3) := nextR r2
  let m := 3 + b % 7
  let name (x : Nat) : String := s!"v{x % n}"
  let rec cons (k : Nat) (s : Nat) (acc : String) : String :=
    match k with
    | 0 => acc
    | k + 1 =>
        let (kind, s1) := nextR s
        let (i, s2) := nextR s1
        let (j, s3) := nextR s2
        let (l, s4) := nextR s3
        let (c1, s5) := nextR s4
        let (c2, s6) := nextR s5
        let (c3, s7) := nextR s6
        let (bb, s8) := nextR s7
        -- three DISTINCT variable indices (n >= 3)
        let i0 := i % n
        let j0 := (i0 + 1 + j % (n - 1)) % n
        let rest := (List.range n).filter fun x => x != i0 && x != j0
        let l0 := rest.getD (l % rest.length) 0
        let vi := name i0
        let vj := name j0
        let vl := name l0
        let cf (c : Nat) : Int := let x : Int := Int.ofNat (c % 5) - 2; if x == 0 then 3 else x
        -- PLAN L0c: the new propCheck families join the fuzz mix. The reified
        -- arms use the shared Boolean slot `bb` (declared before the
        -- constraints in the assembly below, since the parser requires all
        -- declarations first) and pin it through `bool_clause` (a seed-clause
        -- family), so the reification slot is forced and pinned-frame
        -- configurations exercise `propCheck`. `linNe`/`linLeReif` arms stay
        -- within the already-declared int vars.
        let line :=
          match kind % 13 with
          | 0 => s!"constraint int_ne({vi}, {vj});\n"
          | 1 => s!"constraint int_le({vi}, {vj});\n"
          | 2 => s!"constraint int_lt({vi}, {vj});\n"
          | 3 => s!"constraint int_plus({vi}, {vj}, {vl});\n"
          | 4 => s!"constraint int_lin_le([{cf c1}, {cf c2}, {cf c3}], [{vi}, {vj}, {vl}], {Int.ofNat (bb % 9) - 2});\n"
          | 5 => s!"constraint int_times({vi}, {vj}, {vl});\n"
          | 6 => s!"constraint int_min({vi}, {vj}, {vl});\n"
          | 7 => s!"constraint int_max({vi}, {vj}, {vl});\n"
          | 8 => s!"constraint int_lin_eq([{cf c1}, {cf c2}], [{vi}, {vj}], {Int.ofNat (bb % 7) - 2});\n"
          | 9 => s!"constraint int_lin_ne([{cf c1}, {cf c2}], [{vi}, {vj}], {Int.ofNat (bb % 7) - 2});\n"
          | 10 =>
              s!"constraint int_le_reif({vi}, {vj}, bb);\n" ++
                (if bb % 2 == 0 then "constraint bool_clause([bb], []);\n"
                 else "constraint bool_clause([], [bb]);\n")
          | 11 =>
              s!"constraint int_lin_le_reif([{cf c1}, {cf c2}], [{vi}, {vj}], {Int.ofNat (bb % 9) - 2}, bb);\n" ++
                (if c3 % 2 == 0 then "constraint bool_clause([bb], []);\n"
                 else "constraint bool_clause([], [bb]);\n")
          | _ => s!"constraint all_different([{vi}, {vj}, {vl}]);\n"
        cons k s8 (acc ++ line)
  let cs := cons m r3 ""
  -- The shared reification slot is declared only when an arm uses it (all
  -- declarations must precede the constraints).
  let boolDecl := if (cs.splitOn "bb").length > 1 then "var bool: bb;\n" else ""
  ds ++ boolDecl ++ cs ++ "solve satisfy;\n"

/-- The built-in battery: (source name, FlatZinc text). -/
def battery : List (String × String) :=
  [ ("pigeon-3-2", pigeon 3 2)
  , ("pigeon-4-3", pigeon 4 3)
  , ("pigeon-5-4", pigeon 5 4)
  , ("pigeon-6-5", pigeon 6 5)
  , ("pigeon-4-4-sat", pigeon 4 4)
  , ("pigeonAD-5-4", pigeonAD 5 4)
  , ("pigeonAD-6-5", pigeonAD 6 5)
  , ("odd-cycle-5-2col", coloring 5 2 (cycleEdges 5))
  , ("cycle-6-2col-sat", coloring 6 2 (cycleEdges 6))
  , ("K4-3col", coloring 4 3 (completeEdges 4))
  , ("K5-4col", coloring 5 4 (completeEdges 5))
  , ("K6-5col", coloring 6 5 (completeEdges 6))
  , ("petersen-3col-sat", coloring 10 3 petersenEdges)
  , ("grotzsch-3col", coloring 11 3 grotzschEdges)
  , ("grotzsch-4col-sat", coloring 11 4 grotzschEdges)
  , ("rand-12-3col", coloring 12 3 (randomEdges 12 30 7))
  , ("rand-16-3col", coloring 16 3 (randomEdges 16 42 11))
  , ("chain-lt-4-4-sat", chainLt 4 4)
  , ("chain-lt-5-4", chainLt 5 4)
  , ("chain-lt-8-8-sat", chainLt 8 8)
  , ("chain-lt-9-8", chainLt 9 8)
  , ("cycle-le-5", cycleLe 5 5)
  , ("sumAD-3-5-12-sat", sumAD 3 5 12)
  , ("sumAD-3-5-13", sumAD 3 5 13)
  , ("sumAD-5-6-20", sumAD 5 6 20)
  , ("plus-sat", srcPlus)
  , ("plus-unsat", srcPlusUnsat)
  , ("bool-sat", srcBoolSat)
  , ("bool-unsat", srcBoolUnsat)
  , ("mixed", srcMixed)
  , ("latin-3-pinned", latin 3 true)
  , ("latin-4", latin 4 false)
  , ("latin-4-pinned", latin 4 true)
  , ("sat3-8-30", sat3 8 30 1)
  , ("sat3-8-40", sat3 8 40 2)
  , ("sat3-10-43", sat3 10 43 3)
  , ("sat3-10-50", sat3 10 50 4)
  , ("sat3-12-52", sat3 12 52 5)
  , ("sat3-12-60", sat3 12 60 6)
  , ("sat3-14-60", sat3 14 60 7)
  , ("plusChain-5-6-7", plusChain 5 6 7)
  , ("plusChain-6-5-6", plusChain 6 5 6)
  , ("plusChain-6-6-8", plusChain 6 6 8)
  , ("bool2int-6chains", bool2intChains 6)
  , ("bool2int-unsat", bool2intUnsat) ]

/-- Extra heavier timing instances (run with `--heavy`). -/
def heavy : List (String × String) :=
  [ ("sat3-16-68", sat3 16 68 8)
  , ("sat3-20-86", sat3 20 86 9)
  , ("sat3-24-103", sat3 24 103 10)
  , ("pigeon-7-6", pigeon 7 6)
  , ("pigeon-8-7", pigeon 8 7)
  , ("pigeonAD-8-7", pigeonAD 8 7)
  , ("rand-20-3col", coloring 20 3 (randomEdges 20 52 3))
  , ("rand-25-3col", coloring 25 3 (randomEdges 25 62 5))
  , ("latin-5", latin 5 false)
  , ("K7-6col", coloring 7 6 (completeEdges 7)) ]

end LcgHarness

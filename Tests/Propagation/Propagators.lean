import LeanFzn.Solver.Propagation.DomainConstraints
import LeanFzn.Compiler.Extract
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Compiler


/-!
# Propagator tests

Unit tests for the propagation contract and the propagators of
`LeanFzn.Solver/Propagators.lean`:

* `DomConstraint.satisfiedB` agreement spot checks (the Boolean twin
  vs the declarative semantics on accepting and rejecting shapes);
* narrowing correctness of each propagator on small domains
  (`propEqSlot` intersects, `propNeSlot` removes a singleton value,
  `propLeSlot` bounds by the domain extrema, `LeanFzn.Solver.Propagation.DomainFiltering.propConstEq` pins,
  `propPlusSlot` narrows each slot to its implied interval,
  `LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi` / `LeanFzn.Solver.Propagation.DomainFiltering.propLeConstLo` bound by the constant);
* contradiction detection (empty intersection, empty remainder, no
  orderable integers, absent constant, emptied plus interval,
  crossed plus bounds, emptied constant bound, all-different
  pigeonhole);
* preservation sanity: a known-satisfying assignment survives the
  narrowing (checked through the spec `allAssigns_spec` / intro
  `allAssigns_intro` pair, i.e. exactly the theorem obligations), and
  the slot-count invariant of narrowing;
* extraction (`LeanFzn.Solver/Extract.lean`): the recognized argument shapes
  map to the expected `DomConstraint`s and the unsupported shapes
  are skipped.

The end-to-end `solveModelProp` sections were retired with the
legacy LeanFzn.Solver stack (PLAN.md §1); the propagators themselves stay
exercised here, and the LCG engine drives them in `tests_lcg`.
-/

open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver

/-- A mutable failure flag with a counted check helper (the style of
    `LeanFzn.Solver/Tests.lean`). -/
structure TestState where
  passed : Nat
  failed : Nat

def TestState.check (st : TestState) (name : String) (ok : Bool) : IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def vi (i : Int) : Value := .int i

/-- Structural equality of extracted slot constraints (for testing;
    the positions, constants, and slot lists must match exactly). -/
def domConstraintEq (a b : DomConstraint) : Bool :=
  match a, b with
  | .eqSlot i j, .eqSlot i' j' => i == i' && j == j'
  | .neSlot i j, .neSlot i' j' => i == i' && j == j'
  | .leSlot i j, .leSlot i' j' => i == i' && j == j'
  | .constEq i v, .constEq i' v' => i == i' && v.eqB v'
  | .plusSlot i j k, .plusSlot i' j' k' => i == i' && j == j' && k == k'
  | .leConstHi i c, .leConstHi i' c' => i == i' && c == c'
  | .leConstLo i c, .leConstLo i' c' => i == i' && c == c'
  | .allDiff is, .allDiff is' =>
      is.length == is'.length && (is.zip is').all (fun p => p.1 == p.2)
  | .timesSlot i j k, .timesSlot i' j' k' => i == i' && j == j' && k == k'
  | .minSlot i j k, .minSlot i' j' k' => i == i' && j == j' && k == k'
  | .maxSlot i j k, .maxSlot i' j' k' => i == i' && j == j' && k == k'
  | .absSlot i k, .absSlot i' k' => i == i' && k == k'
  | .linEq coeffs is b, .linEq coeffs' is' b' =>
      coeffs.length == coeffs'.length && b == b' &&
        (coeffs.zip coeffs').all (fun p => p.1 == p.2) &&
        (is.zip is').all (fun p => p.1 == p.2)
  | .linLe coeffs is b, .linLe coeffs' is' b' =>
      coeffs.length == coeffs'.length && b == b' &&
        (coeffs.zip coeffs').all (fun p => p.1 == p.2) &&
        (is.zip is').all (fun p => p.1 == p.2)
  | .ltSlot i j, .ltSlot i' j' => i == i' && j == j'
  | .ltConstHi i c, .ltConstHi i' c' => i == i' && c == c'
  | .ltConstLo i c, .ltConstLo i' c' => i == i' && c == c'
  | .boolNotSlot i j, .boolNotSlot i' j' => i == i' && j == j'
  | .boolAndSlot i j k, .boolAndSlot i' j' k' =>
      i == i' && j == j' && k == k'
  | .boolOrSlot i j k, .boolOrSlot i' j' k' =>
      i == i' && j == j' && k == k'
  | _, _ => false

/-- List equality of extracted constraints (for testing). -/
def domConstraintsEq (a b : List DomConstraint) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => domConstraintEq p.1 p.2)

/-- Decidable-equality helper on domain lists (a simple structural
    equality up to `Value` equality — domains are small in the
    tests). -/
def domEq (a b : List (List Value)) : Bool :=
  a.length == b.length &&
    (a.zip b).all (fun p => valuesEqB p.1 p.2)

/-- Every value of `doms'` lies in the corresponding slot of `doms`
    and the slot counts agree — the shrinking half of the contract,
    as a Boolean test (mirrors `DomPointwiseSub`). -/
def pointwiseSub (doms' doms : List (List Value)) : Bool :=
  doms'.length == doms.length &&
    (doms'.zip doms).all (fun p => p.1.all (fun v => p.2.any (fun u => u.eqB v)))

/-- A satisfying assignment is still an assignment of the narrowed
    domains — the preservation half of the contract, as a Boolean
    test (mirrors the `allAssigns_spec`/`allAssigns_intro` theorem
    pair). -/
def survives (a : List Value) (doms' : List (List Value)) : Bool :=
  a.length == doms'.length &&
    (a.zip doms').all (fun p => p.2.any (fun u => u.eqB p.1))

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## satisfiedB agreement (spot checks)

  st ← st.check "satisfiedB: eqSlot accepting"
    (DomConstraint.satisfiedB (.eqSlot 0 1) [vi 3, vi 3])
  st ← st.check "satisfiedB: eqSlot rejecting"
    (!DomConstraint.satisfiedB (.eqSlot 0 1) [vi 3, vi 4])
  st ← st.check "satisfiedB: neSlot accepting"
    (DomConstraint.satisfiedB (.neSlot 0 1) [vi 3, vi 4])
  st ← st.check "satisfiedB: neSlot rejecting"
    (!DomConstraint.satisfiedB (.neSlot 0 1) [vi 3, vi 3])
  st ← st.check "satisfiedB: leSlot accepting"
    (DomConstraint.satisfiedB (.leSlot 0 1) [vi 2, vi 5])
  st ← st.check "satisfiedB: leSlot rejecting (order)"
    (!DomConstraint.satisfiedB (.leSlot 0 1) [vi 5, vi 2])
  st ← st.check "satisfiedB: leSlot rejecting (non-integer)"
    (!DomConstraint.satisfiedB (.leSlot 0 1) [Value.bool true, vi 2])
  st ← st.check "satisfiedB: constEq accepting"
    (DomConstraint.satisfiedB (.constEq 0 (vi 7)) [vi 7])
  st ← st.check "satisfiedB: constEq rejecting"
    (!DomConstraint.satisfiedB (.constEq 0 (vi 7)) [vi 8])
  st ← st.check "satisfiedB: eqSlot out-of-range"
    (!DomConstraint.satisfiedB (.eqSlot 0 5) [vi 3])

  -- ## propEqSlot: narrowing

  -- [1,2,3] vs [2,3,4]: both narrow to [2,3]
  st ← st.check "eq: narrows to intersection"
    (propEqSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] ==
      .narrowed [[vi 2, vi 3], [vi 2, vi 3]])
  -- disjoint: contradiction
  st ← st.check "eq: contradiction on empty intersection"
    (propEqSlot 0 1 [[vi 1, vi 2], [vi 3, vi 4]] == .contradiction)
  -- untouched slots stay; slot count preserved
  st ← st.check "eq: other slots untouched"
    (propEqSlot 1 2 [[vi 9], [vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] ==
      .narrowed [[vi 9], [vi 2, vi 3], [vi 2, vi 3]])
  -- preservation sanity: the satisfying (2,2) survives
  st ← st.check "eq: satisfying assignment survives"
    (match propEqSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] with
      | .narrowed d => survives [vi 2, vi 2] d
      | .contradiction => false)
  -- shrinking sanity
  st ← st.check "eq: narrowed domains pointwise-subset"
    (match propEqSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] with
      | .narrowed d => pointwiseSub d [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]]
      | .contradiction => false)
  -- boolean domains: equality channeling works the same
  st ← st.check "eq: bool slots"
    (propEqSlot 0 1 [[Value.bool true, Value.bool false],
      [Value.bool false, Value.bool true]] ==
      .narrowed [[Value.bool true, Value.bool false],
        [Value.bool false, Value.bool true]])

  -- ## propNeSlot: narrowing

  -- second domain a singleton: its value is removed from the first
  st ← st.check "ne: removes singleton value"
    (propNeSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2]] ==
      .narrowed [[vi 1, vi 3], [vi 2]])
  -- symmetric: first domain singleton, second narrowed
  st ← st.check "ne: symmetric singleton removal"
    (propNeSlot 0 1 [[vi 2], [vi 1, vi 2, vi 3]] ==
      .narrowed [[vi 2], [vi 1, vi 3]])
  -- first domain singleton {2}, second is only {2}: contradiction
  st ← st.check "ne: contradiction on forced equality"
    (propNeSlot 0 1 [[vi 2], [vi 2]] == .contradiction)
  -- neither a singleton: unchanged
  st ← st.check "ne: no singleton, unchanged"
    (propNeSlot 0 1 [[vi 1, vi 2], [vi 1, vi 2]] ==
      .narrowed [[vi 1, vi 2], [vi 1, vi 2]])
  -- preservation sanity: a differing assignment survives
  st ← st.check "ne: differing assignment survives"
    (match propNeSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2]] with
      | .narrowed d => survives [vi 1, vi 2] d
      | .contradiction => false)
  -- shrinking sanity
  st ← st.check "ne: narrowed domains pointwise-subset"
    (match propNeSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2]] with
      | .narrowed d => pointwiseSub d [[vi 1, vi 2, vi 3], [vi 2]]
      | .contradiction => false)

  -- ## propLeSlot: narrowing

  -- [1,2,3] ≤ [2,3,4]: left keeps ≤ 4 (all), right keeps ≥ 1 (all)
  st ← st.check "le: no prune when bounds allow everything"
    (propLeSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] ==
      .narrowed [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]])
  -- [3,4,5] ≤ [1,2,3]: left keeps ≤ 3 → [3], right keeps ≥ 3 → [3]
  st ← st.check "le: prunes both sides"
    (propLeSlot 0 1 [[vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3]] ==
      .narrowed [[vi 3], [vi 3]])
  -- [4,5] ≤ [1,2]: left keeps ≤ 2 → empty: contradiction
  st ← st.check "le: contradiction on crossed domains"
    (propLeSlot 0 1 [[vi 4, vi 5], [vi 1, vi 2]] == .contradiction)
  -- non-integer domain: no orderable integers, contradiction
  st ← st.check "le: contradiction without integers"
    (propLeSlot 0 1 [[Value.bool true], [vi 1, vi 2]] == .contradiction)
  -- untouched slot stays (indices are 1 and 2 here)
  st ← st.check "le: other slots untouched"
    (propLeSlot 1 2 [[vi 9], [vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3]] ==
      .narrowed [[vi 9], [vi 3], [vi 3]])
  -- preservation sanity: an ordered assignment survives
  st ← st.check "le: ordered assignment survives"
    (match propLeSlot 0 1 [[vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3]] with
      | .narrowed d => survives [vi 3, vi 3] d
      | .contradiction => false)
  -- shrinking sanity
  st ← st.check "le: narrowed domains pointwise-subset"
    (match propLeSlot 0 1 [[vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3]] with
      | .narrowed d => pointwiseSub d [[vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3]]
      | .contradiction => false)

  -- ## LeanFzn.Solver.Propagation.DomainFiltering.propConstEq: narrowing

  -- constant present: domain becomes the constant
  st ← st.check "const: pins to the constant"
    (LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 0 (vi 2) [[vi 1, vi 2, vi 3]] == .narrowed [[vi 2]])
  -- constant absent: contradiction
  st ← st.check "const: contradiction when absent"
    (LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 0 (vi 7) [[vi 1, vi 2, vi 3]] == .contradiction)
  -- other slots stay; slot count preserved
  st ← st.check "const: other slots untouched"
    (LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 1 (vi 2) [[vi 9], [vi 1, vi 2, vi 3]] ==
      .narrowed [[vi 9], [vi 2]])
  -- bool constant
  st ← st.check "const: bool constant"
    (LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 0 (Value.bool true) [VarDomain.boolDom.values] ==
      .narrowed [[Value.bool true]])
  -- preservation sanity: the pinned assignment survives
  st ← st.check "const: pinned assignment survives"
    (match LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 0 (vi 2) [[vi 1, vi 2, vi 3]] with
      | .narrowed d => survives [vi 2] d
      | .contradiction => false)
  -- shrinking sanity
  st ← st.check "const: narrowed domains pointwise-subset"
    (match LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 0 (vi 2) [[vi 1, vi 2, vi 3]] with
      | .narrowed d => pointwiseSub d [[vi 1, vi 2, vi 3]]
      | .contradiction => false)

  -- ## out-of-range indices (defensive shape): an out-of-range slot
  -- has the empty domain, so equality with it is unsatisfiable
  st ← st.check "eq: out-of-range slot contradicts"
    (propEqSlot 0 9 [[vi 1, vi 2]] == .contradiction)
  st ← st.check "const: out-of-range slot contradicts"
    (LeanFzn.Solver.Propagation.DomainFiltering.propConstEq 9 (vi 1) [[vi 1, vi 2]] == .contradiction)

  -- ## fixed-point style composition (two propagators in sequence)

  -- x = y with [1,2,3]/[2,3,4] then x ≠ 2 (via constEq x 2 failing
  -- would be a contradiction — instead propagate y ≤ 3)
  st ← st.check "compose: eq then le"
    (match propEqSlot 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]] with
      | .narrowed d =>
          propLeSlot 0 1 d == .narrowed [[vi 2, vi 3], [vi 2, vi 3]]
      | .contradiction => false)

  -- ## propPlusSlot: bounds propagation for x + y = z

  -- x,y in 1..5, z in 3..4: x and y narrow to [1,3] (p ≤ 4-1 and
  -- p ≥ 3-5 is trivial), z stays [3,4]
  st ← st.check "plus: narrows both addends"
    (propPlusSlot 0 1 2
      [[vi 1, vi 2, vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3, vi 4, vi 5],
       [vi 3, vi 4]] ==
      .narrowed [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3], [vi 3, vi 4]])
  -- x in 5..6, y in 1..2, z in 1..3: x's interval [1-2, 3-1] misses
  -- [5,6] entirely: contradiction
  st ← st.check "plus: contradiction on crossed bounds"
    (propPlusSlot 0 1 2 [[vi 5, vi 6], [vi 1, vi 2], [vi 1, vi 2, vi 3]] ==
      .contradiction)
  -- a domain without integers: contradiction
  st ← st.check "plus: contradiction without integers"
    (propPlusSlot 0 1 2 [[Value.bool true], [vi 1, vi 2], [vi 1, vi 2]] ==
      .contradiction)
  -- x in 1..3, y fixed 2, z in 3..5: z narrows to [3,5] via
  -- [1+2, 3+2] — no change; x narrows to [1,3]∩[1,3] — no change
  st ← st.check "plus: stable when bounds allow everything"
    (propPlusSlot 0 1 2 [[vi 1, vi 2, vi 3], [vi 2], [vi 3, vi 4, vi 5]] ==
      .narrowed [[vi 1, vi 2, vi 3], [vi 2], [vi 3, vi 4, vi 5]])
  -- preservation sanity: the satisfying (2, 1, 3) survives
  st ← st.check "plus: satisfying assignment survives"
    (match propPlusSlot 0 1 2
        [[vi 1, vi 2, vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3, vi 4, vi 5],
         [vi 3, vi 4]] with
      | .narrowed d => survives [vi 2, vi 1, vi 3] d
      | .contradiction => false)
  -- shrinking sanity
  st ← st.check "plus: narrowed domains pointwise-subset"
    (match propPlusSlot 0 1 2
        [[vi 1, vi 2, vi 3, vi 4, vi 5], [vi 1, vi 2, vi 3, vi 4, vi 5],
         [vi 3, vi 4]] with
      | .narrowed d =>
          pointwiseSub d [[vi 1, vi 2, vi 3, vi 4, vi 5],
            [vi 1, vi 2, vi 3, vi 4, vi 5], [vi 3, vi 4]]
      | .contradiction => false)
  -- coinciding slots: x + x = z on 1..3 and 2..6 narrows soundly
  st ← st.check "plus: coinciding addend slots"
    (match propPlusSlot 0 0 1 [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4, vi 5, vi 6]] with
      | .narrowed d => survives [vi 2, vi 4] d
      | .contradiction => false)

  -- ## LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi / LeanFzn.Solver.Propagation.DomainFiltering.propLeConstLo: constant bounds

  -- x in 1..5 with x ≤ 3: narrows to [1,3]
  st ← st.check "leConstHi: keeps values at most the constant"
    (LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi 0 3 [[vi 1, vi 2, vi 3, vi 4, vi 5]] ==
      .narrowed [[vi 1, vi 2, vi 3]])
  -- x in 1..5 with x ≤ 0: empties: contradiction
  st ← st.check "leConstHi: contradiction when emptied"
    (LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi 0 0 [[vi 1, vi 2, vi 3]] == .contradiction)
  -- x in 1..5 with 2 ≤ x: narrows to [2,5]
  st ← st.check "leConstLo: keeps values at least the constant"
    (LeanFzn.Solver.Propagation.DomainFiltering.propLeConstLo 0 2 [[vi 1, vi 2, vi 3, vi 4, vi 5]] ==
      .narrowed [[vi 2, vi 3, vi 4, vi 5]])
  -- x in 1..5 with 6 ≤ x: empties: contradiction
  st ← st.check "leConstLo: contradiction when emptied"
    (LeanFzn.Solver.Propagation.DomainFiltering.propLeConstLo 0 6 [[vi 1, vi 2, vi 3]] == .contradiction)
  -- non-integer domain: the bound empties it: contradiction
  st ← st.check "leConstHi: bool domain contradicts"
    (LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi 0 1 [[Value.bool true, Value.bool false]] == .contradiction)
  -- preservation sanity
  st ← st.check "leConstHi: bounded assignment survives"
    (match LeanFzn.Solver.Propagation.DomainFiltering.propLeConstHi 0 3 [[vi 1, vi 2, vi 3, vi 4, vi 5]] with
      | .narrowed d => survives [vi 2] d
      | .contradiction => false)
  st ← st.check "leConstLo: bounded assignment survives"
    (match LeanFzn.Solver.Propagation.DomainFiltering.propLeConstLo 0 2 [[vi 1, vi 2, vi 3, vi 4, vi 5]] with
      | .narrowed d => survives [vi 4] d
      | .contradiction => false)

  -- ## propAllDiff: pigeonhole counting

  -- three slots over two values: 3 > 2: contradiction
  st ← st.check "allDiff: pigeonhole contradiction"
    (propAllDiff [0, 1, 2] [[vi 1, vi 2], [vi 1, vi 2], [vi 1, vi 2]] ==
      .contradiction)
  -- three slots over three values: no contradiction, unchanged
  st ← st.check "allDiff: enough values, unchanged"
    (propAllDiff [0, 1, 2] [[vi 1, vi 2, vi 3], [vi 1, vi 2], [vi 2, vi 3]] ==
      .narrowed [[vi 1, vi 2, vi 3], [vi 1, vi 2], [vi 2, vi 3]])
  -- a repeated slot can never read two distinct values: union of
  -- {1,2} has 2 distinct values < 3 slots: contradiction
  st ← st.check "allDiff: repeated slot contradicts"
    (propAllDiff [0, 1, 0] [[vi 1, vi 2], [vi 1, vi 2]] == .contradiction)
  -- one slot: trivially pairwise distinct: unchanged
  st ← st.check "allDiff: single slot unchanged"
    (propAllDiff [0] [[vi 1, vi 2]] == .narrowed [[vi 1, vi 2]])
  -- out-of-range slots read no values, so they do not count toward
  -- the pigeonhole (soundness edge: [0, 5] on a one-slot model is
  -- satisfiable by any single value — the read at 5 is absent)
  st ← st.check "allDiff: out-of-range slot does not count"
    (propAllDiff [0, 5] [[vi 1]] == .narrowed [[vi 1]])
  -- distinct-union counting uses deduplication: domains [1,1,2] and
  -- [2,3]: union {1,2,3} has 3 values for 2 slots: no contradiction
  st ← st.check "allDiff: union counts distinct values"
    (propAllDiff [0, 1] [[vi 1, vi 1, vi 2], [vi 2, vi 3]] ==
      .narrowed [[vi 1, vi 1, vi 2], [vi 2, vi 3]])
  -- preservation sanity: an all-distinct assignment survives (no
  -- contradiction path fires)
  st ← st.check "allDiff: distinct assignment survives"
    (match propAllDiff [0, 1, 2] [[vi 1, vi 2, vi 3], [vi 1, vi 2], [vi 2, vi 3]] with
      | .narrowed d => survives [vi 1, vi 2, vi 3] d
      | .contradiction => false)

  -- ## satisfiedB agreement for the new constructors

  st ← st.check "satisfiedB: plusSlot accepting"
    (DomConstraint.satisfiedB (.plusSlot 0 1 2) [vi 2, vi 3, vi 5])
  st ← st.check "satisfiedB: plusSlot rejecting"
    (!DomConstraint.satisfiedB (.plusSlot 0 1 2) [vi 2, vi 3, vi 6])
  st ← st.check "satisfiedB: leConstHi accepting"
    (DomConstraint.satisfiedB (.leConstHi 0 3) [vi 3])
  st ← st.check "satisfiedB: leConstHi rejecting"
    (!DomConstraint.satisfiedB (.leConstHi 0 3) [vi 4])
  st ← st.check "satisfiedB: leConstLo accepting"
    (DomConstraint.satisfiedB (.leConstLo 0 3) [vi 3])
  st ← st.check "satisfiedB: leConstLo rejecting"
    (!DomConstraint.satisfiedB (.leConstLo 0 3) [vi 2])
  st ← st.check "satisfiedB: allDiff accepting"
    (DomConstraint.satisfiedB (.allDiff [0, 1, 2]) [vi 1, vi 2, vi 3])
  st ← st.check "satisfiedB: allDiff rejecting"
    (!DomConstraint.satisfiedB (.allDiff [0, 1, 2]) [vi 1, vi 2, vi 2])

  -- ## extraction of the new shapes (LeanFzn.Solver/Extract.lean)

  -- helpers to parse and extract
  let parse (src : String) : LeanFzn.Model :=
    match LeanFzn.Parser.parseModel src with
    | .ok m => m
    | .error e => panic! s!"unexpected parse error: {e}"
  let extractsTo (m : LeanFzn.Model) (expected : List DomConstraint) : Bool :=
    match extractConstraints m with
    | .ok cs => domConstraintsEq cs expected
    | .error _ => false
  -- int_plus on three slots
  st ← st.check "extract: int_plus on three slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
       constraint int_plus(x, y, z);\nsolve satisfy;") [.plusSlot 0 1 2])
  -- int_plus with a literal argument: not extracted (TODO shape)
  st ← st.check "extract: int_plus with literal skipped"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_plus(x, y, 5);\nsolve satisfy;") [])
  -- int_le against a constant, both directions
  st ← st.check "extract: int_le(x, c) is leConstHi"
    (extractsTo (parse "var 1..3: x;\nconstraint int_le(x, 2);\nsolve satisfy;") [.leConstHi 0 2])
  st ← st.check "extract: int_le(c, x) is leConstLo"
    (extractsTo (parse "var 1..3: x;\nconstraint int_le(2, x);\nsolve satisfy;") [.leConstLo 0 2])
  -- int_le between two slots still works
  st ← st.check "extract: int_le(x, y) still leSlot"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_le(x, y);\nsolve satisfy;") [.leSlot 0 1])
  -- all_different over an explicit array of slots
  st ← st.check "extract: all_different array of slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
       constraint all_different([x, y, z]);\nsolve satisfy;")
      [.allDiff [0, 1, 2]])
  -- all_different with a non-slot element: not extracted
  st ← st.check "extract: all_different with literal skipped"
    (extractsTo (parse "var 1..3: x;\n\
       constraint all_different([x, 2]);\nsolve satisfy;") [])
  -- all_different over an array variable: not extracted (search
  -- slots are only scalars)
  st ← st.check "extract: all_different over array variable skipped"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       array [1..2] of var 1..3: xs = [x, y];\n\
       constraint all_different(xs);\nsolve satisfy;") [])
  -- the global fzn_all_different_int name is not extracted (only
  -- the stdlib all_different shape is)
  st ← st.check "extract: fzn_all_different_int skipped"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint fzn_all_different_int([x, y]);\nsolve satisfy;") [])
  -- the new propagator-extension shapes
  st ← st.check "extract: int_times on three slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\nvar 1..9: z;\n\
       constraint int_times(x, y, z);\nsolve satisfy;") [.timesSlot 0 1 2])
  st ← st.check "extract: int_min on three slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
       constraint int_min(x, y, z);\nsolve satisfy;") [.minSlot 0 1 2])
  st ← st.check "extract: int_max on three slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
       constraint int_max(x, y, z);\nsolve satisfy;") [.maxSlot 0 1 2])
  st ← st.check "extract: int_abs on two slots"
    (extractsTo (parse "var -3..3: x;\nvar 0..3: y;\n\
       constraint int_abs(x, y);\nsolve satisfy;") [.absSlot 0 1])
  st ← st.check "extract: int_lt on two slots"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_lt(x, y);\nsolve satisfy;") [.ltSlot 0 1])
  st ← st.check "extract: int_lt(x, c) is ltConstHi"
    (extractsTo (parse "var 1..3: x;\nconstraint int_lt(x, 2);\nsolve satisfy;")
      [.ltConstHi 0 2])
  st ← st.check "extract: int_lt(c, x) is ltConstLo"
    (extractsTo (parse "var 1..3: x;\nconstraint int_lt(2, x);\nsolve satisfy;")
      [.ltConstLo 0 2])
  st ← st.check "extract: bool_not on two slots"
    (extractsTo (parse "var bool: p;\nvar bool: q;\n\
       constraint bool_not(p, q);\nsolve satisfy;") [.boolNotSlot 0 1])
  st ← st.check "extract: bool_and on three slots"
    (extractsTo (parse "var bool: p;\nvar bool: q;\nvar bool: r;\n\
       constraint bool_and(p, q, r);\nsolve satisfy;") [.boolAndSlot 0 1 2])
  st ← st.check "extract: bool_or on three slots"
    (extractsTo (parse "var bool: p;\nvar bool: q;\nvar bool: r;\n\
       constraint bool_or(p, q, r);\nsolve satisfy;") [.boolOrSlot 0 1 2])
  -- int_lin_eq / int_lin_le extraction
  st ← st.check "extract: int_lin_eq arrays"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_lin_eq([1, 2], [x, y], 5);\nsolve satisfy;")
      [.linEq [1, 2] [0, 1] 5])
  st ← st.check "extract: int_lin_le arrays"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_lin_le([1, 2], [x, y], 5);\nsolve satisfy;")
      [.linLe [1, 2] [0, 1] 5])
  -- int_lin with mismatched array lengths: not extracted
  st ← st.check "extract: int_lin_eq length mismatch skipped"
    (extractsTo (parse "var 1..3: x;\nvar 1..3: y;\n\
       constraint int_lin_eq([1, 2, 3], [x, y], 5);\nsolve satisfy;") [])
  if st.failed == 0 then
    IO.println s!"passed {st.passed} propagator tests"
    return 0
  else
    IO.eprintln s!"{st.failed} propagator tests FAILED ({st.passed} passed)"
    return 1

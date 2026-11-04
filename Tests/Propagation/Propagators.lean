import LeanFzn.Solver.Propagation.DomainConstraints
import LeanFzn.Legacy.Solver.Propagation.Proofs.Fam.Reif
import LeanFzn.Legacy.Solver.Propagation.Proofs.Propagators
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
  | .arrayIntElementSlot xs i k, .arrayIntElementSlot xs' i' k' =>
      xs.length == xs'.length && (xs.zip xs').all (fun p => p.1 == p.2) &&
        i == i' && k == k'
  | .arrayBoolAndSlot is k, .arrayBoolAndSlot is' k' =>
      is.length == is'.length && (is.zip is').all (fun p => p.1 == p.2) &&
        k == k'
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

/-! ## PLAN G1: the unpinned bounds-decide-`r` arm (`int_le_reif`)

Test-only exhaustive oracle for `propLeReifB` (`Fam/Reif.lean`): on every tiny
configuration over the candidate domains below, the arm must never conflict,
every fitting solution of `int_le_reif` must satisfy the emitted pivot, and
the two non-pivot cause literals must be false at every fitting assignment.
The firing checks pin down the intended strength (separation ⇒ the matching
pin) and the guards (pinned reif, mixed/empty/aliased/out-of-range slots ⇒
`.stable`). A closure demo shows the arm removing the reif decision on a
separating fixture (before/after on a fixture where the arm fires), and the
pinned-direction differential re-checks that `propLeReifSlotB` equals
`propLeReifSlot` on every pinned shape. -/

/-- Trail-free test state with the given domains. -/
def armSt (doms : List (List Value)) : LeanFzn.Solver.Propagation.State :=
  { domains := doms.map Dom.ofList, trail := [], decisionLevel := 0, clauses := [], learned := [],
    queue := [], conflict := none }

/-- Exhaustive soundness of `propLeReifB` on a tiny state: no conflict, the
    emitted pivot is true at every fitting solution of `int_le_reif`, and
    every non-pivot (cause) literal is not true at any fitting assignment. -/
def armCheck (doms : List (List Value)) (i j r : Nat) : Bool :=
  match propLeReifB (armSt doms) i j r with
  | .stable => true
  | .conflict _ => false
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.leReifSlot i j r) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- The arm's emitted literal on a tiny state, if any. -/
def armEmitted (doms : List (List Value)) (i j r : Nat) : Option Literal :=
  match propLeReifB (armSt doms) i j r with
  | .implied l _ => some l
  | _ => none

/-- The candidate tiny domains of the exhaustive sweep. -/
def armCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi (-1)], [vi 0, vi 1], [vi (-1), vi 1],
    [vi 0, vi 1, vi 2], [Value.bool true], [Value.bool false],
    [Value.bool true, Value.bool false], [vi 0, Value.bool true]]

/-- Every tiny three-slot configuration, every aliasing/out-of-range variant,
    is exhaustively checked. -/
def armExhaustive : Bool :=
  armCandDomains.all fun d1 =>
    armCandDomains.all fun d2 =>
      armCandDomains.all fun d3 =>
        armCheck [d1, d2, d3] 0 1 2 && armCheck [d1, d2, d3] 0 1 0 &&
          armCheck [d1, d2, d3] 0 1 1 && armCheck [d1, d2, d3] 0 0 2 &&
          armCheck [d1, d2] 0 0 1

/-- Structural equality of results (test-only; `PropagationResult` carries no
    `DecidableEq`). -/
def armResEqB : PropagationResult → PropagationResult → Bool
  | .stable, .stable => true
  | .implied l r, .implied l' r' => (l == l') && (r.clause == r'.clause)
  | .conflict c, .conflict c' => c == c'
  | _, _ => false

/-- Byte-identical pinned direction: on every pinned shape of the sweep, the
    strengthened function returns exactly the old function's result. -/
def armPinnedAgree : Bool :=
  armCandDomains.all fun d1 =>
    armCandDomains.all fun d2 =>
      armCandDomains.all fun d3 =>
        let st := armSt [d1, d2, d3]
        if (domBoolPin st.domains 2 true || domBoolPin st.domains 2 false) then
          armResEqB (propLeReifSlotB st 0 1 2) (propLeReifSlot st 0 1 2)
        else true

/-- Apply the arm's emission to the box (test-level mirror of the engine's
    Boolean pin: only the reif pivot can fire). -/
def armApply (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .boolEq s b, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => v.eqB (.bool b)) else d
  | _, _ => doms

/-- One test-level propagation pass: the arm's emission applied to the box. -/
def armStep (doms : List (List Value)) (i j r : Nat) : List (List Value) :=
  match propLeReifB (armSt doms) i j r with
  | .implied l _ => armApply doms l
  | _ => doms

/-- Number of satisfying assignments of `int_le_reif` over a box. -/
def armSatCount (doms : List (List Value)) (i j r : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.leReifSlot i j r) a)).length

/-- PLAN G1 registration: the registered `.leReifSlot` propagator runs the
    strengthened function — on the separating fixture shape it emits the
    `r = true` pin through `propagatorOfProved`. -/
def armRegisteredFires : Bool :=
  match propagatorOfProved (.leReifSlot 0 1 2) with
  | some p =>
      match p.run (armSt [[vi 0], [vi 1, vi 2, vi 3], [Value.bool true, Value.bool false]]) with
      | .implied l _ => l == posBool 2 true
      | _ => false
  | none => false

/-- PLAN P3: the registered `.leReifSlot` propagator declares the audited
    `[i, j, r]` watch footprint. -/
def armRegisteredWatches : Bool :=
  match propagatorOfProved (.leReifSlot 0 1 2) with
  | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
  | none => false

/-- Micro-benchmark of the arm against the original delegation: `n` runs on a
    stable wide-domain state (the cost added when the registration switches)
    and on a firing separating state. -/
def armBench (n : Nat) : IO (Nat × Nat) := do
  let wide : List (List Value) :=
    [[vi 0, vi 100], [vi 50, vi 150], [Value.bool true, Value.bool false]]
  let sep : List (List Value) :=
    [[vi 0, vi 50], [vi 60, vi 100], [Value.bool true, Value.bool false]]
  let t0 ← IO.monoMsNow
  let mut acc := 0
  for _ in [:n] do
    acc := acc + (match propLeReifB (armSt wide) 0 1 2 with
      | .stable => 0
      | _ => 1)
    acc := acc + (match propLeReifSlotB (armSt wide) 0 1 2 with
      | .stable => 0
      | _ => 1)
  let t1 ← IO.monoMsNow
  let mut acc2 := 0
  for _ in [:n] do
    acc2 := acc2 + (match propLeReifB (armSt sep) 0 1 2 with
      | .implied _ _ => 1
      | _ => 0)
  let t2 ← IO.monoMsNow
  IO.println s!"arm bench: {n} stable-pair runs {t1 - t0}ms (acc {acc}), \
    {n} firing runs {t2 - t1}ms (fired {acc2})"
  pure (t1 - t0, t2 - t1)

/-! ## PLAN G1-B: the `bool2int` channel (`bool2intSlot`)

Test-only exhaustive oracle for `propBool2intSlot` (`Fam/Bool.lean`): on every
tiny configuration over the candidate domains below, a reported conflict must
exclude every solution (brute force), every implied head must be true at every
fitting solution, every non-pivot cause literal must be false at every fitting
assignment, and one propagation step must preserve the number of satisfying
assignments. The firing checks pin down the intended strength (Boolean pin ⇒
opposite-digit removal, raw `[.int 0]`/`[.int 1]` target ⇒ Boolean pin, wide
target `> 1` ⇒ the `posLe` conflict) and the guards (aliasing, empty and
out-of-range slots ⇒ `.stable`). -/

/-- The candidate tiny domains of the exhaustive sweep. -/
def b2iCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [vi (-1)], [vi 0, vi 1], [vi 0, vi 1, vi 2],
    [vi 0, vi 2], [Value.bool true], [Value.bool false],
    [Value.bool true, Value.bool false], [vi 0, Value.bool false]]

/-- Exhaustive soundness of `propBool2intSlot` on a tiny state. -/
def b2iCheck (doms : List (List Value)) (i k : Nat) : Bool :=
  match propBool2intSlot (armSt doms) i k with
  | .stable => true
  | .conflict c =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.bool2intSlot i k) a)).isEmpty &&
      (LeanFzn.Solver.Core.allAssigns doms).all
        (fun a => c.all (fun q => q.eval a != some true))
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.bool2intSlot i k) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- Every tiny two-slot configuration, every aliasing/out-of-range variant,
    is exhaustively checked. -/
def b2iExhaustive : Bool :=
  b2iCandDomains.all fun d1 =>
    b2iCandDomains.all fun d2 =>
      b2iCheck [d1, d2] 0 1 && b2iCheck [d1, d2] 0 0 && b2iCheck [d1, d2] 1 0 &&
        b2iCheck [d1] 0 1 && b2iCheck [d1, d2] 0 9

/-- Keep exactly the values with integer view `w`. -/
def b2iIntViewEq (w : Int) (v : Value) : Bool :=
  match Value.intView v with
  | some u => decide (u = w)
  | none => true

/-- The test-level literal application over a box. -/
def b2iFilterLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .intNe s w, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => !b2iIntViewEq w v) else d
  | .boolEq s b, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => v.eqB (.bool b)) else d
  | .intLe s w, true =>
      doms.mapIdx fun s' d =>
        if s' == s then d.filter (fun v => match Value.intView v with
          | some u => decide (u ≤ w) | none => true) else d
  | .intLe s w, false =>
      doms.mapIdx fun s' d =>
        if s' == s then d.filter (fun v => match Value.intView v with
          | some u => decide (w < u) | none => true) else d
  | _, _ => doms

/-- Number of satisfying assignments of `bool2intSlot` over a box. -/
def b2iSatCount (doms : List (List Value)) (i k : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.bool2intSlot i k) a)).length

/-- One test-level propagation pass: the run's emission applied to the box. -/
def b2iStep (doms : List (List Value)) (i k : Nat) : List (List Value) :=
  match propBool2intSlot (armSt doms) i k with
  | .implied l _ => b2iFilterLit doms l
  | _ => doms

/-- One step of the channel never removes a satisfying assignment. -/
def b2iPreserves : Bool :=
  b2iCandDomains.all fun d1 =>
    b2iCandDomains.all fun d2 =>
      b2iSatCount (b2iStep [d1, d2] 0 1) 0 1 == b2iSatCount [d1, d2] 0 1

/-- The registered `.bool2intSlot` propagator runs the channel function:
    on a wide target it reports the `posLe` bound conflict. -/
def b2iRegisteredFires : Bool :=
  match propagatorOfProved (.bool2intSlot 0 1) with
  | some p =>
      match p.run (armSt [[Value.bool true, Value.bool false], [vi 2]]) with
      | .conflict cc => cc == [posLe 1 1]
      | _ => false
  | none => false

/-- The registered `.bool2intSlot` propagator pins the source Boolean from a
    raw `[.int 1]` target. -/
def b2iRegisteredTargetPin : Bool :=
  match propagatorOfProved (.bool2intSlot 0 1) with
  | some p =>
      match p.run (armSt [[Value.bool true, Value.bool false], [vi 1]]) with
      | .implied l _ => l == posBool 0 true
      | _ => false
  | none => false

/-- PLAN P3: the registered `.bool2intSlot` propagator declares the audited
    `[i, k]` watch footprint. -/
def b2iRegisteredWatches : Bool :=
  match propagatorOfProved (.bool2intSlot 0 1) with
  | some p => p.watches == [.intLe 0 0, .intLe 1 0]
  | none => false

/-! ## PLAN G1c: the constant-table element (`arrayIntElementSlot`)

Test-only exhaustive oracle for `propArrayIntElement` (`Fam/Element.lean`): on
every tiny configuration over the candidate domains and tables below, a
reported conflict must exclude every solution (brute force), every implied
head must be true at every fitting solution, every non-pivot cause literal
must be false at every fitting assignment, and one propagation step must
preserve the number of satisfying assignments. The firing checks pin down the
intended strength (pinned index ⇒ target narrowing or out-of-range conflict,
pinned target ⇒ unsupported index removal, unpinned out-of-range unit
removal, no-support removal on an integer-only target) and the guards
(aliasing, empty and out-of-range slots ⇒ `.stable`). -/

/-- The constant tables swept by the exhaustive oracle. -/
def aieTables : List (List Int) :=
  [[], [7], [4, 5, 6], [4, 5, 6, 7], [0, 0, 0]]

/-- The candidate tiny domains of the exhaustive sweep. -/
def aieCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [vi 3], [vi (-1)], [vi 1, vi 2],
    [vi 0, vi 1, vi 2], [vi 1, vi 3], [vi 2, vi 3], [vi 5, vi 6],
    [Value.bool true], [Value.bool false],
    [Value.bool true, Value.bool false], [vi 1, Value.bool true]]

/-- Exhaustive soundness of `propArrayIntElement` on a tiny state. -/
def aieCheck (xs : List Int) (doms : List (List Value)) (i k : Nat) : Bool :=
  match propArrayIntElement (armSt doms) xs i k with
  | .stable => true
  | .conflict c =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.arrayIntElementSlot xs i k) a)).isEmpty &&
      (LeanFzn.Solver.Core.allAssigns doms).all
        (fun a => c.all (fun q => q.eval a != some true))
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.arrayIntElementSlot xs i k) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- Every tiny two-slot configuration, every aliasing/out-of-range variant,
    is exhaustively checked. -/
def aieExhaustive : Bool :=
  aieTables.all fun xs =>
    aieCandDomains.all fun d1 =>
      aieCandDomains.all fun d2 =>
        aieCheck xs [d1, d2] 0 1 && aieCheck xs [d1, d2] 0 0 &&
          aieCheck xs [d1, d2] 1 0 && aieCheck xs [d1] 0 1 &&
          aieCheck xs [d1, d2] 0 9

/-- The test-level literal application over a box (removal literals only). -/
def aieFilterLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .intNe s w, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => !b2iIntViewEq w v) else d
  | _, _ => doms

/-- Number of satisfying assignments of `arrayIntElementSlot` over a box. -/
def aieSatCount (xs : List Int) (doms : List (List Value)) (i k : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.arrayIntElementSlot xs i k) a)).length

/-- One test-level propagation pass: the run's emission applied to the box. -/
def aieStep (xs : List Int) (doms : List (List Value)) (i k : Nat) : List (List Value) :=
  match propArrayIntElement (armSt doms) xs i k with
  | .implied l _ => aieFilterLit doms l
  | _ => doms

/-- One step of the element propagator never removes a satisfying assignment. -/
def aiePreserves : Bool :=
  aieTables.all fun xs =>
    aieCandDomains.all fun d1 =>
      aieCandDomains.all fun d2 =>
        aieSatCount xs (aieStep xs [d1, d2] 0 1) 0 1 == aieSatCount xs [d1, d2] 0 1

/-- The candidate domain pairs of the no-support preservation sweep (the
    integer-only guard needs integer target domains). -/
def aieIntDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [vi 3], [vi (-1)], [vi 1, vi 2],
    [vi 0, vi 1, vi 2], [vi 1, vi 3], [vi 2, vi 3], [vi 5, vi 6]]

/-- Solution-count preservation over the integer-domain sweep (where the
    no-support arm fires). -/
def aiePreservesInt : Bool :=
  aieTables.all fun xs =>
    aieIntDomains.all fun d1 =>
      aieIntDomains.all fun d2 =>
        aieSatCount xs (aieStep xs [d1, d2] 0 1) 0 1 == aieSatCount xs [d1, d2] 0 1

/-- The registered `.arrayIntElementSlot` propagator runs the element
    function: a pinned index with a defined entry removes the first target
    value with a different integer view. -/
def aieRegisteredFires : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p =>
      match p.run (armSt [[vi 2], [vi 4, vi 10]]) with
      | .implied l rs => l == posNe 1 4 && rs.clause == [posNe 1 4, posNe 0 2]
      | _ => false
  | none => false

/-- The registered element propagator conflicts on an out-of-range pinned
    index. -/
def aieRegisteredOutRange : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p =>
      match p.run (armSt [[vi 5], [vi 4, vi 5, vi 6]]) with
      | .conflict cc => cc == [posNe 0 5]
      | _ => false
  | none => false

/-- The registered element propagator removes an unsupported index through
    the falsified `k = v` on an integer-only target. -/
def aieRegisteredNoSupport : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p =>
      match p.run (armSt [[vi 1, vi 2, vi 3], [vi 5, vi 6]]) with
      | .implied l rs => l == posNe 0 1 && rs.clause == [posNe 0 1, negNe 1 4]
      | _ => false
  | none => false

/-- The registered element propagator removes an index through the pinned
    target. -/
def aieRegisteredPinVal : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p =>
      match p.run (armSt [[vi 1, vi 2, vi 3], [vi 5]]) with
      | .implied l rs => l == posNe 0 1 && rs.clause == [posNe 0 1, posNe 1 5]
      | _ => false
  | none => false

/-- The registered element propagator removes an out-of-range index by the
    unit clause. -/
def aieRegisteredOutRemoval : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p =>
      match p.run (armSt [[vi 7, vi 1], [vi 4, vi 5]]) with
      | .implied l rs => l == posNe 0 7 && rs.clause == [posNe 0 7]
      | _ => false
  | none => false

/-- The guards: aliasing, empty and out-of-range slots, and a fully
    supported unpinned state stay `.stable`. -/
def aieGuardsStable : Bool :=
  (match propArrayIntElement (armSt [[vi 1]]) [4, 5, 6] 0 0 with
    | .stable => true
    | _ => false) &&
  (match propArrayIntElement (armSt [[], [vi 4]]) [4, 5, 6] 0 1 with
    | .stable => true
    | _ => false) &&
  (match propArrayIntElement (armSt [[vi 1], [vi 4]]) [4, 5, 6] 0 5 with
    | .stable => true
    | _ => false) &&
  (match propArrayIntElement (armSt [[vi 1, vi 2], [vi 4, vi 5, vi 6]]) [4, 5, 6] 0 1 with
    | .stable => true
    | _ => false)

/-- PLAN G1c registration / PLAN P1 locality: the registered
    `.arrayIntElementSlot` propagator watches exactly its index and target
    slots (the table is a constant). -/
def aieRegisteredWatches : Bool :=
  match propagatorOfProved (.arrayIntElementSlot [4, 5, 6] 0 1) with
  | some p => p.watches == [.intLe 0 0, .intLe 1 0]
  | none => false

/-! ## PLAN §3.3 item 1: the variable-table element (`arrayVarIntElementSlot`)

Test-only exhaustive oracle for `propArrayVarIntElement`
(`Fam/VarElement.lean`): on every tiny configuration over the candidate
domains and table-slot lists below, a reported conflict must exclude every
solution, every implied head must be true at every fitting solution, every
non-pivot cause literal must be false at every fitting assignment, and one
propagation step must preserve the number of satisfying assignments. The
firing checks pin down the intended strength (pinned index ⇒ target/entry
narrowing or out-of-range conflict, pinned target ⇒ unsupported-index
removal, unpinned out-of-range unit removal, hull separation and
no-support removal) and the guards (aliasing, repeated table slots, empty
and non-integer slots ⇒ `.stable`). -/

/-- The table-slot lists swept by the exhaustive oracle (with the index,
    target and an aliasing slot among the variants). -/
def avieTables : List (List Nat) :=
  [[0, 1], [1, 0], [0], [], [2], [0, 0]]

/-- The candidate tiny domains of the exhaustive sweep. -/
def avieCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [vi 3], [vi 1, vi 2], [vi 2, vi 3],
    [vi 0, vi 1, vi 2], [Value.bool true], [vi 1, Value.bool true]]

/-- Exhaustive soundness of `propArrayVarIntElement` on a tiny state. -/
def avieCheck (is : List Nat) (doms : List (List Value)) (i k : Nat) : Bool :=
  match propArrayVarIntElement (armSt doms) is i k with
  | .stable => true
  | .conflict c =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.arrayVarIntElementSlot is i k) a)).isEmpty &&
      (LeanFzn.Solver.Core.allAssigns doms).all
        (fun a => c.all (fun q => q.eval a != some true))
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.arrayVarIntElementSlot is i k) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- Every tiny four-slot configuration, every table-slot list variant and
    index/target/aliasing placement is exhaustively checked. -/
def avieExhaustive : Bool :=
  avieTables.all fun is =>
    avieCandDomains.all fun d1 =>
      avieCandDomains.all fun d2 =>
        avieCandDomains.all fun d3 =>
          avieCandDomains.all fun d4 =>
            avieCheck is [d1, d2, d3, d4] 2 3 &&
              avieCheck is [d1, d2, d3, d4] 3 2 &&
              avieCheck is [d1, d2, d3, d4] 2 2

/-- Number of satisfying assignments of `arrayVarIntElementSlot` over a box. -/
def avieSatCount (is : List Nat) (doms : List (List Value)) (i k : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.arrayVarIntElementSlot is i k) a)).length

/-- One test-level propagation pass: the run's emission applied to the box. -/
def avieStep (is : List Nat) (doms : List (List Value)) (i k : Nat) :
    List (List Value) :=
  match propArrayVarIntElement (armSt doms) is i k with
  | .implied l _ => aieFilterLit doms l
  | _ => doms

/-- One step of the variable-table element propagator never removes a
    satisfying assignment. -/
def aviePreserves : Bool :=
  avieTables.all fun is =>
    avieCandDomains.all fun d1 =>
      avieCandDomains.all fun d2 =>
        avieCandDomains.all fun d3 =>
          avieCandDomains.all fun d4 =>
            avieSatCount is (avieStep is [d1, d2, d3, d4] 2 3) 2 3 ==
              avieSatCount is [d1, d2, d3, d4] 2 3

/-- The registered `.arrayVarIntElementSlot` propagator runs the family
    function: a pinned index narrows the target through the entry slot. -/
def avieRegisteredFires : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 7], [vi 5], [vi 2], [vi 5, vi 9]]) with
      | .implied l rs => l == posNe 3 9 &&
          rs.clause == [posNe 3 9, posNe 2 2, negNe 1 9]
      | _ => false
  | none => false

/-- The registered variable-table propagator conflicts on an out-of-range
    pinned index. -/
def avieRegisteredOutRange : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 7], [vi 5], [vi 5], [vi 7, vi 5]]) with
      | .conflict cc => cc == [posNe 2 5]
      | _ => false
  | none => false

/-- The registered variable-table propagator removes an unsupported index
    through a pinned target. -/
def avieRegisteredPinVal : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 7], [vi 5], [vi 1, vi 2], [vi 5]]) with
      | .implied l rs => l == posNe 2 1 &&
          rs.clause == [posNe 2 1, posNe 3 5, negNe 0 5]
      | _ => false
  | none => false

/-- The registered variable-table propagator removes a below-separated
    index through the two hull causes. -/
def avieRegisteredBelow : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 1, vi 2], [vi 2, vi 3], [vi 1, vi 2],
          [vi 7, vi 8]]) with
      | .implied l rs => l == posNe 2 1 &&
          rs.clause == [posNe 2 1, negLe 0 2, posLe 3 6]
      | _ => false
  | none => false

/-- The registered variable-table propagator removes a target value absent
    from every table slot. -/
def avieRegisteredNoSupp : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 1, vi 2], [vi 2, vi 3], [vi 1, vi 2],
          [vi 1, vi 4]]) with
      | .implied l rs => l == posNe 3 4 &&
          rs.clause == [posNe 3 4, negNe 0 4, negNe 1 4]
      | _ => false
  | none => false

/-- The registered variable-table propagator removes a hole singleton entry
    value absent from the target domain. -/
def avieRegisteredSingle : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vi 2], [vi 1, vi 3], [vi 1, vi 2],
          [vi 1, vi 3]]) with
      | .implied l rs => l == posNe 2 1 &&
          rs.clause == [posNe 2 1, posNe 0 2, negNe 3 2]
      | _ => false
  | none => false

/-- The guards: aliasing, a table slot equal to the index/target, repeated
    table slots, empty/non-integer slots, and a fully supported unpinned
    state stay `.stable`. -/
def avieGuardsStable : Bool :=
  (match propArrayVarIntElement (armSt [[vi 1], [vi 1], [vi 1], [vi 1]]) [0, 1] 2 2 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[vi 1], [vi 1], [vi 1], [vi 1]]) [0, 2] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[vi 1], [vi 1], [vi 1], [vi 1]]) [0, 3] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[vi 1], [vi 1], [vi 1], [vi 1]]) [0, 0] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[], [vi 1], [vi 1], [vi 1]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[Value.bool true], [vi 1], [vi 1], [vi 1]])
      [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarIntElement (armSt [[vi 1, vi 2], [vi 1, vi 2],
      [vi 1, vi 2], [vi 1, vi 2]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false)

/-- PLAN §3.3 registration: the registered `.arrayVarIntElementSlot`
    propagator watches the index, the target and every table slot (P3). -/
def avieRegisteredNoWatches : Bool :=
  match propagatorOfProved (.arrayVarIntElementSlot [0, 1] 2 3) with
  | some p => p.watches == [.intLe 2 0, .intLe 3 0, .intLe 0 0, .intLe 1 0]
  | none => false

/-! ## PLAN §3.3 item 2: the variable-table Boolean element
(`arrayVarBoolElementSlot`)

Test-only exhaustive oracle for `propArrayVarBoolElement`
(`Fam/BoolElement.lean`): on every tiny configuration over the candidate
domains and table-slot lists below, a reported conflict must exclude every
solution, every implied head must be true at every fitting solution, every
non-pivot cause literal must be false at every fitting assignment, and one
propagation step must preserve the number of satisfying assignments. The
firing checks pin down the intended strength (pinned index ⇒ Boolean
channel narrowing or out-of-range conflict, pinned target ⇒ unsupported-index
removal, unpinned opposite-singleton and no-support removal, conflict on an
empty target support) and the guards (aliasing, repeated table slots, empty,
non-Boolean and non-integer slots ⇒ `.stable`). -/

def vb (b : Bool) : Value := .bool b

/-- The table-slot lists swept by the exhaustive oracle. -/
def avbeTables : List (List Nat) :=
  [[0, 1], [1, 0], [0], [], [2], [0, 0]]

/-- The candidate tiny domains of the exhaustive sweep. -/
def avbeCandDomains : List (List Value) :=
  [[], [vb true], [vb false], [vb true, vb false], [vi 0], [vi 1],
    [vi 2], [vi 1, vi 2], [vb true, vi 1]]

/-- Exhaustive soundness of `propArrayVarBoolElement` on a tiny state. -/
def avbeCheck (is : List Nat) (doms : List (List Value)) (i k : Nat) : Bool :=
  match propArrayVarBoolElement (armSt doms) is i k with
  | .stable => true
  | .conflict c =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.arrayVarBoolElementSlot is i k) a)).isEmpty &&
      (LeanFzn.Solver.Core.allAssigns doms).all
        (fun a => c.all (fun q => q.eval a != some true))
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.arrayVarBoolElementSlot is i k) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- Every tiny four-slot configuration, every table-slot list variant and
    index/target/aliasing placement is exhaustively checked. -/
def avbeExhaustive : Bool :=
  avbeTables.all fun is =>
    avbeCandDomains.all fun d1 =>
      avbeCandDomains.all fun d2 =>
        avbeCandDomains.all fun d3 =>
          avbeCandDomains.all fun d4 =>
            avbeCheck is [d1, d2, d3, d4] 2 3 &&
              avbeCheck is [d1, d2, d3, d4] 3 2 &&
              avbeCheck is [d1, d2, d3, d4] 2 2

/-- The test-level literal application over a box (index and Boolean
    removals). -/
def avbeFilterLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .intNe s w, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => !b2iIntViewEq w v) else d
  | .boolEq s b, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => v.eqB (.bool b)) else d
  | _, _ => doms

/-- Number of satisfying assignments of `arrayVarBoolElementSlot` over a box. -/
def avbeSatCount (is : List Nat) (doms : List (List Value)) (i k : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.arrayVarBoolElementSlot is i k) a)).length

/-- One test-level propagation pass: the run's emission applied to the box. -/
def avbeStep (is : List Nat) (doms : List (List Value)) (i k : Nat) :
    List (List Value) :=
  match propArrayVarBoolElement (armSt doms) is i k with
  | .implied l _ => avbeFilterLit doms l
  | _ => doms

/-- One step of the Boolean variable-table element propagator never removes
    a satisfying assignment. -/
def avbePreserves : Bool :=
  avbeTables.all fun is =>
    avbeCandDomains.all fun d1 =>
      avbeCandDomains.all fun d2 =>
        avbeCandDomains.all fun d3 =>
          avbeCandDomains.all fun d4 =>
            avbeSatCount is (avbeStep is [d1, d2, d3, d4] 2 3) 2 3 ==
              avbeSatCount is [d1, d2, d3, d4] 2 3

/-- The registered `.arrayVarBoolElementSlot` propagator runs the family
    function: a pinned index narrows the Boolean target through the entry
    slot. -/
def avbeRegisteredFires : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb false], [vb false], [vi 2], [vb true, vb false]]) with
      | .implied l rs => l == posBool 3 false &&
          rs.clause == [posBool 3 false, posNe 2 2, posBool 1 true]
      | _ => false
  | none => false

/-- The registered Boolean variable-table propagator conflicts on an
    out-of-range pinned index. -/
def avbeRegisteredOutRange : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb true], [vb false], [vi 5], [vb true, vb false]]) with
      | .conflict cc => cc == [posNe 2 5]
      | _ => false
  | none => false

/-- The registered Boolean variable-table propagator removes an unsupported
    index through a pinned target. -/
def avbeRegisteredPinVal : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb false], [vb false], [vi 1, vi 2], [vb true]]) with
      | .implied l rs => l == posNe 2 1 &&
          rs.clause == [posNe 2 1, posBool 3 false, posBool 0 true]
      | _ => false
  | none => false

/-- The registered Boolean variable-table propagator removes an unpinned
    out-of-range index by the unit clause. -/
def avbeRegisteredOutUnpinned : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb true], [vb false], [vi 1, vi 5], [vb true, vb false]]) with
      | .implied l rs => l == posNe 2 5 && rs.clause == [posNe 2 5]
      | _ => false
  | none => false

/-- The registered Boolean variable-table propagator removes a target value
    absent from every table slot. -/
def avbeRegisteredNoSupp : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb true], [vb true], [vi 1, vi 2], [vb true, vb false]]) with
      | .implied l rs => l == posBool 3 true &&
          rs.clause == [posBool 3 true, posBool 0 false, posBool 1 false]
      | _ => false
  | none => false

/-- The registered Boolean variable-table propagator reports a conflict on
    an empty target support: the target is `true`, the entry only `false`. -/
def avbeRegisteredEmptySupport : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p =>
      match p.run (armSt [[vb false], [vb false], [vi 2], [vb true]]) with
      | .conflict cc =>
          cc == [posBool 3 false, posNe 2 2, posBool 1 true]
      | _ => false
  | none => false

/-- The guards: aliasing, a table slot equal to the index/target, repeated
    table slots, non-integer/non-Boolean/empty slots, and a fully supported
    unpinned state stay `.stable`. -/
def avbeGuardsStable : Bool :=
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vi 1], [vb true]]) [0, 1] 2 2 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vi 1], [vb true]]) [0, 2] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vi 1], [vb true]]) [0, 3] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vi 1], [vb true]]) [0, 0] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[], [vb true], [vi 1], [vb true]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vi 0], [vi 1], [vb true]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vb true], [vb true]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true], [vb true], [vi 1], [vi 0]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false) &&
  (match propArrayVarBoolElement (armSt [[vb true, vb false], [vb true, vb false],
      [vi 1, vi 2], [vb true, vb false]]) [0, 1] 2 3 with
    | .stable => true
    | _ => false)

/-- PLAN §3.3 item 2 registration: the registered
    `.arrayVarBoolElementSlot` propagator watches the index, the target and
    every table slot (P3). -/
def avbeRegisteredNoWatches : Bool :=
  match propagatorOfProved (.arrayVarBoolElementSlot [0, 1] 2 3) with
  | some p => p.watches == [.intLe 2 0, .intLe 3 0, .intLe 0 0, .intLe 1 0]
  | none => false

/-! ## PLAN G1d: the `linLeReif` r = false direction

Test-only exhaustive oracle for `propLinLeReifB`/`propLinLeReif`
(`Fam/Lin.lean`): on every tiny configuration over the candidate domains,
coefficient pairs and bounds below, every implied head must be true at every
fitting solution of `int_lin_le_reif` (brute force), every non-pivot cause
literal must be false at every fitting assignment, and one propagation step
must preserve the number of satisfying assignments. The firing checks pin
down the two new emissions (the dual `sumMin > b ⇒ r = false` pin and the
retained `r = false` delegated bound implication). -/

/-- The candidate tiny domains of the G1d sweep. -/
def lrCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [vi (-1)], [vi 0, vi 1], [vi 1, vi 2],
    [vi 0, vi 1, vi 2], [Value.bool true], [Value.bool false],
    [Value.bool true, Value.bool false]]

/-- The coefficient pairs and bounds of the G1d sweep. -/
def lrCoeffBounds : List (List Int × Int) :=
  [([1, 1], 1), ([1, 1], 2), ([1, -1], 0), ([-1, -1], -1), ([2, -1], 1),
    ([0, 1], 1)]

/-- Exhaustive soundness of `propLinLeReifB` on a tiny state: no conflict,
    implied heads true at fitting solutions, causes false at fitting
    assignments. -/
def lrCheck (coeffs : List Int) (b : Int) (doms : List (List Value)) : Bool :=
  match propLinLeReifB (armSt doms) coeffs [0, 1] b 2 with
  | .stable => true
  | .conflict _ => false
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.linLeReif coeffs [0, 1] b 2) a ||
          l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

/-- Exhaustive soundness of the full `propLinLeReif` on a tiny state: a
    reported conflict must exclude every fitting solution; an implied head
    must be true at every fitting solution with all causes false at every
    fitting assignment. -/
def lrCheckReg (coeffs : List Int) (b : Int) (doms : List (List Value)) : Bool :=
  match propLinLeReif (armSt doms) coeffs [0, 1] b 2 with
  | .stable => true
  | .conflict _ =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.linLeReif coeffs [0, 1] b 2) a)).isEmpty
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.linLeReif coeffs [0, 1] b 2) a ||
          l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

def lrExhaustive : Bool :=
  lrCoeffBounds.all fun cb =>
    lrCandDomains.all fun d0 =>
      lrCandDomains.all fun d1 =>
        lrCandDomains.all fun d2 =>
          lrCheck cb.1 cb.2 [d0, d1, d2] && lrCheckReg cb.1 cb.2 [d0, d1, d2]

/-- The test-level literal application over a box (Boolean pins only). -/
def lrFilterLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .boolEq s w, true =>
      doms.mapIdx fun s' d =>
        if s' == s then d.filter (fun v => v.eqB (.bool w)) else d
  | _, _ => doms

/-- Number of satisfying assignments of `linLeReif` over a box. -/
def lrSatCount (coeffs : List Int) (b : Int) (doms : List (List Value)) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.linLeReif coeffs [0, 1] b 2) a)).length

/-- One test-level propagation pass: the run's emission applied to the box. -/
def lrStep (coeffs : List Int) (b : Int) (doms : List (List Value)) : List (List Value) :=
  match propLinLeReifB (armSt doms) coeffs [0, 1] b 2 with
  | .implied l _ => lrFilterLit doms l
  | _ => doms

/-- One step of the bounds arm never removes a satisfying assignment. -/
def lrPreserves : Bool :=
  lrCoeffBounds.all fun cb =>
    lrCandDomains.all fun d0 =>
      lrCandDomains.all fun d1 =>
        lrCandDomains.all fun d2 =>
          lrSatCount cb.1 cb.2 (lrStep cb.1 cb.2 [d0, d1, d2]) ==
            lrSatCount cb.1 cb.2 [d0, d1, d2]

/-- The dual arm fires with the exact escapes and min-causes. -/
def lrDualFires : Bool :=
  match propLinLeReifB
      (armSt [[vi 4], [vi 4], [Value.bool true, Value.bool false]])
      [1, 1] [0, 1] 3 2 with
  | .implied l rs =>
      l == posBool 2 false &&
        rs.clause == [posBool 2 false, posBool 0 false, posBool 0 true,
          posBool 1 false, posBool 1 true, posLe 0 3, posLe 1 3]
  | _ => false

/-- A feasible inequality (minimum contribution inside the bound while the
    maximum exceeds it) stays stable. -/
def lrDualGuardStable : Bool :=
  match propLinLeReifB
      (armSt [[vi 0, vi 2], [vi 0, vi 2], [Value.bool true, Value.bool false]])
      [1, 1] [0, 1] 3 2 with
  | .stable => true
  | _ => false

/-- The registered `.linLeReif` propagator fires the dual pin through
    `propagatorOfProved`. -/
def lrRegisteredDual : Bool :=
  match propagatorOfProved (.linLeReif [1, 1] [0, 1] 3 2) with
  | some p =>
      match p.run (armSt [[vi 4], [vi 4], [Value.bool true, Value.bool false]]) with
      | .implied l _ => l == posBool 2 false
      | _ => false
  | none => false

/-- The registered propagator's pinned-`false` branch retains the delegated
    bound implication (`y ≥ 5` from `x + y ≥ 11` with `r = false`), wrapped
    in the `r = true` escape. -/
def lrRegisteredBound : Bool :=
  match propagatorOfProved (.linLeReif [1, 1] [0, 1] 10 2) with
  | some p =>
      match p.run (armSt [[vi 4, vi 6], [vi 4, vi 9], [Value.bool false]]) with
      | .implied l rs =>
          l == negLe 1 4 && rs.clause.any (fun q => q == posBool 2 true)
      | _ => false
  | none => false

/-- The pinned-`true` direction is unchanged (the delegation still emits
    the underlying upper bound with the `r = false` escape). -/
def lrRegisteredTrue : Bool :=
  match propagatorOfProved (.linLeReif [1, 1] [0, 1] 10 2) with
  | some p =>
      match p.run (armSt [[vi 4, vi 6], [vi 4, vi 9], [Value.bool true]]) with
      | .implied l rs =>
          l == posLe 1 6 && rs.clause.any (fun q => q == posBool 2 false)
      | _ => false
  | none => false

/-- The registered `.linLeReif` propagator watches the reif slot and the
    constraint slots. -/
def lrRegisteredWatches : Bool :=
  match propagatorOfProved (.linLeReif [1, 1] [0, 1] 10 2) with
  | some p => p.watches == [.intLe 2 0, .intLe 0 0, .intLe 1 0]
  | none => false

/-- The registered `.minSlot`/`.maxSlot` propagators watch all three slots. -/
def msRegisteredWatches : Bool :=
  (match propagatorOfProved (.minSlot 0 1 2) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.maxSlot 0 1 2) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false)

/-- P3 batch 8: `timesSlot` watches its three slots. -/
def tsRegisteredWatches : Bool :=
  match propagatorOfProved (.timesSlot 0 1 2) with
  | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
  | none => false

/-- P3 batch 9: `absSlot` watches `[i, k]`; `divGen`/`modGen` watch every
    slot named by their three operands (literals contribute none). -/
def adRegisteredWatches : Bool :=
  (match propagatorOfProved (.absSlot 0 1) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0]
   | none => false) &&
  (match propagatorOfProved (.divGen (.slot 0) (.slot 1) (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.modGen (.slot 0) (.lit 3) (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 2 0]
   | none => false)

/-- P3 batch 10: `maxGen`/`minGen` watch their operands' named slots and
    the result slot (literals contribute none). -/
def genRegisteredWatches : Bool :=
  (match propagatorOfProved (.maxGen [.slot 0, .lit 5, .slot 1] (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.minGen [.slot 0, .slot 1] (.lit 4)) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0]
   | none => false)

/-- P3 batch 11: the all-slot `minPair`/`maxPair` shapes watch `[i, j, k]`;
    a literal operand keeps `propCheck` at `dcSlotsFull dc`. -/
def pairRegisteredWatches : Bool :=
  (match propagatorOfProved (.minPair (.slot 0) (.slot 1) (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.maxPair (.slot 0) (.slot 1) (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 1 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.minPair (.slot 0) (.lit 3) (.slot 2)) with
   | some p => p.watches == [.intLe 0 0, .intLe 2 0]
   | none => false) &&
  (match propagatorOfProved (.maxPair (.lit 7) (.slot 1) (.slot 2)) with
   | some p => p.watches == [.intLe 1 0, .intLe 2 0]
   | none => false)

/-! ## PLAN G1e: the array-Boolean conjunction (`arrayBoolAndSlot`)

Test-only exhaustive oracle for `propArrayBoolAnd` (`Fam/Bool.lean`): on
every tiny configuration over the candidate domains and input lists below,
a reported conflict must exclude every fitting solution (brute force),
every implied head must be true at every fitting solution, every non-pivot
cause literal must be false at every fitting assignment, and one
propagation step must preserve the number of satisfying assignments. The
firing checks pin down the four rounds (all inputs pinned true, a
pinned-false input, a pinned-true target pruning inputs, the Boolean-only
singleton) and the guards (aliasing, empty and out-of-range slots). -/

def abaCandDomains : List (List Value) :=
  [[], [vi 0], [vi 1], [vi 2], [Value.bool true], [Value.bool false],
    [Value.bool true, Value.bool false], [vi 0, Value.bool true],
    [vi 0, vi 1]]

def abaCandLists : List (List Nat) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 0], [0, 1, 2]]

def abaCheck (doms : List (List Value)) (is : List Nat) (k : Nat) : Bool :=
  match propArrayBoolAnd (armSt doms) is k with
  | .stable => true
  | .conflict _ =>
      ((LeanFzn.Solver.Core.allAssigns doms).filter
        (fun a => DomConstraint.satisfiedB (.arrayBoolAndSlot is k) a)).isEmpty
  | .implied l rs =>
      (LeanFzn.Solver.Core.allAssigns doms).all fun a =>
        (!DomConstraint.satisfiedB (.arrayBoolAndSlot is k) a || l.eval a == some true) &&
          (rs.clause.drop 1).all (fun q => q.eval a != some true)

def abaExhaustive : Bool :=
  abaCandLists.all fun is =>
    abaCandDomains.all fun d0 =>
      abaCandDomains.all fun d1 =>
        abaCandDomains.all fun d2 =>
          abaCheck [d0, d1, d2] is 2 && abaCheck [d0, d1] is 5 &&
            abaCheck [d0] is 0

def abaFilterLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom, l.positive with
  | .boolEq s w, true =>
      doms.mapIdx fun s' d => if s' == s then d.filter (fun v => v.eqB (.bool w)) else d
  | _, _ => doms

def abaSatCount (doms : List (List Value)) (is : List Nat) (k : Nat) : Nat :=
  ((LeanFzn.Solver.Core.allAssigns doms).filter
    (fun a => DomConstraint.satisfiedB (.arrayBoolAndSlot is k) a)).length

def abaStep (doms : List (List Value)) (is : List Nat) (k : Nat) : List (List Value) :=
  match propArrayBoolAnd (armSt doms) is k with
  | .implied l _ => abaFilterLit doms l
  | _ => doms

def abaPreserves : Bool :=
  abaCandLists.all fun is =>
    abaCandDomains.all fun d0 =>
      abaCandDomains.all fun d1 =>
        abaCandDomains.all fun d2 =>
          abaSatCount (abaStep [d0, d1, d2] is 2) is 2 ==
            abaSatCount [d0, d1, d2] is 2

/-- The all-inputs-pinned round pins the target with the inputs' false
    causes. -/
def abaAllTrueFires : Bool :=
  match propArrayBoolAnd
      (armSt [[Value.bool true], [Value.bool true],
        [Value.bool true, Value.bool false]]) [0, 1] 2 with
  | .implied l rs =>
      l == posBool 2 true &&
        rs.clause == [posBool 2 true, posBool 0 false, posBool 1 false]
  | _ => false

/-- A pinned-false input forces the target false. -/
def abaPinFalseFires : Bool :=
  match propArrayBoolAnd
      (armSt [[Value.bool false], [Value.bool true, Value.bool false],
        [Value.bool true, Value.bool false]]) [0] 2 with
  | .implied l rs =>
      l == posBool 2 false && rs.clause == [posBool 2 false, posBool 0 true]
  | _ => false

/-- A pinned-true target prunes the first input. -/
def abaKTrueFires : Bool :=
  match propArrayBoolAnd
      (armSt [[Value.bool true, Value.bool false], [Value.bool true],
        [Value.bool true]]) [0] 2 with
  | .implied l rs =>
      l == posBool 0 true && rs.clause == [posBool 0 true, posBool 2 false]
  | _ => false

/-- The Boolean-only singleton round follows a pinned-false target. -/
def abaSingleFires : Bool :=
  match propArrayBoolAnd
      (armSt [[Value.bool true, Value.bool false], [],
        [Value.bool false]]) [0] 2 with
  | .implied l rs =>
      l == posBool 0 false && rs.clause == [posBool 0 false, posBool 2 true]
  | _ => false

/-- The empty input list pins the target true (the `all [] = true` case,
    as a unit clause). -/
def abaEmptyFires : Bool :=
  match propArrayBoolAnd
      (armSt [[], [], [Value.bool true, Value.bool false]]) [] 2 with
  | .implied l rs => l == posBool 2 true && rs.clause == [posBool 2 true]
  | _ => false

/-- The pinned-false input round reports a conflict against a
    pinned-true target. -/
def abaConflictFires : Bool :=
  match propArrayBoolAnd (armSt [[Value.bool false], [Value.bool true]]) [0] 1 with
  | .conflict cc => cc == [posBool 1 false, posBool 0 true]
  | _ => false

/-- The guards: aliasing, empty and out-of-range slots stay `.stable`. -/
def abaGuardsStable : Bool :=
  (match propArrayBoolAnd (armSt [[Value.bool true, Value.bool false]]) [0] 0 with
    | .stable => true
    | _ => false) &&
  (match propArrayBoolAnd (armSt [[], [Value.bool true, Value.bool false]]) [0] 1 with
    | .stable => true
    | _ => false) &&
  (match propArrayBoolAnd
      (armSt [[Value.bool true, Value.bool false], [Value.bool true]])
      [0] 5 with
    | .stable => true
    | _ => false)

/-- The registered `.arrayBoolAndSlot` propagator runs the family function
    and watches the target plus every input slot (P3). -/
def abaRegisteredFires : Bool :=
  match propagatorOfProved (.arrayBoolAndSlot [0, 1] 2) with
  | some p =>
      p.watches == [.intLe 2 0, .intLe 0 0, .intLe 1 0] &&
        (match p.run (armSt [[Value.bool true], [Value.bool true],
          [Value.bool true, Value.bool false]]) with
          | .implied l _ => l == posBool 2 true
          | _ => false)
  | none => false

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

  -- ## PLAN G1: the unpinned bounds-decide-`r` arm (`int_le_reif`)

  -- exhaustive tiny-domain oracle: 11^3 three-slot shapes plus the
  -- aliasing/out-of-range variants; no solution of `int_le_reif` is
  -- removed, no conflict is ever reported, and the two cause literals
  -- are false at every fitting assignment
  st ← st.check "G1 reif arm: exhaustive tiny-domain soundness (11^3 shapes)"
    armExhaustive

  -- the arm fires exactly on the intended separations, with the exact clause
  st ← st.check "G1 reif arm: mx_i ≤ mn_j pins r = true"
    (armEmitted [[vi 0, vi 1], [vi 1, vi 2], [Value.bool true, Value.bool false]] 0 1 2
      == some (posBool 2 true))
  st ← st.check "G1 reif arm: r=true clause is [r, ¬(i≤mx_i), j≤mn_j−1]"
    (match propLeReifB (armSt [[vi 0, vi 1], [vi 1, vi 2], [Value.bool true, Value.bool false]]) 0 1 2 with
      | .implied l rs =>
          l == posBool 2 true && rs.clause == [posBool 2 true, negLe 0 1, posLe 1 0]
      | _ => false)
  st ← st.check "G1 reif arm: mx_j < mn_i pins r = false"
    (armEmitted [[vi 2, vi 3], [vi 0, vi 1], [Value.bool true, Value.bool false]] 0 1 2
      == some (posBool 2 false))
  st ← st.check "G1 reif arm: r=false clause is [r, i≤mn_i−1, ¬(j≤mx_j)]"
    (match propLeReifB (armSt [[vi 2, vi 3], [vi 0, vi 1], [Value.bool true, Value.bool false]]) 0 1 2 with
      | .implied l rs =>
          l == posBool 2 false && rs.clause == [posBool 2 false, posLe 0 1, negLe 1 1]
      | _ => false)
  st ← st.check "G1 reif arm: no separation stays stable"
    (armEmitted [[vi 0, vi 2], [vi 1, vi 3], [Value.bool true, Value.bool false]] 0 1 2
      == none)

  -- the guards: pinned reif, mixed, empty, aliased and out-of-range slots
  st ← st.check "G1 reif arm: pinned r = true stays stable"
    (armEmitted [[vi 0, vi 1], [vi 1, vi 2], [Value.bool true]] 0 1 2 == none)
  st ← st.check "G1 reif arm: pinned r = false stays stable"
    (armEmitted [[vi 0, vi 1], [vi 1, vi 2], [Value.bool false]] 0 1 2 == none)
  st ← st.check "G1 reif arm: boolean operand stays stable"
    (armEmitted [[Value.bool true], [vi 1], [Value.bool true, Value.bool false]] 0 1 2
      == none)
  st ← st.check "G1 reif arm: mixed operand stays stable"
    (armEmitted [[vi 0, Value.bool true], [vi 1], [Value.bool true, Value.bool false]] 0 1 2
      == none)
  st ← st.check "G1 reif arm: empty operand stays stable"
    (armEmitted [[], [vi 1], [Value.bool true, Value.bool false]] 0 1 2 == none)
  st ← st.check "G1 reif arm: empty reif stays stable"
    (armEmitted [[vi 0, vi 1], [vi 1, vi 2], []] 0 1 2 == none)
  st ← st.check "G1 reif arm: aliased reif i = r stays stable"
    (armEmitted [[Value.bool true, Value.bool false], [vi 0, vi 1]] 0 1 0 == none)
  st ← st.check "G1 reif arm: aliased reif j = r stays stable"
    (armEmitted [[vi 0, vi 1], [Value.bool true, Value.bool false]] 0 1 1 == none)
  st ← st.check "G1 reif arm: out-of-range reif stays stable"
    (armEmitted [[vi 0, vi 1], [vi 1, vi 2]] 0 1 9 == none)
  st ← st.check "G1 reif arm: out-of-range operand stays stable"
    (armEmitted [[vi 0, vi 1], [Value.bool true, Value.bool false]] 0 5 1 == none)

  -- byte-identical pinned direction of the strengthened run function
  st ← st.check "G1 reif arm: pinned direction byte-identical (exhaustive)"
    armPinnedAgree

  -- the registered `.leReifSlot` propagator is the strengthened run
  st ← st.check "G1 reif arm: registered propagator fires the r=true pin"
    armRegisteredFires
  st ← st.check "G1 reif arm: registered propagator declares [i,j,r]"
    armRegisteredWatches

  -- closure demo (before/after on a fixture where the arm fires): the
  -- separating box loses no solution and its reif slot is pinned to one
  -- value; the unseparated box keeps both values
  let sepBox : List (List Value) :=
    [[vi 0, vi 1], [vi 2, vi 3], [Value.bool true, Value.bool false]]
  let sepClosed := armStep sepBox 0 1 2
  st ← st.check "G1 reif arm: separation closure keeps all solutions"
    (armSatCount sepClosed 0 1 2 == armSatCount sepBox 0 1 2 &&
      armSatCount sepBox 0 1 2 == 4)
  st ← st.check "G1 reif arm: separation closure pins the reif slot"
    ((sepClosed.getD 2 []).length == 1 && sepClosed.getD 2 [] == [Value.bool true])
  st ← st.check "G1 reif arm: no-separation box keeps both reif values"
    (((armStep [[vi 0, vi 2], [vi 1, vi 3], [Value.bool true, Value.bool false]]
      0 1 2).getD 2 []).length == 2)

  -- micro-benchmark (stable vs firing frames, arm + strengthened function)
  let (stableMs, fireMs) ← armBench 200000
  st ← st.check "G1 reif arm: micro-benchmark ran"
    (stableMs < 8000 && fireMs < 8000)
  -- ## PLAN G1-B: the `bool2int` channel (`bool2intSlot`)

  -- exhaustive tiny-domain oracle: no spurious conflict, implied heads
  -- true at every fitting solution, causes false at every fitting
  -- assignment, and one step preserves the solution count
  st ← st.check "G1-B channel: exhaustive tiny-domain soundness (12^2 shapes)"
    b2iExhaustive
  st ← st.check "G1-B channel: exhaustive solution-count preservation (12^2 shapes)"
    b2iPreserves

  -- the intended strength of the pinning rounds, with exact clauses
  st ← st.check "G1-B channel: pinned true removes the first non-1 view"
    (match propBool2intSlot (armSt [[Value.bool true], [vi 0, vi 2, Value.bool true]]) 0 1 with
      | .implied l rs => l == posNe 1 0 && rs.clause == [posNe 1 0, posBool 0 false]
      | _ => false)
  st ← st.check "G1-B channel: pinned false removes the first non-0 view"
    (match propBool2intSlot (armSt [[Value.bool false], [vi 1, vi 0]]) 0 1 with
      | .implied l rs => l == posNe 1 1 && rs.clause == [posNe 1 1, posBool 0 true]
      | _ => false)
  st ← st.check "G1-B channel: raw [.int 1] target pins the source true"
    (match propBool2intSlot (armSt [[Value.bool true, Value.bool false], [vi 1]]) 0 1 with
      | .implied l rs => l == posBool 0 true && rs.clause == [posBool 0 true, posNe 1 1]
      | _ => false)
  st ← st.check "G1-B channel: raw [.int 0] target pins the source false"
    (match propBool2intSlot (armSt [[Value.bool true, Value.bool false], [vi 0]]) 0 1 with
      | .implied l rs => l == posBool 0 false && rs.clause == [posBool 0 false, posNe 1 0]
      | _ => false)
  st ← st.check "G1-B channel: wide target above 1 reports the posLe conflict"
    (match propBool2intSlot (armSt [[Value.bool true, Value.bool false], [vi 2]]) 0 1 with
      | .conflict cc => cc == [posLe 1 1]
      | _ => false)
  st ← st.check "G1-B channel: negative target reports the negLe conflict"
    (match propBool2intSlot (armSt [[Value.bool true, Value.bool false], [vi (-2), vi (-1)]]) 0 1 with
      | .conflict cc => cc == [negLe 1 (-1)]
      | _ => false)
  st ← st.check "G1-B channel: both digits present, wide box stays stable"
    (b2iCheck [[Value.bool true, Value.bool false], [vi 0, vi 1]] 0 1 &&
      (match propBool2intSlot (armSt [[Value.bool true, Value.bool false], [vi 0, vi 1]]) 0 1 with
        | .stable => true
        | _ => false))

  -- the guards: aliasing, empty and out-of-range slots
  st ← st.check "G1-B channel: aliased source = target stays stable"
    (b2iCheck [[Value.bool true, Value.bool false]] 0 0 &&
      (match propBool2intSlot (armSt [[Value.bool true, Value.bool false]]) 0 0 with
        | .stable => true
        | _ => false))
  st ← st.check "G1-B channel: empty slots stay stable"
    (match propBool2intSlot (armSt [[], [vi 0]]) 0 1 with
      | .stable => true
      | _ => false)
  st ← st.check "G1-B channel: out-of-range target stays stable"
    (match propBool2intSlot (armSt [[vi 0], [vi 0]]) 0 5 with
      | .stable => true
      | _ => false)

  -- the registered `.bool2intSlot` propagator is the channel function
  st ← st.check "G1-B channel: registered propagator fires the posLe conflict"
    b2iRegisteredFires
  st ← st.check "G1-B channel: registered propagator pins the source from the target"
    b2iRegisteredTargetPin
  st ← st.check "G1-B channel: registered propagator declares [i,k]"
    b2iRegisteredWatches

  -- ## PLAN G1c: the constant-table element (`arrayIntElementSlot`)

  -- exhaustive tiny-domain oracle: no spurious conflict, implied heads
  -- true at every fitting solution, causes false at every fitting
  -- assignment, and one step preserves the solution count
  st ← st.check "G1c element: exhaustive tiny-domain soundness (15^2 shapes x 5 tables)"
    aieExhaustive
  st ← st.check "G1c element: exhaustive solution-count preservation (15^2 shapes x 5 tables)"
    aiePreserves
  st ← st.check "G1c element: integer-sweep solution-count preservation (11^2 shapes x 5 tables)"
    aiePreservesInt

  -- the intended strength of the four firing rounds, with exact clauses
  st ← st.check "G1c element: pinned index narrows the target through the entry"
    aieRegisteredFires
  st ← st.check "G1c element: pinned out-of-range index reports the conflict"
    aieRegisteredOutRange
  st ← st.check "G1c element: unpinned no-support index removal (int-only target)"
    aieRegisteredNoSupport
  st ← st.check "G1c element: pinned target removes the unsupported index"
    aieRegisteredPinVal
  st ← st.check "G1c element: unpinned out-of-range index unit removal"
    aieRegisteredOutRemoval

  -- the guards: aliasing, empty/out-of-range slots, fully supported state
  st ← st.check "G1c element: guard shapes stay stable"
    aieGuardsStable

  -- the registered `.arrayIntElementSlot` propagator is the element function
  st ← st.check "G1c element: registered propagator watches only its index and target slots"
    aieRegisteredWatches

  -- the compiled element shape reaches the family
  st ← st.check "G1c element: extract array_int_element with a literal table"
    (extractsTo (parse "var 1..3: i;\nvar 1..9: v;\n\
       constraint array_int_element(i, [4, 5, 6], v);\nsolve satisfy;")
      [.arrayIntElementSlot [4, 5, 6] 0 1])

  -- ## PLAN §3.3 item 1: the variable-table element
  -- (`arrayVarIntElementSlot`)

  st ← st.check "3.3 var-element: exhaustive tiny-domain soundness (6 tables x 10^4 shapes)"
    avieExhaustive
  st ← st.check "3.3 var-element: exhaustive solution-count preservation (6 tables x 10^4 shapes)"
    aviePreserves
  st ← st.check "3.3 var-element: pinned index narrows the target through the entry"
    avieRegisteredFires
  st ← st.check "3.3 var-element: pinned out-of-range index reports the conflict"
    avieRegisteredOutRange
  st ← st.check "3.3 var-element: pinned target removes the unsupported index"
    avieRegisteredPinVal
  st ← st.check "3.3 var-element: below-hull index removal through the two bounds"
    avieRegisteredBelow
  st ← st.check "3.3 var-element: target value absent from every table slot"
    avieRegisteredNoSupp
  st ← st.check "3.3 var-element: singleton entry hole removes the index"
    avieRegisteredSingle
  st ← st.check "3.3 var-element: guard shapes stay stable"
    avieGuardsStable
  st ← st.check "3.3 var-element: registered propagator watches i :: k :: is"
    avieRegisteredNoWatches

  -- ## PLAN §3.3 item 2: the variable-table Boolean element
  -- (`arrayVarBoolElementSlot`)

  st ← st.check "3.3 bool-element: exhaustive tiny-domain soundness (6 tables x 9^4 shapes)"
    avbeExhaustive
  st ← st.check "3.3 bool-element: exhaustive solution-count preservation (6 tables x 9^4 shapes)"
    avbePreserves
  st ← st.check "3.3 bool-element: pinned index narrows the target through the entry"
    avbeRegisteredFires
  st ← st.check "3.3 bool-element: pinned out-of-range index reports the conflict"
    avbeRegisteredOutRange
  st ← st.check "3.3 bool-element: pinned target removes the unsupported index"
    avbeRegisteredPinVal
  st ← st.check "3.3 bool-element: unpinned out-of-range index removes by the unit"
    avbeRegisteredOutUnpinned
  st ← st.check "3.3 bool-element: target value absent from every table slot"
    avbeRegisteredNoSupp
  st ← st.check "3.3 bool-element: empty target support reports the conflict"
    avbeRegisteredEmptySupport
  st ← st.check "3.3 bool-element: guard shapes stay stable"
    avbeGuardsStable
  st ← st.check "3.3 bool-element: registered propagator watches i :: k :: is"
    avbeRegisteredNoWatches

  -- ## PLAN G1d: the linLeReif r = false direction

  -- exhaustive tiny-domain oracle: implied heads true at fitting
  -- solutions, causes false at fitting assignments, solution-count
  -- preservation (6 coefficient/bound pairs x 11^3 shapes, both the
  -- bounds arm and the full delegation)
  st ← st.check "G1d linLeReif: exhaustive tiny-domain soundness (6 x 11^3 shapes)"
    lrExhaustive
  st ← st.check "G1d linLeReif: exhaustive solution-count preservation"
    lrPreserves

  -- the two new emissions, with exact clause shapes
  st ← st.check "G1d linLeReif: dual sumMin > b pins r = false with escapes"
    lrDualFires
  st ← st.check "G1d linLeReif: feasible minimum leaves the bounds arm stable"
    lrDualGuardStable

  -- the registered propagator fires both new emissions
  st ← st.check "G1d linLeReif: registered dual pin through propLinLeReifB"
    lrRegisteredDual
  st ← st.check "G1d linLeReif: registered pinned-false retained bound"
    lrRegisteredBound
  st ← st.check "G1d linLeReif: registered pinned-true delegation unchanged"
    lrRegisteredTrue
  st ← st.check "G1d linLeReif: registered propagator watches r :: is"
    lrRegisteredWatches

  -- ## PLAN G1e: the array-Boolean conjunction (`arrayBoolAndSlot`)

  -- exhaustive tiny-domain oracle: conflicts exclude every fitting
  -- solution, implied heads true at fitting solutions, causes false at
  -- fitting assignments, solution count preserved
  st ← st.check "G1e arrayBoolAnd: exhaustive tiny-domain soundness (7 lists x 9^3 shapes)"
    abaExhaustive
  st ← st.check "G1e arrayBoolAnd: exhaustive solution-count preservation"
    abaPreserves

  -- the four rounds and the empty-list case, with exact clauses
  st ← st.check "G1e arrayBoolAnd: all inputs pinned true pins the target"
    abaAllTrueFires
  st ← st.check "G1e arrayBoolAnd: pinned-false input forces the target false"
    abaPinFalseFires
  st ← st.check "G1e arrayBoolAnd: pinned-true target prunes the first input"
    abaKTrueFires
  st ← st.check "G1e arrayBoolAnd: Boolean-only singleton follows the target"
    abaSingleFires
  st ← st.check "G1e arrayBoolAnd: empty input list pins the target true"
    abaEmptyFires
  st ← st.check "G1e arrayBoolAnd: pinned-false input conflicts with a true target"
    abaConflictFires
  st ← st.check "G1e arrayBoolAnd: guard shapes stay stable"
    abaGuardsStable
  st ← st.check "G1e arrayBoolAnd: registered propagator fires, watches k :: is"
    abaRegisteredFires

  -- the compiled shape reaches the family
  st ← st.check "G1e arrayBoolAnd: extract array_bool_and over slot idents"
    (extractsTo (parse "var bool: p;
var bool: q;
var bool: r;
       constraint array_bool_and([p, q], r);
solve satisfy;")
      [.arrayBoolAndSlot [0, 1] 2])

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
  st ← st.check "P3: minSlot/maxSlot watch all three slots"
    msRegisteredWatches
  st ← st.check "P3: timesSlot watches all three slots"
    tsRegisteredWatches
  st ← st.check "extract: int_abs on two slots"
    (extractsTo (parse "var -3..3: x;\nvar 0..3: y;\n\
       constraint int_abs(x, y);\nsolve satisfy;") [.absSlot 0 1])
  st ← st.check "P3: absSlot/divGen/modGen watch their operand slots"
    adRegisteredWatches
  st ← st.check "P3: maxGen/minGen watch their named slots"
    genRegisteredWatches
  st ← st.check "P3: minPair/maxPair slot and propCheck footprints"
    pairRegisteredWatches
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

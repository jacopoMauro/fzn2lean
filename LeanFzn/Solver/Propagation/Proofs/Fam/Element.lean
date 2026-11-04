/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/Element.lean

Purpose:
  The LCG propagator and proof package for the constant-table element
  family `array_int_element` (`arrayIntElementSlot xs i k`), the PLAN G1c
  dedicated propagator:

  * pinned index (`i`'s domain the raw int singleton `[.int idx]`): an
    out-of-range table position is a conflict `[i ≠ idx]`; a defined entry
    `v` removes every target value whose integer view is not `v` (the
    falsified cause `i ≠ idx` explains the removal);
  * pinned target (`k`'s domain the raw int singleton `[.int v]`): every
    index whose table entry is not `v` (or is out of range) is removed
    (the falsified cause `k ≠ v`);
  * unpinned index: every index value with no table entry is removed by
    the unit clause `[i ≠ idx]`; when the target domain is integer-only,
    every index whose entry `v` is absent from the target domain is
    removed through `[i ≠ idx, k = v]`.

  Every emission is over the existing literal vocabulary (`posNe`/`negNe`
  heads), its clause is CONSTRAINT-VALID under the `arrayIntElementSlot`
  constraint alone (the true-literals half of `Reason.Valid`), and each
  non-pivot cause is falsified by the state's own domain shape (`FixExpl`
  for raw int singletons, `BoundsExpl`/`HolesExpl` for the missing-value
  cause). Guards: aliasing `i = k`, empty and out-of-range slots are
  `.stable`; non-`int` index/target values are left to the leaf check.

  The complete case split is `propArrayIntElement_cases`; the satisfaction
  views, clause-entailment lemmas and singleton-read bridges below are the
  leaves the consumer packages (`Propagators`, `Reason`, `BoxPropagators`,
  `FallbackFit`, the `Lcg*` files) consume.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fam.Bool: the shared `firstBadView`
    finder and its inversion lemmas, and (transitively) ConstFamilies'
    `slotInt_of_int_read` / `fits_*` reads and Encoding's literal
    evaluation lemmas.
  - LeanFzn.Solver.Propagation.Proofs.Fam.Lin: the integer-only domain
    guard `domsIntOnlyB` with its inversion `domsIntOnlyB_eq`.

DAG:
  Fam.Bool + Fam.Lin -> Fam.Element -> Proofs.Propagators
    (registration + safety triple) -> Reason / BoxPropagators / FallbackFit
    -> the Lcg* consumer arms.
-/

import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
import LeanFzn.Solver.Propagation.CompactDomain
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## PLAN G1c: the constant-table element propagator -/

/-- The pinned-target keep test: the table entry at `idx` is exactly `v`. -/
def aieEntryEqB (xs : List Int) (idx : Int) (v : Int) : Bool :=
  match valuesGet1 (xs.map Value.int) idx with
  | some (.int e) => decide (e = v)
  | _ => false

/-- The support keep test: the table entry at `idx` is present and lies in
    the target domain `kd`. -/
def aieSupportB (xs : List Int) (kd : List Value) (idx : Int) : Bool :=
  match valuesGet1 (xs.map Value.int) idx with
  | some (.int e) => valueMemB (.int e) kd
  | _ => true

/-- The pinned-target keep test with the table's `Value.int` view already
    materialized.  `aieEntryEqV (xs.map Value.int)` is definitionally
    `aieEntryEqB xs`, so the hoist changes no result. -/
def aieEntryEqV (xsV : List Value) (idx : Int) (v : Int) : Bool :=
  match valuesGet1 xsV idx with
  | some (.int e) => decide (e = v)
  | _ => false

theorem aieEntryEqV_map (xs : List Int) (idx v : Int) :
    aieEntryEqV (xs.map Value.int) idx v = aieEntryEqB xs idx v := rfl

/-- The support keep test with the table view hoisted: the propagator maps
    the constant table once per run instead of once per index probe. -/
def aieSupportV (xsV : List Value) (kd : List Value) (idx : Int) : Bool :=
  match valuesGet1 xsV idx with
  | some (.int e) => valueMemB (.int e) kd
  | _ => true

theorem aieSupportV_map (xs : List Int) (kd : List Value) (idx : Int) :
    aieSupportV (xs.map Value.int) kd idx = aieSupportB xs kd idx := rfl

/-- Compact membership on `Dom.ofList` is the legacy list membership.  This
    is the bridge that lets the support scan use a prebuilt compact target
    without changing the keep predicate. -/
theorem Dom.memBool_ofList (vs : List Value) (v : Value) :
    Dom.memBool (Dom.ofList vs) v = valueMemB v vs := by
  rw [Bool.eq_iff_iff, Dom.memBool_iff, Dom.enum_ofList, valueMemB_iff]

/-- Compact membership on the domain itself is the legacy list membership
    on its enumeration.  This is the bridge that lets the support scan read
    the target structurally, without materialising `Dom.enum` at all. -/
theorem Dom.memBool_enum (d : Dom) (v : Value) :
    Dom.memBool d v = valueMemB v (Dom.enum d) := by
  rw [Bool.eq_iff_iff, Dom.memBool_iff, valueMemB_iff]

/-- The support keep test against a prebuilt compact target domain.  The
    `S1` bridge: when `kd` is a contiguous run, `Dom.ofRange?` replaces the
    per-probe list membership with the compact one, and the result is
    unchanged. -/
def aieSupportDomV (xsV : List Value) (kd : Dom) (idx : Int) : Bool :=
  match valuesGet1 xsV idx with
  | some (.int e) => Dom.memBool kd (.int e)
  | _ => true

theorem aieSupportDomV_ofRange? {xsV : List Value} {kd : List Value} {d : Dom}
    (h : Dom.ofRange? kd = some d) (idx : Int) :
    aieSupportDomV xsV d idx = aieSupportV xsV kd idx := by
  unfold aieSupportDomV aieSupportV
  cases hv : valuesGet1 xsV idx with
  | none => rfl
  | some e =>
      cases e with
      | int z =>
          rw [Bool.eq_iff_iff, Dom.memBool_iff, valueMemB_iff, Dom.enum_ofRange? h]
      | bool b => rfl
      | setOfInt s => rfl
      | array a => rfl

/-- Compact membership on `Dom.ofList` is the legacy support test.  This is
    the bridge for the hoisted-target scan: the compact target is built once
    per propagator call, and each per-index test is `Dom.memBool`. -/
theorem aieSupportDomV_ofList (xsV : List Value) (kd : List Value) (idx : Int) :
    aieSupportDomV xsV (Dom.ofList kd) idx = aieSupportV xsV kd idx := by
  unfold aieSupportDomV aieSupportV
  cases hv : valuesGet1 xsV idx with
  | none => rfl
  | some e =>
      cases e with
      | int z => simp only [Dom.memBool_ofList]
      | bool b => rfl
      | setOfInt s => rfl
      | array a => rfl

/-- Function-level form for the `firstBadView` scan. -/
theorem aieSupportDomV_ofList_fun (xsV : List Value) (kd : List Value) :
    aieSupportDomV xsV (Dom.ofList kd) = aieSupportV xsV kd := by
  funext idx
  exact aieSupportDomV_ofList xsV kd idx

/-- The table view is already materialized at the call site, so the mapped
    form is the `aieSupportB` keep predicate. -/
theorem aieSupportDomV_ofList_map (xs : List Int) (kd : List Value) :
    aieSupportDomV (xs.map Value.int) (Dom.ofList kd) = aieSupportB xs kd := by
  funext idx
  rw [aieSupportDomV_ofList, aieSupportV_map]

/-- Structural membership on a domain is the support test on its
    enumeration: the target domain need not be materialised. -/
theorem aieSupportDomV_enum (xsV : List Value) (d : Dom) (idx : Int) :
    aieSupportDomV xsV d idx = aieSupportV xsV (Dom.enum d) idx := by
  unfold aieSupportDomV aieSupportV
  cases hv : valuesGet1 xsV idx with
  | none => rfl
  | some e =>
      cases e with
      | int z => simp only [Dom.memBool_enum]
      | bool b => rfl
      | setOfInt s => rfl
      | array a => rfl

theorem aieSupportDomV_enum_fun (xsV : List Value) (d : Dom) :
    aieSupportDomV xsV d = aieSupportV xsV (Dom.enum d) := by
  funext idx
  exact aieSupportDomV_enum xsV d idx

theorem aieSupportDomV_enum_map (xs : List Int) (d : Dom) :
    aieSupportDomV (xs.map Value.int) d = aieSupportB xs (Dom.enum d) := by
  funext idx
  rw [aieSupportDomV_enum, aieSupportV_map]

/-- Function-level form of the hoisted table view. -/
theorem aieSupportV_map_fun (xs : List Int) (kd : List Value) :
    aieSupportV (xs.map Value.int) kd = aieSupportB xs kd := by
  funext idx
  exact aieSupportV_map xs kd idx

/-- 1-based `Array` access, the twin of `valuesGet1`.  `Array.get?` is O(1)
    while `List.get?` is O(index), so hoisting the constant table to an
    `Array` once per propagator call removes the quadratic table scan. -/
def valuesGet1A (a : Array Value) (i : Int) : Option Value :=
  if 0 < i then a[i.toNat - 1]? else none

/-- The `Array` access is the list access on `toArray`. -/
theorem valuesGet1A_toArray (xs : List Value) (i : Int) :
    valuesGet1A xs.toArray i = valuesGet1 xs i := by
  unfold valuesGet1A valuesGet1
  split <;> simp [List.getElem?_toArray]

/-- The table lookup of the support scan.  `xa` is the hoisted `Array` view of
    the constant table when the scan is long enough to amortize it. -/
def aieLookup (xsV : List Value) (xa : Option (Array Value)) (idx : Int) :
    Option Value :=
  match xa with
  | some a => valuesGet1A a idx
  | none => valuesGet1 xsV idx

theorem aieLookup_none (xsV : List Value) (idx : Int) :
    aieLookup xsV none idx = valuesGet1 xsV idx := rfl

theorem aieLookup_array (xsV : List Value) (idx : Int) :
    aieLookup xsV (some xsV.toArray) idx = valuesGet1 xsV idx := by
  simp [aieLookup, valuesGet1A_toArray]

/-- The structural support test with the table lookup hoisted: the target is
    read as a `Dom` (no enumeration), and the per-index table probe goes
    through the `Array` view when it is available. -/
def aieSupportDomVArr (xsV : List Value) (xa : Option (Array Value))
    (kd : Dom) (idx : Int) : Bool :=
  match aieLookup xsV xa idx with
  | some (.int e) => Dom.memBool kd (.int e)
  | _ => true

theorem aieSupportDomVArr_none (xsV : List Value) (kd : Dom) :
    aieSupportDomVArr xsV none kd = aieSupportDomV xsV kd := rfl

theorem aieSupportDomVArr_array (xsV : List Value) (kd : Dom) :
    aieSupportDomVArr xsV (some xsV.toArray) kd = aieSupportDomV xsV kd := by
  funext idx
  unfold aieSupportDomVArr aieSupportDomV
  rw [aieLookup_array]


/-- The support scan's keep predicate with the table and the compact target
    both optional.  `xa`/`cd` are precomputed once per propagator call, so the
    per-index cost is only the `Option` match: the `Array` view removes the
    O(index) table walk and the compact target removes the O(|kd|) membership
    scan, both amortized over the whole scan. -/
def aieSupportCached (xsV : List Value) (xa : Option (Array Value))
    (kd : List Value) (cd : Option Dom) : Int → Bool :=
  fun idx =>
    match aieLookup xsV xa idx with
    | some (.int e) =>
        match cd with
        | some d => Dom.memBool d (.int e)
        | none => valueMemB (.int e) kd
    | _ => true

theorem aieSupportCached_plain (xsV : List Value) (kd : List Value) :
    aieSupportCached xsV none kd none = aieSupportV xsV kd := by
  funext idx
  rfl

theorem aieSupportCached_hoisted (xsV : List Value) (kd : List Value) :
    aieSupportCached xsV (some xsV.toArray) kd (some (Dom.ofList kd)) =
      aieSupportV xsV kd := by
  funext idx
  unfold aieSupportCached aieSupportV
  rw [aieLookup_array]
  cases hv : valuesGet1 xsV idx with
  | none => rfl
  | some e =>
      cases e with
      | int z => simp only [Dom.memBool_ofList]
      | bool b => rfl
      | setOfInt s => rfl
      | array a => rfl

theorem aieSupportCached_plain_map (xs : List Int) (kd : List Value) :
    aieSupportCached (xs.map Value.int) none kd none = aieSupportB xs kd := by
  rw [aieSupportCached_plain, aieSupportV_map_fun]

theorem aieSupportCached_hoisted_map (xs : List Int) (kd : List Value) :
    aieSupportCached (xs.map Value.int) (some (xs.map Value.int).toArray) kd
        (some (Dom.ofList kd)) = aieSupportB xs kd := by
  rw [aieSupportCached_hoisted, aieSupportV_map_fun]

/-- The out-of-range scan's keep predicate (`isSome` of the table entry), with
    the same optional `Array` table view. -/
def aieEntrySomeCached (xsV : List Value) (xa : Option (Array Value)) :
    Int → Bool :=
  fun idx => (aieLookup xsV xa idx).isSome

theorem aieEntrySomeCached_plain (xsV : List Value) :
    aieEntrySomeCached xsV none = fun idx => (valuesGet1 xsV idx).isSome := by
  funext idx
  rfl

theorem aieEntrySomeCached_array (xsV : List Value) :
    aieEntrySomeCached xsV (some xsV.toArray) =
      fun idx => (valuesGet1 xsV idx).isSome := by
  funext idx
  unfold aieEntrySomeCached
  rw [aieLookup_array]

theorem aieEntrySomeCached_plain_map (xs : List Int) :
    aieEntrySomeCached (xs.map Value.int) none =
      fun idx => (valuesGet1 (xs.map Value.int) idx).isSome :=
  aieEntrySomeCached_plain _

theorem aieEntrySomeCached_array_map (xs : List Int) :
    aieEntrySomeCached (xs.map Value.int) (some (xs.map Value.int).toArray) =
      fun idx => (valuesGet1 (xs.map Value.int) idx).isSome :=
  aieEntrySomeCached_array _

/-- The index-width gate, resolved once for the out-of-range scan: the hoisted
    `Array` view is the list scan decision for every index. -/
theorem aieEntrySomeCached_gate (xs : List Int) (di : List Value) :
    aieEntrySomeCached (xs.map Value.int)
        (if 64 < di.length then some (xs.map Value.int).toArray else none) =
      fun idx => (valuesGet1 (xs.map Value.int) idx).isSome := by
  by_cases hw : 64 < di.length
  · rw [if_pos hw, aieEntrySomeCached_array_map]
  · rw [if_neg hw, aieEntrySomeCached_plain_map]

/-- The same gate for the support scan: hoisting the table to an `Array` and
    the target to a `Dom` changes no support decision. -/
theorem aieSupportCached_gate (xs : List Int) (di kd : List Value) :
    aieSupportCached (xs.map Value.int)
        (if 64 < di.length then some (xs.map Value.int).toArray else none) kd
        (if 64 < di.length then some (Dom.ofList kd) else none) =
      aieSupportB xs kd := by
  by_cases hw : 64 < di.length
  · rw [if_pos hw, if_pos hw, aieSupportCached_hoisted_map]
  · rw [if_neg hw, if_neg hw, aieSupportCached_plain_map]

/-- The gate with the target kept structural and the table lookup hoisted:
    the optional compact `ofList` target is replaced by the domain itself,
    so the wide-target hot path never materialises `Dom.enum`. -/
theorem aieSupportCached_gate_general (xsV : List Value)
    (xa : Option (Array Value)) (di : List Value) (d : Dom) :
    aieSupportCached xsV xa (Dom.enum d)
        (if 64 < di.length then some (Dom.ofList (Dom.enum d)) else none) =
      aieSupportDomVArr xsV xa d := by
  by_cases hw : 64 < di.length
  · rw [if_pos hw]
    funext idx
    unfold aieSupportCached aieSupportDomVArr
    cases hl : aieLookup xsV xa idx with
    | none => rfl
    | some e =>
        cases e with
        | int z => simp only [Dom.enum_ofList, Dom.memBool_enum]
        | bool b => rfl
        | setOfInt s => rfl
        | array a => rfl
  · rw [if_neg hw]
    funext idx
    unfold aieSupportCached aieSupportDomVArr
    cases hl : aieLookup xsV xa idx with
    | none => rfl
    | some e =>
        cases e with
        | int z => simp only [Dom.memBool_enum]
        | bool b => rfl
        | setOfInt s => rfl
        | array a => rfl

/-- The target domain is a raw integer singleton.  Cardinality-gated: only
    a one-element domain is enumerated, so the wide-target hot path never
    materialises `Dom.enum`. -/
def domSingleInt? (d : Dom) : Option Int :=
  if d.card = 1 then
    match Dom.enum d with
    | [.int v] => some v
    | _ => none
  else none

theorem domSingleInt?_eq_some_iff (d : Dom) (v : Int) :
    domSingleInt? d = some v ↔ Dom.enum d = [.int v] := by
  unfold domSingleInt?
  by_cases hc : d.card = 1
  · rw [if_pos hc]
    cases h : Dom.enum d with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil => cases x <;> simp
        | cons y ys => simp
  · rw [if_neg hc]
    constructor
    · intro h; cases h
    · intro h
      have hcard : d.card = 1 := by
        rw [Dom.card_eq_length_enum, h]
        rfl
      exact absurd hcard hc

/-- The reference's `match Dom.enum d with | [.int v] => …` is the
    cardinality-gated singleton test. -/
theorem enum_match_domSingleInt? {α : Type} (d : Dom) (P : Int → α)
    (Q : α) :
    (match Dom.enum d with
     | [.int v] => P v
     | _ => Q) =
    (match domSingleInt? d with
     | some v => P v
     | none => Q) := by
  cases h : domSingleInt? d with
  | none =>
      have hne : ∀ v, Dom.enum d ≠ [.int v] := by
        intro v hv
        have hsome : domSingleInt? d = some v :=
          (domSingleInt?_eq_some_iff d v).mpr hv
        rw [h] at hsome
        cases hsome
      rw [show (match (none : Option Int) with
          | some v => P v
          | none => Q) = Q from rfl]
      split
      · next v hv => exact absurd hv (hne v)
      · rfl
  | some v =>
      rw [(domSingleInt?_eq_some_iff d v).mp h]

/-- The pinned-index arm's target removal: `posNe k w` with the pin escape
    `posNe i idx` as the falsified cause. -/
def aieResPinIdx (i k : Nat) (idx w : Int) : PropagationResult :=
  .implied (posNe k w) { clause := [posNe k w, posNe i idx] }

/-- The pinned-index conflict at an out-of-range table position. -/
def aieResPinBad (i : Nat) (idx : Int) : PropagationResult :=
  .conflict [posNe i idx]

/-- The unpinned out-of-range removal of an index value: the unit clause
    `[posNe i idx]`. -/
def aieResOut (i : Nat) (idx : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx] }

/-- The pinned-target removal of an index whose entry is not the pinned
    value, through the falsified cause `posNe k v`. -/
def aieResPinVal (i k : Nat) (idx v : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, posNe k v] }

/-- The unpinned no-support removal: the entry `v` at `idx` is absent from
    an integer-only target domain, explained by the falsified `k = v`. -/
def aieResNoSupp (i k : Nat) (idx v : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, negNe k v] }

/-- PLAN G1c: the explained propagator of `array_int_element` —
    `arrayIntElementSlot xs i k` (the constant table `xs`; `i` the 1-based
    index slot, `k` the element slot). Guarded rounds, in order:

    * aliasing (`i = k`), empty or out-of-range slots ⇒ `.stable`;
    * pinned index `[.int idx]`: an out-of-range position is the conflict
      `[i ≠ idx]`; a defined entry `v` removes the first target value with
      a different integer view (`posNe k w` through the pin escape);
    * pinned target `[.int v]`: removes the first index whose entry is not
      `v` or is out of range (`posNe i idx` through the falsified `k ≠ v`);
    * unpinned index: removes the first index with no table entry (unit
      `posNe i idx`); with an integer-only target domain, removes the
      first index whose entry `v` is missing from the target domain
      through the falsified `k = v` (`negNe k v`).

    Every emission's clause is over the existing vocabulary: `posNe` /
    `negNe` integer-removal literals on the index and target slots. -/
def propArrayIntElementV (st : State) (xsV : List Value) (i k : Nat) :
    PropagationResult :=
  if i = k then .stable
  else if (st.domains.getD i Dom.empty).isEmpty
      || (st.domains.getD k Dom.empty).isEmpty then .stable
  else
    match Dom.enum (st.domains.getD i Dom.empty) with
    | [.int idx] =>
        match valuesGet1 xsV idx with
        | none => aieResPinBad i idx
        | some (.int v) =>
            if valuesEqB (Dom.enum (st.domains.getD k Dom.empty)) [.int v] then .stable
            else
              match firstBadView (Dom.enum (st.domains.getD k Dom.empty))
                  (fun w => decide (w = v)) with
              | some w => aieResPinIdx i k idx w
              | none => .stable
        | some _ => .stable
    | _ =>
        match Dom.enum (st.domains.getD k Dom.empty) with
        | [.int v] =>
            match firstBadView (Dom.enum (st.domains.getD i Dom.empty))
                (aieEntryEqV xsV · v) with
            | some idx => aieResPinVal i k idx v
            | none => .stable
        | _ =>
            let di := Dom.enum (st.domains.getD i Dom.empty)
            let kd := Dom.enum (st.domains.getD k Dom.empty)
            let wideI := 64 < di.length
            let xa : Option (Array Value) := if wideI then some xsV.toArray else none
            match firstBadView di (aieEntrySomeCached xsV xa) with
            | some idx => aieResOut i idx
            | none =>
                if domsIntOnlyB st.domains [k] then
                  let cd : Option Dom :=
                    if wideI then some (Dom.ofList kd) else none
                  match firstBadView di (aieSupportCached xsV xa kd cd) with
                  | some idx =>
                      match valuesGet1 xsV idx with
                      | some (.int v) => aieResNoSupp i k idx v
                      | _ => .stable
                  | none => .stable
                else .stable

/-- Runtime twin of `propArrayIntElementV`: the index enumeration is built
    once, the target domain is read structurally (its enumeration is
    materialised only when the domain is a one-element singleton), and the
    single-slot integer-only guard is answered structurally. -/
def propArrayIntElementVFast (st : State) (xsV : List Value) (i k : Nat) :
    PropagationResult :=
  if i = k then .stable
  else if (st.domains.getD i Dom.empty).isEmpty
      || (st.domains.getD k Dom.empty).isEmpty then .stable
  else
    let di := Dom.enum (st.domains.getD i Dom.empty)
    let dkD := st.domains.getD k Dom.empty
    match di with
    | [.int idx] =>
        let dk := Dom.enum dkD
        match valuesGet1 xsV idx with
        | none => aieResPinBad i idx
        | some (.int v) =>
            if valuesEqB dk [.int v] then .stable
            else
              match firstBadView dk
                  (fun w => decide (w = v)) with
              | some w => aieResPinIdx i k idx w
              | none => .stable
        | some _ => .stable
    | _ =>
        match domSingleInt? dkD with
        | some v =>
            match firstBadView di
                (aieEntryEqV xsV · v) with
            | some idx => aieResPinVal i k idx v
            | none => .stable
        | none =>
            let wideI := 64 < di.length
            let xa : Option (Array Value) :=
              if wideI then some xsV.toArray else none
            match firstBadView di (aieEntrySomeCached xsV xa) with
            | some idx => aieResOut i idx
            | none =>
                if domsIntOnlyBFast st.domains [k] then
                  match firstBadView di (aieSupportDomVArr xsV xa dkD) with
                  | some idx =>
                      match valuesGet1 xsV idx with
                      | some (.int v) => aieResNoSupp i k idx v
                      | _ => .stable
                  | none => .stable
                else .stable

theorem propArrayIntElementVFast_eq (st : State) (xsV : List Value)
    (i k : Nat) :
    propArrayIntElementVFast st xsV i k =
      propArrayIntElementV st xsV i k := by
  unfold propArrayIntElementVFast propArrayIntElementV
  dsimp only
  rw [domsIntOnlyBFast_eq]
  simp only [enum_match_domSingleInt?]
  cases h : domSingleInt? (st.domains.getD k Dom.empty) with
  | some v => simp
  | none =>
      simp
      rw [aieSupportCached_gate_general]

attribute [implemented_by propArrayIntElementVFast]
  propArrayIntElementV

/-- The table view is materialized once per run: the two `firstBadView`
    loops otherwise rebuilt `xs.map Value.int` on every index probe (the
    measured dominant constant of the family on wide-table models). -/
def propArrayIntElement (st : State) (xs : List Int) (i k : Nat) :
    PropagationResult :=
  propArrayIntElementV st (xs.map Value.int) i k

/-- Runtime twin of the table-view entry point. -/
def propArrayIntElementFast (st : State) (xs : List Int) (i k : Nat) :
    PropagationResult :=
  propArrayIntElementVFast st (xs.map Value.int) i k

theorem propArrayIntElementFast_eq (st : State) (xs : List Int) (i k : Nat) :
    propArrayIntElementFast st xs i k =
      propArrayIntElement st xs i k := by
  unfold propArrayIntElementFast propArrayIntElement
  exact propArrayIntElementVFast_eq st (xs.map Value.int) i k

attribute [implemented_by propArrayIntElementFast] propArrayIntElement

/-! ### Locality of the run (PLAN P1) -/

/-- A nonempty `getD` read is in range (the out-of-range read is `[]`). -/
theorem lt_length_of_getD_ne_nil {l : List Domain} {k : Nat}
    (h : l.getD k Dom.empty ≠ Dom.empty) : k < l.length := by
  by_cases hk : k < l.length
  · exact hk
  · exfalso
    apply h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- The single-slot `domsIntOnlyB` guard reads only that slot's domain: equal
    `getD` reads give equal guards (an empty read makes both sides false;
    a nonempty read places the slot in range on both sides). -/
theorem domsIntOnlyB_singleton_congr {d1 d2 : List Domain} {k : Nat}
    (h : d1.getD k Dom.empty = d2.getD k Dom.empty) :
    domsIntOnlyB d1 [k] = domsIntOnlyB d2 [k] := by
  unfold domsIntOnlyB
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hne : d1.getD k Dom.empty = Dom.empty
  · have h2 : d2.getD k Dom.empty = Dom.empty := by rw [← h]; exact hne
    rw [hne, h2]
    simp [Dom.enum_empty]
  · have hk1 : k < d1.length := lt_length_of_getD_ne_nil hne
    have hk2 : k < d2.length := lt_length_of_getD_ne_nil (by rw [← h]; exact hne)
    rw [decide_eq_true_eq.mpr hk1, decide_eq_true_eq.mpr hk2, h]

/-- `propArrayIntElement` reads only the index and element slots (the table
    `xs` is a compile-time constant): equal domains at `i` and `k` give equal
    runs. -/
theorem propArrayIntElement_local {st1 st2 : State} {xs : List Int} {i k : Nat}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propArrayIntElement st1 xs i k = propArrayIntElement st2 xs i k := by
  unfold propArrayIntElement propArrayIntElementV
  simp only [hi, hk, domsIntOnlyB_singleton_congr hk]

/-! ### `valuesGet1` reads of a mapped constant table -/

/-- A `valuesGet1` read is a list member. -/
theorem aie_mem_of_valuesGet1_some {l : List Value} {i : Int} {v : Value}
    (h : valuesGet1 l i = some v) : v ∈ l := by
  unfold valuesGet1 at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

/-- Every `valuesGet1` read of `xs.map Value.int` carries an integer. -/
theorem aie_valuesGet1_map_int {xs : List Int} {i : Int} {v : Value}
    (h : valuesGet1 (xs.map Value.int) i = some v) : ∃ e : Int, v = .int e := by
  obtain ⟨x, -, hx⟩ := List.mem_map.mp (aie_mem_of_valuesGet1_some h)
  exact ⟨x, hx.symm⟩

/-! ### The keep tests and their inversions -/

/-- The `(· = v)` keep test's found view is not `v`. -/
theorem aie_firstBadView_eq_some {d : List Value} {v w : Int}
    (h : firstBadView d (fun w => decide (w = v)) = some w) : w ≠ v := by
  obtain ⟨-, -, -, hk⟩ := firstBadView_some h
  exact of_decide_eq_false hk

/-- The `isSome` keep test's found view has no table entry. -/
theorem aie_firstBadView_isSome_some {d : List Value} {xs : List Int} {idx : Int}
    (h : firstBadView d
      (fun idx => (valuesGet1 (xs.map Value.int) idx).isSome) = some idx) :
    valuesGet1 (xs.map Value.int) idx = none := by
  obtain ⟨-, -, -, hk⟩ := firstBadView_some h
  simpa using hk

/-- The entry-equality test's failure: the entry is missing or differs
    from `v`. -/
theorem aieEntryEqB_false {xs : List Int} {idx v : Int}
    (h : aieEntryEqB xs idx v = false) :
    valuesGet1 (xs.map Value.int) idx = none ∨
      ∃ e : Int, valuesGet1 (xs.map Value.int) idx = some (.int e) ∧ e ≠ v := by
  cases hg : valuesGet1 (xs.map Value.int) idx with
  | none => exact Or.inl rfl
  | some w =>
      obtain ⟨e, he⟩ := aie_valuesGet1_map_int (i := idx) (v := w) hg
      cases he
      refine Or.inr ⟨e, rfl, ?_⟩
      have h' : decide (e = v) = false := by
        unfold aieEntryEqB at h
        rw [hg] at h
        exact h
      exact of_decide_eq_false h'

/-- The entry-equality test's found view has an entry differing from
    `v` or none at all. -/
theorem aie_firstBadView_entryEqB_some {d : List Value} {xs : List Int} {v idx : Int}
    (h : firstBadView d (fun idx => aieEntryEqB xs idx v) = some idx) :
    valuesGet1 (xs.map Value.int) idx = none ∨
      ∃ e : Int, valuesGet1 (xs.map Value.int) idx = some (.int e) ∧ e ≠ v := by
  obtain ⟨-, -, -, hk⟩ := firstBadView_some h
  exact aieEntryEqB_false (by simpa using hk)

/-- The support test's found view has a defined entry outside the target
    domain. -/
theorem aie_firstBadView_supportB_some {d : List Value} {xs : List Int}
    {kd : List Value} {idx : Int}
    (h : firstBadView d (fun idx => aieSupportB xs kd idx) = some idx) :
    ∃ v : Int, valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
      valueMemB (.int v) kd = false := by
  obtain ⟨-, -, -, hk⟩ := firstBadView_some h
  have hk' : aieSupportB xs kd idx = false := hk
  cases hg : valuesGet1 (xs.map Value.int) idx with
  | none =>
      unfold aieSupportB at hk'
      rw [hg] at hk'
      cases hk'
  | some w =>
      obtain ⟨e, he⟩ := aie_valuesGet1_map_int (i := idx) (v := w) hg
      cases he
      refine ⟨e, rfl, ?_⟩
      unfold aieSupportB at hk'
      rw [hg] at hk'
      exact hk'

/-! ### Singleton-domain reads -/

/-- A fitting read of a raw singleton domain. -/
theorem aie_read_of_dom_singleton {st : State} {a : Assignment} {s : Nat}
    {v : Value} (hfit : Core.Assignment.Fits st.domains a)
    (hd : slotEnum st.domains s = [v]) : a[s]? = some v :=
  b2i_read_of_dom_singleton hfit hd

/-- A fitting read of a raw integer singleton has that integer view. -/
theorem aie_fits_slotInt {st : State} {a : Assignment} {s : Nat} {v : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hd : slotEnum st.domains s = [.int v]) : slotInt a s = some v :=
  slotInt_of_int_read (aie_read_of_dom_singleton hfit hd)

/-! ### The complete case split -/

/-- Complete case split of `propArrayIntElement`: `.stable`, the pinned-index
    out-of-range conflict, the pinned-index target removal, the pinned-target
    index removal, the unpinned out-of-range unit removal, or the unpinned
    no-support removal on an integer-only target domain. -/
theorem propArrayIntElement_cases (st : State) (xs : List Int) (i k : Nat) :
    propArrayIntElement st xs i k = .stable ∨
    (∃ idx : Int, slotEnum st.domains i = [.int idx] ∧
      valuesGet1 (xs.map Value.int) idx = none ∧
      propArrayIntElement st xs i k = aieResPinBad i idx) ∨
    (∃ idx v w : Int, slotEnum st.domains i = [.int idx] ∧
      valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
      firstBadView (slotEnum st.domains k) (fun w => decide (w = v)) = some w ∧
      propArrayIntElement st xs i k = aieResPinIdx i k idx w) ∨
    (∃ v idx : Int, slotEnum st.domains k = [.int v] ∧
      firstBadView (slotEnum st.domains i) (fun idx => aieEntryEqB xs idx v)
        = some idx ∧
      propArrayIntElement st xs i k = aieResPinVal i k idx v) ∨
    (∃ idx : Int, firstBadView (slotEnum st.domains i)
        (fun idx => (valuesGet1 (xs.map Value.int) idx).isSome) = some idx ∧
      propArrayIntElement st xs i k = aieResOut i idx) ∨
    (∃ idx v : Int, domsIntOnlyB st.domains [k] = true ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => aieSupportB xs (slotEnum st.domains k) idx) = some idx ∧
      valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
      propArrayIntElement st xs i k = aieResNoSupp i k idx v) := by
  unfold propArrayIntElement propArrayIntElementV
  by_cases halias : i = k
  · rw [if_pos halias]; exact Or.inl rfl
  · rw [if_neg halias]
    by_cases hemp : ((st.domains.getD i Dom.empty).isEmpty
        || (st.domains.getD k Dom.empty).isEmpty) = true
    · rw [if_pos hemp]; exact Or.inl rfl
    · rw [if_neg hemp]
      split
      · next idx hidx =>
        split
        · next hnone =>
            exact Or.inr (Or.inl ⟨idx, hidx, hnone, rfl⟩)
        · next v hent =>
            by_cases hpin : valuesEqB (Dom.enum (st.domains.getD k Dom.empty)) [.int v] = true
            · rw [if_pos hpin]; exact Or.inl rfl
            · rw [if_neg hpin]
              split
              · next w hfb =>
                  exact Or.inr (Or.inr (Or.inl
                    ⟨idx, v, w, hidx, hent, hfb, rfl⟩))
              · next => exact Or.inl rfl
        · next => exact Or.inl rfl
      · next =>
        split
        · next v hk =>
            split
            · next idx hfb =>
                exact Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨v, idx, hk, hfb, rfl⟩)))
            · next => exact Or.inl rfl
        · next =>
            dsimp only
            rw [aieEntrySomeCached_gate]
            split
            · next idx hfb =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨idx, hfb, rfl⟩))))
            · next =>
                by_cases hg : domsIntOnlyB st.domains [k] = true
                · rw [if_pos hg]
                  rw [aieSupportCached_gate]
                  split
                  · next idx hfb =>
                      split
                      · next v hent =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            ⟨idx, v, hg, hfb, hent, rfl⟩))))
                      · next => exact Or.inl rfl
                  · next => exact Or.inl rfl
                · rw [if_neg hg]; exact Or.inl rfl

/-! ### The constraint's reads and literal evaluations -/

/-- The `arrayIntElementSlot` semantics at the reads. -/
theorem arrayIntElement_views {a : Assignment} {xs : List Int} {i k : Nat}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) :
    ∃ idx e : Int, a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
      valuesGet1 (xs.map Value.int) idx = some (.int e) := h

/-- The index slot's integer view at a solution. -/
theorem arrayIntElement_slotInt_i {a : Assignment} {xs : List Int} {i k : Nat}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) :
    ∃ idx : Int, slotInt a i = some idx := by
  obtain ⟨idx, -, hi, -⟩ := arrayIntElement_views h
  exact ⟨idx, slotInt_of_int_read hi⟩

/-- The element slot's integer view at a solution. -/
theorem arrayIntElement_slotInt_k {a : Assignment} {xs : List Int} {i k : Nat}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) :
    ∃ e : Int, slotInt a k = some e := by
  obtain ⟨-, e, -, hk, -⟩ := arrayIntElement_views h
  exact ⟨e, slotInt_of_int_read hk⟩

/-- A fitting membership read. -/
theorem aie_fits_mem {st : State} {a : Assignment} {s : Nat} {v : Value}
    (hfit : Core.Assignment.Fits st.domains a) (h : a[s]? = some v) :
    v ∈ st.domains.getD s Dom.empty := hfit.2 s v h

/-- A removal literal holds when the slot's view differs. -/
theorem aie_posNe_eval_true {a : Assignment} {s : Nat} {v p : Int}
    (h : slotInt a s = some p) (hp : p ≠ v) :
    (posNe s v).eval a = some true :=
  (eval_posNe_iff a s v).mpr ⟨p, h, hp⟩

/-- The negation-removal literal holds when the slot's view matches. -/
theorem aie_negNe_eval_true {a : Assignment} {s : Nat} {v p : Int}
    (h : slotInt a s = some p) (hp : p = v) :
    (negNe s v).eval a = some true :=
  (eval_negNe_iff a s v).mpr ⟨p, h, hp⟩

/-! ### Clause entailment at solutions (the reason side) -/

/-- The out-of-range clause carries a true literal at every solution of
    the constraint. -/
theorem aieResOut_entailed {a : Assignment} {xs : List Int} {i k : Nat}
    {idx : Int}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hnone : valuesGet1 (xs.map Value.int) idx = none) :
    ∃ l ∈ [posNe i idx], l.eval a = some true := by
  obtain ⟨idx', e, hi, -, hent⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rw [hent] at hnone
    cases hnone
  · exact ⟨posNe i idx, List.mem_singleton_self _,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidxe⟩

/-- The pinned-index removal's clause carries a true literal at every
    solution of the constraint. -/
theorem aieResPinIdx_entailed {a : Assignment} {xs : List Int} {i k : Nat}
    {idx v w : Int}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v))
    (hw : w ≠ v) :
    ∃ l ∈ [posNe k w, posNe i idx], l.eval a = some true := by
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rw [hent] at hent'
    have hve : v = e := Value.int.inj (Option.some.inj hent')
    exact ⟨posNe k w, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hk)
        (fun hwe => hw (hve.trans hwe).symm)⟩
  · exact ⟨posNe i idx, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      aie_posNe_eval_true (slotInt_of_int_read hi) hidxe⟩

/-- The pinned-target removal's clause carries a true literal at every
    solution of the constraint. -/
theorem aieResPinVal_entailed {a : Assignment} {xs : List Int} {i k : Nat}
    {idx v : Int}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hbad : valuesGet1 (xs.map Value.int) idx = none ∨
      ∃ e : Int, valuesGet1 (xs.map Value.int) idx = some (.int e) ∧ e ≠ v) :
    ∃ l ∈ [posNe i idx, posNe k v], l.eval a = some true := by
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rcases hbad with hnone | ⟨e', hent, hev⟩
    · rw [hent'] at hnone
      cases hnone
    · rw [hent'] at hent
      have hee : e = e' := Value.int.inj (Option.some.inj hent)
      exact ⟨posNe k v, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        aie_posNe_eval_true (slotInt_of_int_read hk)
          (fun hev' => hev (hee ▸ hev'))⟩
  · exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidxe⟩

/-- The no-support removal's clause carries a true literal at every
    solution of the constraint. -/
theorem aieResNoSupp_entailed {a : Assignment} {xs : List Int} {i k : Nat}
    {idx v : Int}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v)) :
    ∃ l ∈ [posNe i idx, negNe k v], l.eval a = some true := by
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rw [hent] at hent'
    have hev : e = v := Value.int.inj (Option.some.inj hent'.symm)
    exact ⟨negNe k v, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      aie_negNe_eval_true (slotInt_of_int_read hk) hev⟩
  · exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidxe⟩

/-! ### State-side exclusions and fitting pivot truths -/

/-- The pinned-index out-of-range conflict excludes every fitting solution. -/
theorem aie_pinBad_excluded {st : State} {a : Assignment} {xs : List Int}
    {i k : Nat} {idx : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (hnone : valuesGet1 (xs.map Value.int) idx = none)
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) : False := by
  obtain ⟨idx', e, hi, -, hent⟩ := arrayIntElement_views h
  have hread : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  have hidx' : idx' = idx :=
    (Value.int.inj (Option.some.inj (hread.symm.trans hi))).symm
  rw [hidx'] at hent
  rw [hent] at hnone
  cases hnone

/-- The pinned-index target removal's pivot is true at every fitting
    solution. -/
theorem aie_posNe_k_pinIdx_true {st : State} {a : Assignment} {xs : List Int}
    {i k : Nat} {idx v w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v))
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hw : w ≠ v) :
    (posNe k w).eval a = some true := by
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views h
  have hread : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  have hidx' : idx' = idx :=
    (Value.int.inj (Option.some.inj (hread.symm.trans hi))).symm
  rw [hidx'] at hent'
  have hev : e = v := Value.int.inj (Option.some.inj (hent'.symm.trans hent))
  exact aie_posNe_eval_true (slotInt_of_int_read hk)
    (fun hwe => hw (hev.symm.trans hwe).symm)

/-- The pinned-target index removal's pivot is true at every fitting
    solution. -/
theorem aie_posNe_i_pinVal_true {st : State} {a : Assignment} {xs : List Int}
    {i k : Nat} {idx v : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hk : slotEnum st.domains k = [.int v])
    (hbad : valuesGet1 (xs.map Value.int) idx = none ∨
      ∃ e : Int, valuesGet1 (xs.map Value.int) idx = some (.int e) ∧ e ≠ v)
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, hi, hk', hent⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    have hke : e = v := by
      have hkread : slotInt a k = some v := aie_fits_slotInt hfit hk
      rw [slotInt_of_int_read hk'] at hkread
      exact Option.some.inj hkread
    rcases hbad with hnone | ⟨e', hent', hev⟩
    · rw [hent] at hnone
      cases hnone
    · rw [hent] at hent'
      have hee : e = e' := Value.int.inj (Option.some.inj hent')
      exact absurd ((hke ▸ hee).symm) hev
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidxe

/-- The unpinned out-of-range removal's pivot is true at every solution
    of the constraint. -/
theorem aie_posNe_i_out_true {a : Assignment} {xs : List Int} {i k : Nat}
    {idx : Int}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a)
    (hnone : valuesGet1 (xs.map Value.int) idx = none) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, hi, -, hent⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rw [hent] at hnone
    cases hnone
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidxe

/-- The no-support removal's pivot is true at every fitting solution. -/
theorem aie_posNe_i_noSupp_true {st : State} {a : Assignment} {xs : List Int}
    {i k : Nat} {idx v : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hvm : valueMemB (.int v) (slotEnum st.domains k) = false)
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v))
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy a) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views h
  by_cases hidxe : idx' = idx
  · subst hidxe
    rw [hent] at hent'
    have hev : v = e := Value.int.inj (Option.some.inj hent')
    have hmem : (.int e : Value) ∈ st.domains.getD k Dom.empty :=
      aie_fits_mem hfit hk
    have hmemv : (.int v : Value) ∈ st.domains.getD k Dom.empty := by
      rw [hev]
      exact hmem
    have hmemE : (.int v : Value) ∈ slotEnum st.domains k := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemv
    have htrue : valueMemB (.int v) (slotEnum st.domains k) = true :=
      valueMemB_iff.mpr hmemE
    rw [hvm] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidxe

/-! ### Literal normalization -/

/-- Normalization is the identity on positive removal literals. -/
theorem posNe_norm (s : Nat) (k : Int) : (posNe s k).norm = posNe s k :=
  rfl

/-- Normalization is the identity on negative removal literals. -/
theorem negNe_norm (s : Nat) (k : Int) : (negNe s k).norm = negNe s k :=
  rfl

end LeanFzn.Solver.Propagation

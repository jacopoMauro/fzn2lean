/-
File: LeanFzn/Solver/Propagation/CompactDomain.lean

Purpose (D2 stages 1–3; S1 makes this the runtime domain):
  The compact finite-domain representation `Dom` for the approved D2
  migration (D0-domain-design.md, D1 go-ahead recorded in PLAN.md
  "Owner decision recorded 2026-10-17"), together with its denotation
  `Dom.enum`, its canonicality invariant `Dom.WF`, the constructor
  `Dom.ofList` and the basic operations with their refinement proofs.
  Stage 2 adds the interval-with-holes variant, the `Literal` filter
  (`filterLit`/`filterLitKeep`), the `SlotSum`-shaped query summary
  with its conservation law, and (in the companion module
  `CompactDomainBridges`) the positional `filterSlots`/`filterFrame`/
  `Frame.mass` bridges.

  S1 makes `LeanFzn.Solver.Core.Domain` an alias of `Dom`; this module
  is now the runtime representation layer consumed by the integration
  stages (D0 §5.3 S1-S7).

Representation (D0 §3.4, adapted):
  * `Rep.small isBool offset bits` - a 64-bit bitset over the window
    `offset .. offset + 63`: `isBool = false` denotes the integers
    `offset + k` whose bit `k` is set (D0's bool/indexed-int case);
    `isBool = true` denotes `.bool false`/`.bool true` for bits 0/1
    (the offset is ignored by the denotation and forced to 0 by `WF`;
    the tag is what keeps `Value.bool` from being conflated with
    `Value.int`).  At most 64 values, exact cardinality by popcount.
  * `Rep.holes lo hi hs` - the integers of `[lo, hi]` minus the hole
    list `hs` (stage 2).  `hs` is a `List Int` (D0 sketched
    `Array Int`; the list was chosen so that the canonicality proofs
    reuse the `List` induction and `Pairwise`/`Nodup` machinery of the
    rest of this file; the compiler stage may switch the field to
    `Array` behind the same denotation once the proofs are replayed).
    The canonical form (`WF`) has sorted, distinct, strictly interior
    holes, a span above 64, and at most a quarter of the span missing;
    `enum` still materializes the interval only when consumed.
  * `Rep.general vs` - the existing `List Value`, order and duplicates
    preserved, for everything the canonical forms do not cover
    (non-int/bool values, duplicates, unordered, sparse-over-wide or
    reversed-range lists).

Denotation relation (D0 §2):
  * `enum : Dom -> List Value` is the order- and multiplicity-preserving
    enumeration; `(D2)` is `denote := enum` by definition.
  * `memBool_iff` is `(D1)`; `enum_ofList` is the round trip
    `enum (ofList l) = l` for every list (exact, not merely a
    permutation), which makes every `ofList`-defined operation commute
    with its list counterpart by construction (`(D3)`).
  * `WF` is the canonicality invariant (`WF` docstring below): every
    `ofList` output satisfies it (`WF_ofList`), on `WF` inputs the
    canonicalization is a retraction (`ofList_enum_eq_of_WF`), and two
    `WF` values with the same enumeration are equal
    (`enum_injective_of_WF`).

Imports:
  * stage 1 (representation core; D0 §5.1 wants only the shared `Value`):
    LeanFzn.Semantics.ValueEquality (`value_eqB_iff`, `value_eqB_refl`)
    and LeanFzn.Semantics.Globals.Common (`valueMemB`, `valueMemB_iff`),
    plus LeanFzn.Solver.Core.Semantics (`Domain`, `Assignment`, `Fits`)
    and LeanFzn.Solver.Core.Enumerate (`allAssigns`).
  * stage 2 (literal filter; new): LeanFzn.Solver.Propagation.
    LiteralEval (via `Operations`) supplies `Literal`,
    `Literal.valueHolds` and the shared `Value.intView` that the wave-2
    `SlotSum` summaries are built from.  `FrameFilter` now sits ABOVE
    this module: it calls `Dom.filterLit`/`Dom.filterLitKeep`, so the
    positional `filterSlots`/`filterFrame`/`Frame.mass` bridges moved
    to the companion `CompactDomainBridges.lean` (which imports both).

DAG:
  LeanFzn.Semantics.ValueEquality + LeanFzn.Semantics.Globals.Common +
  LeanFzn.Solver.Core.Semantics + LeanFzn.Solver.Core.Enumerate +
  LeanFzn.Solver.Propagation.LiteralEval
    -> LeanFzn.Solver.Propagation.CompactDomain
    -> LeanFzn.Solver.Propagation.FrameFilter
    -> LeanFzn.Solver.Propagation.CompactDomainBridges
    -> (S1/S2/S3 integration: Core.Domain alias, Pruning, families)

Obligation ledger for D0's 26 obligations is appended as a comment
block at the end of this file.
-/

import LeanFzn.Semantics.ValueEquality
import LeanFzn.Semantics.Globals.Common
import LeanFzn.Solver.Core.Semantics
import LeanFzn.Solver.Core.Enumerate
import LeanFzn.Solver.Propagation.LiteralEval
import LeanFzn.Solver.Core.CompactDomain
namespace LeanFzn.Solver.Propagation

open LeanFzn.Semantics LeanFzn.Solver.Core

namespace Dom

theorem valueIntView_eq_value_intView (v : Value) : valueIntView v = Value.intView v := rfl

theorem domInts_eq_intView (d : Dom) :
    domInts d = (enum d).filterMap Value.intView := by
  unfold domInts
  exact filterMap_congr (fun v _ => valueIntView_eq_value_intView v)

/-! ### Boolean presence and the `SlotSum`-shaped summary

The wave-2 `SlotSum` (`DbScanIndex.lean`) collects, in one fold over a
legacy domain: the integer extremes of the `Value.intView` image and
the two Boolean memberships.  The queries below are the `Dom`-level
versions; `summary_conservation` states that they are the summary of
the enumeration (the fold's mathematical content), and the compact
cases answer them without enumerating. -/

/-- `.bool true` occurs in the enumeration; O(1) on the compact cases. -/
def hasTrueB (d : Dom) : Bool :=
  match d.rep with
  | .small true _ bits => bits.toNat.testBit 1
  | .small false _ _ => false
  | .holes .. => false
  | .general vs => vs.any fun v => v.eqB (.bool true)

/-- `.bool false` occurs in the enumeration; O(1) on the compact cases. -/
def hasFalseB (d : Dom) : Bool :=
  match d.rep with
  | .small true _ bits => bits.toNat.testBit 0
  | .small false _ _ => false
  | .holes .. => false
  | .general vs => vs.any fun v => v.eqB (.bool false)

theorem any_eqB_true_iff {xs : List Value} {x : Value} :
    xs.any (fun v => v.eqB x) = true ↔ x ∈ xs := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hv, heq⟩
    rw [Evaluation.value_eqB_iff] at heq
    exact heq ▸ hv
  · intro h
    exact ⟨x, h, Evaluation.value_eqB_refl x⟩

theorem hasTrueB_iff (d : Dom) : hasTrueB d = true ↔ (.bool true : Value) ∈ enum d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              show bits.toNat.testBit 1 = true ↔ (.bool true : Value) ∈ smallBools bits
              simpa using (mem_smallBools_bool bits true).symm
          | false =>
              refine ⟨fun h => absurd h (by simp [hasTrueB]), fun h => ?_⟩
              obtain ⟨i, -, heq⟩ := List.mem_map.mp h
              cases heq
      | holes lo hi hs =>
          refine ⟨fun h => absurd h (by simp [hasTrueB]), fun h => ?_⟩
          obtain ⟨i, heq⟩ := eq_int_of_mem_holes_enum h
          cases heq
      | general vs =>
          show vs.any (fun v => v.eqB (.bool true)) = true ↔ (.bool true : Value) ∈ vs
          exact any_eqB_true_iff

theorem hasFalseB_iff (d : Dom) : hasFalseB d = true ↔ (.bool false : Value) ∈ enum d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              show bits.toNat.testBit 0 = true ↔ (.bool false : Value) ∈ smallBools bits
              simpa using (mem_smallBools_bool bits false).symm
          | false =>
              refine ⟨fun h => absurd h (by simp [hasFalseB]), fun h => ?_⟩
              obtain ⟨i, -, heq⟩ := List.mem_map.mp h
              cases heq
      | holes lo hi hs =>
          refine ⟨fun h => absurd h (by simp [hasFalseB]), fun h => ?_⟩
          obtain ⟨i, heq⟩ := eq_int_of_mem_holes_enum h
          cases heq
      | general vs =>
          show vs.any (fun v => v.eqB (.bool false)) = true ↔ (.bool false : Value) ∈ vs
          exact any_eqB_true_iff

theorem hasTrueB_eq_any (d : Dom) :
    hasTrueB d = (enum d).any (fun v => v.eqB (.bool true)) := by
  rw [Bool.eq_iff_iff, hasTrueB_iff, any_eqB_true_iff]

theorem hasFalseB_eq_any (d : Dom) :
    hasFalseB d = (enum d).any (fun v => v.eqB (.bool false)) := by
  rw [Bool.eq_iff_iff, hasFalseB_iff, any_eqB_true_iff]

theorem hasTrueB_small_true (off : Int) (bits : UInt64) :
    hasTrueB ⟨.small true off bits⟩ = bits.toNat.testBit 1 := rfl

theorem hasFalseB_small_true (off : Int) (bits : UInt64) :
    hasFalseB ⟨.small true off bits⟩ = bits.toNat.testBit 0 := rfl

theorem hasTrueB_small_false (off : Int) (bits : UInt64) :
    hasTrueB ⟨.small false off bits⟩ = false := rfl

theorem hasFalseB_small_false (off : Int) (bits : UInt64) :
    hasFalseB ⟨.small false off bits⟩ = false := rfl

theorem hasTrueB_holes (lo hi : Int) (hs : List Int) :
    hasTrueB ⟨.holes lo hi hs⟩ = false := rfl

theorem hasFalseB_holes (lo hi : Int) (hs : List Int) :
    hasFalseB ⟨.holes lo hi hs⟩ = false := rfl

/-- The four-field summary of a domain, mirroring
    `LeanFzn.Solver.Propagation.SlotSum` (`DbScanIndex.lean`). -/
structure Summary where
  minInt : Option Int
  maxInt : Option Int
  hasTrue : Bool
  hasFalse : Bool
  deriving Repr

/-- The direct query summary of a domain (no enumeration on the compact
    cases; the hole bounds read the endpoints). -/
def summary (d : Dom) : Summary := ⟨minInt? d, maxInt? d, hasTrueB d, hasFalseB d⟩

/-- **Conservation (`SlotSum` fields)**: the direct queries equal the
    summary of the enumeration — the `min`/`max` of the
    `Value.intView` image and the two Boolean memberships (the
    mathematical content of the `SlotSum.step` fold). -/
theorem summary_conservation (d : Dom) :
    (summary d).minInt = (domInts d).min? ∧
      (summary d).maxInt = (domInts d).max? ∧
      (summary d).hasTrue = (enum d).any (fun v => v.eqB (.bool true)) ∧
      (summary d).hasFalse = (enum d).any (fun v => v.eqB (.bool false)) :=
  ⟨minInt?_eq_domInts_min d, maxInt?_eq_domInts_max d, hasTrueB_eq_any d,
    hasFalseB_eq_any d⟩

/-! ### Refinement bridges to the legacy `List Value` vocabulary -/

/-- The legacy list domain of a compact domain (D0 `Frame.denote` lane). -/
def toDomain (d : Dom) : List Value := enum d

theorem toDomain_eq_enum (d : Dom) : toDomain d = enum d := rfl

/-- Canonicalize a legacy list domain. -/
def ofDomain (l : List Value) : Dom := ofList l

theorem enum_ofDomain (l : List Value) : enum (ofDomain l) = l := enum_ofList l

theorem enum_ofDomain_singleton (v : Value) : enum (ofDomain [v]) = [v] := enum_ofList [v]

theorem toDomain_empty : toDomain empty = [] := enum_empty

/-- Positional access commutes with the bridge (`enum_getD` lane). -/
theorem enum_getD (d : Dom) (i : Nat) (fallback : Value) :
    (toDomain d).getD i fallback = (enum d).getD i fallback := rfl

/-- Optional positional access commutes with the bridge. -/
theorem enum_getElem? (d : Dom) (i : Nat) : (toDomain d)[i]? = (enum d)[i]? := rfl

/-- `valueMemB` on the legacy view decides `memBool`. -/
theorem valueMemB_toDomain (d : Dom) (v : Value) :
    Globals.valueMemB (toDomain d) v = true ↔ memBool d v = true := by
  rw [Globals.valueMemB_iff]
  constructor
  · rintro ⟨x, hx, heq⟩
    rw [Evaluation.value_eqB_iff] at heq
    exact (memBool_iff d v).mpr (heq ▸ hx)
  · intro h
    exact ⟨v, (memBool_iff d v).mp h, Evaluation.value_eqB_refl v⟩

/-- Slot-wise fits for compact domains: the `memBool` reading of
    `Assignment.Fits` on the `toDomain` view. -/
def FitsD (doms : List Dom) (a : Assignment) : Prop :=
  a.length = doms.length ∧
    ∀ (i : Nat) (v : Value) (d : Dom),
      a[i]? = some v → doms[i]? = some d → memBool d v = true

theorem fits_toDomain_iff {doms : List Dom} {a : Assignment} :
    Assignment.Fits (doms.map toDomain) a ↔ FitsD doms a := by
  unfold FitsD Assignment.Fits
  constructor
  · rintro ⟨hlen, hmem⟩
    rw [List.length_map] at hlen
    refine ⟨hlen, fun i v d hv hd => ?_⟩
    have hm := hmem i v hv
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hd] at hm
    exact (memBool_iff d v).mpr hm
  · rintro ⟨hlen, hmem⟩
    refine ⟨?_, fun i v hv => ?_⟩
    · rw [List.length_map]; exact hlen
    · rw [List.getD_eq_getElem?_getD]
      cases hd : doms[i]? with
      | none =>
          have h1 : doms.length ≤ i := List.getElem?_eq_none_iff.mp hd
          obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hv
          omega
      | some d =>
          simp only [List.getElem?_map, hd, Option.map_some]
          exact (memBool_iff d v).mp (hmem i v d hv hd)

/-- Cardinality-based mass of a list of compact domains. -/
def massD (doms : List Dom) : Nat := (doms.map card).sum

theorem massD_eq_map_length (doms : List Dom) :
    massD doms = ((doms.map toDomain).map List.length).sum := by
  unfold massD
  induction doms with
  | nil => rfl
  | cons d t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [card_eq_length_enum, ← toDomain_eq_enum, ih]

/-- The `Frame.domains`-style projection with compact remaining
    domains: chosen slots contribute singleton lists, exactly as
    `LeanFzn.Solver.Propagation.Frame.domains` does. -/
def frameDomainsD (chosen : Assignment) (doms : List Dom) : List (List Value) :=
  chosen.map (fun v => [v]) ++ doms.map toDomain

theorem frameDomainsD_enum (chosen : Assignment) (doms : List Dom) :
    (frameDomainsD chosen doms).map (fun l => enum (ofDomain l)) =
      chosen.map (fun v => [v]) ++ doms.map enum := by
  unfold frameDomainsD
  rw [List.map_append]
  congr 1
  · induction chosen with
    | nil => rfl
    | cons v t ih =>
        simp only [List.map_cons] at ih ⊢
        rw [enum_ofDomain_singleton, ih]
  · induction doms with
    | nil => rfl
    | cons d t ih =>
        simp only [List.map_cons] at ih ⊢
        rw [enum_ofDomain, ih]
        rfl

/-- The assignment enumeration commutes with the bridge. -/
theorem allAssigns_toDomain (doms : List Dom) :
    allAssigns (doms.map toDomain) = allAssigns (doms.map enum) := rfl

theorem allAssigns_frameDomainsD (chosen : Assignment) (doms : List Dom) :
    allAssigns (frameDomainsD chosen doms) =
      allAssigns (chosen.map (fun v => [v]) ++ doms.map enum) := rfl

/-- The frame-level slot access of the migration consumers
    (`(Frame.domains f).getD i []`). -/
theorem frameDomainsD_getD (chosen : Assignment) (doms : List Dom) (i : Nat) :
    (frameDomainsD chosen doms).getD i [] =
      (chosen.map (fun v => [v]) ++ doms.map enum).getD i [] := rfl

/-! ### Shape facts used by the route gates -/

/-- The `gateOk` shape test: every value has an integer view. -/
def intViewableB (d : Dom) : Bool :=
  match d.rep with
  | .small .. => true
  | .holes .. => true
  | .general vs => vs.all fun v => (valueIntView v).isSome

theorem intViewableB_iff (d : Dom) :
    intViewableB d = true ↔ ∀ v ∈ enum d, valueIntView v ≠ none := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              refine ⟨fun _ v hv => ?_, fun _ => rfl⟩
              obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
              simp [valueIntView]
          | false =>
              refine ⟨fun _ v hv => ?_, fun _ => rfl⟩
              obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
              simp [valueIntView]
      | holes lo hi hs =>
          refine ⟨fun _ v hv => ?_, fun _ => rfl⟩
          obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
          simp [valueIntView]
      | general vs =>
          change vs.all (fun v => (valueIntView v).isSome) = true ↔
            ∀ v ∈ vs, valueIntView v ≠ none
          rw [List.all_eq_true]
          constructor
          · intro h v hv
            simpa [Option.isSome_iff_ne_none] using h v hv
          · intro h v hv
            simpa [Option.isSome_iff_ne_none] using h v hv

/-- The `domPruningOkB` kind check, integer half.  This stage reads the
    enumeration (correct on every constructor, including the empty
    `small` domain); the O(1) tag-based refinement for `small` is a
    stage-2 increment behind the same statement. -/
def allIntB (d : Dom) : Bool :=
  (enum d).all fun v => match v with | .int _ => true | _ => false

theorem allIntB_iff (d : Dom) :
    allIntB d = true ↔ ∀ v ∈ enum d, ∃ i : Int, v = .int i := by
  unfold allIntB
  rw [List.all_eq_true]
  constructor
  · intro h v hv
    cases v with
    | int i => exact ⟨i, rfl⟩
    | bool b => exact absurd (h (.bool b) hv) (by simp)
    | setOfInt s => exact absurd (h (.setOfInt s) hv) (by simp)
    | array a => exact absurd (h (.array a) hv) (by simp)
  · intro h v hv
    obtain ⟨i, hi⟩ := h v hv
    subst hi
    rfl

/-- The structural integer-kind test agrees with the enumerating one. -/
theorem allIntBStruct_eq_allIntB (d : Dom) : allIntBStruct d = allIntB d :=
  allIntBStruct_eq d

/-- The `domPruningOkB` kind check, Boolean half. -/
def allBoolB (d : Dom) : Bool :=
  (enum d).all fun v => match v with | .bool _ => true | _ => false

theorem allBoolB_iff (d : Dom) :
    allBoolB d = true ↔ ∀ v ∈ enum d, ∃ b : Bool, v = .bool b := by
  unfold allBoolB
  rw [List.all_eq_true]
  constructor
  · intro h v hv
    cases v with
    | int i => exact absurd (h (.int i) hv) (by simp)
    | bool b => exact ⟨b, rfl⟩
    | setOfInt s => exact absurd (h (.setOfInt s) hv) (by simp)
    | array a => exact absurd (h (.array a) hv) (by simp)
  · intro h v hv
    obtain ⟨b, hb⟩ := h v hv
    subst hb
    rfl

/-- The `domPruningOkB` shape disjunction (empty domains pass both
    halves, exactly as the list-level check does). -/
theorem shapeTypedB_iff (d : Dom) :
    (allIntB d || allBoolB d) = true ↔
      (∀ v ∈ enum d, ∃ i : Int, v = .int i) ∨
        (∀ v ∈ enum d, ∃ b : Bool, v = .bool b) := by
  rw [Bool.or_eq_true, allIntB_iff, allBoolB_iff]

/-! ### Duplicate-freedom of the compact enumerations -/

theorem nodup_of_pairwise_lt {l : List Int} (h : l.Pairwise fun a b => a < b) :
    l.Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons]
      refine ⟨fun hx => ?_, ih (List.Pairwise.tail h)⟩
      have := (List.pairwise_cons.mp h).1 x hx
      omega

theorem nodup_map_of_injective {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) →
      l.Nodup → (l.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, h, hn => by
      rw [List.nodup_cons] at hn
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_of_injective
        (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hn.2⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨y, hy, hfy⟩ := hmem
      exact hn.1 (h x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hfy.symm ▸ hy)

theorem nodup_smallBools (bits : UInt64) : (smallBools bits).Nodup := by
  have hrange : List.range 2 = [0, 1] := rfl
  rw [smallBools, hrange]
  by_cases h0 : bits.toNat.testBit 0 = true <;>
    by_cases h1 : bits.toNat.testBit 1 = true <;>
      simp [h0, h1]

/-- The gates' duplicate check: on a canonical `small` domain the
    integer views of the enumeration are duplicate-free, by
    construction (no scan). -/
theorem intViewNodup_small (isBool : Bool) (off : Int) (bits : UInt64) :
    ((enum ⟨.small isBool off bits⟩).map valueIntView).Nodup := by
  cases isBool with
  | true =>
      show ((smallBools bits).map valueIntView).Nodup
      refine nodup_map_of_injective (f := valueIntView) ?_ (nodup_smallBools bits)
      intro a ha b hb heq
      obtain ⟨ba, rfl⟩ := eq_bool_of_mem_smallBools ha
      obtain ⟨bb, rfl⟩ := eq_bool_of_mem_smallBools hb
      cases ba <;> cases bb <;> simp_all [valueIntView]
  | false =>
      show (((smallInts off bits).map Value.int).map valueIntView).Nodup
      rw [List.map_map]
      refine nodup_map_of_injective (f := fun i : Int => valueIntView (Value.int i)) ?_
        (nodup_of_pairwise_lt (pairwise_smallInts off bits))
      intro a _ b _ heq
      exact Option.some.inj heq

theorem intViewNodup_holes (lo hi : Int) (hs : List Int) :
    ((enum ⟨.holes lo hi hs⟩).map valueIntView).Nodup := by
  show (((holesInts lo hi hs).map Value.int).map valueIntView).Nodup
  rw [List.map_map]
  refine nodup_map_of_injective (f := fun i : Int => valueIntView (Value.int i)) ?_
    (nodup_of_pairwise_lt (pairwise_holesInts lo hi hs))
  intro a _ b _ heq
  exact Option.some.inj heq

/-- The hole interval passes the `gateOk` int-viewed shape test in
    O(1) (the enumeration only contains integers). -/
theorem intViewableB_holes (lo hi : Int) (hs : List Int) :
    intViewableB ⟨.holes lo hi hs⟩ = true := rfl

/-- The hole interval passes the `domPruningOkB` integer kind test in
    O(1). -/
theorem allIntB_holes (lo hi : Int) (hs : List Int) :
    allIntB ⟨.holes lo hi hs⟩ = true := by
  unfold allIntB
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
  rfl

/-- The hole interval passes the `domPruningOkB` shape-typing test in
    O(1). -/
theorem shapeTypedB_holes (lo hi : Int) (hs : List Int) :
    (allIntB ⟨.holes lo hi hs⟩ || allBoolB ⟨.holes lo hi hs⟩) = true := by
  rw [allIntB_holes]
  rfl

/-! ### Frame-level bridge statements

`Literal.valueHolds`, `filterSlots`, `filterFrame` and `Frame.mass` are
the S2 surface.  The positional bridges themselves now live in
`CompactDomainBridges.lean`, above `FrameFilter`; the pointwise
`valueHolds` facts below stay here because they mention only `Literal`
and `Dom`. -/

/-! ### Pointwise `valueHolds` facts on integer values -/

theorem valueHolds_boolEq_int (s : Nat) (b p : Bool) (a : Int) :
    Literal.valueHolds ⟨.boolEq s b, p⟩ (.int a) = false := rfl

theorem valueHolds_intNe_pos (s : Nat) (x a : Int) :
    Literal.valueHolds ⟨.intNe s x, true⟩ (.int a) = decide (a ≠ x) := by
  unfold Literal.valueHolds
  simp [Value.intView]

theorem valueHolds_intNe_neg (s : Nat) (x a : Int) :
    Literal.valueHolds ⟨.intNe s x, false⟩ (.int a) = decide (a = x) := by
  unfold Literal.valueHolds
  simp only [Value.intView]
  by_cases h : a = x
  · simp [h]
  · simp [h]

theorem valueHolds_intLe_pos (s : Nat) (u a : Int) :
    Literal.valueHolds ⟨.intLe s u, true⟩ (.int a) = decide (a ≤ u) := by
  unfold Literal.valueHolds
  simp [Value.intView]

theorem valueHolds_intLe_neg (s : Nat) (u a : Int) :
    Literal.valueHolds ⟨.intLe s u, false⟩ (.int a) = decide (u < a) := by
  unfold Literal.valueHolds
  simp only [Value.intView]
  by_cases h : a ≤ u
  · have hlt : ¬ u < a := by omega
    simp [h, hlt]
  · have hlt : u < a := by omega
    simp [h, hlt]

/-! ### Integer-list identities for endpoint removal and cuts -/

theorem holesInts_ne_hi {lo hi : Int} {hs : List Int} :
    holesInts lo (hi - 1) hs =
      (holesInts lo hi hs).filter (fun i => decide (i ≠ hi)) := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts ..
  · exact List.Pairwise.filter _ (pairwise_holesInts ..)
  · intro x
    rw [mem_holesInts, List.mem_filter, mem_holesInts, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, by omega, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, by omega, h3⟩

theorem holesInts_ne_lo {lo hi : Int} {hs : List Int} :
    holesInts (lo + 1) hi hs =
      (holesInts lo hi hs).filter (fun i => decide (i ≠ lo)) := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts ..
  · exact List.Pairwise.filter _ (pairwise_holesInts ..)
  · intro x
    rw [mem_holesInts, List.mem_filter, mem_holesInts, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨by omega, h2, h3⟩

theorem holesInts_le {lo hi upper : Int} {hs : List Int}
    (hupper : upper ∉ hs) (hle : upper ≤ hi) :
    holesInts lo upper (hs.filter (fun h => decide (h < upper))) =
      (holesInts lo hi hs).filter (fun i => decide (i ≤ upper)) := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts ..
  · exact List.Pairwise.filter _ (pairwise_holesInts ..)
  · intro x
    simp only [mem_holesInts, List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hxlt : x < upper ∨ x = upper := by omega
      have hxnot : x ∉ hs := by
        rcases hxlt with hlt | heq
        · intro hx
          exact h3 ⟨hx, hlt⟩
        · rw [heq]; exact hupper
      exact ⟨⟨h1, by omega, hxnot⟩, by omega⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h4, fun hx => h3 hx.1⟩

theorem holesInts_gt {lo hi upper : Int} {hs : List Int}
    (hlo : lo ≤ upper + 1) :
    holesInts (upper + 1) hi (hs.filter (fun h => decide (upper < h))) =
      (holesInts lo hi hs).filter (fun i => decide (upper < i)) := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts ..
  · exact List.Pairwise.filter _ (pairwise_holesInts ..)
  · intro x
    simp only [mem_holesInts, List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hxgt : upper < x := by omega
      have hxnot : x ∉ hs := by
        intro hx
        exact h3 ⟨hx, hxgt⟩
      exact ⟨⟨by omega, h2, hxnot⟩, hxgt⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨by omega, h2, fun hx => h3 hx.1⟩

/-! ### Map/filter forms on `enum` -/

theorem enum_holes_filter_boolEq (s : Nat) (b p : Bool) (lo hi : Int) (hs : List Int) :
    (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.boolEq s b, p⟩) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hv
  rw [valueHolds_boolEq_int]
  simp

theorem enum_holes_filter_ne_hi {lo hi : Int} {hs : List Int} :
    enum ⟨.holes lo (hi - 1) hs⟩ =
      (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.intNe 0 hi, true⟩) := by
  show (holesInts lo (hi - 1) hs).map Value.int =
    ((holesInts lo hi hs).map Value.int).filter (Literal.valueHolds ⟨.intNe 0 hi, true⟩)
  rw [List.filter_map]
  congr 1
  have hfun : (Literal.valueHolds ⟨.intNe 0 hi, true⟩) ∘ Value.int =
      fun a => decide (a ≠ hi) := by
    funext a
    exact valueHolds_intNe_pos 0 hi a
  rw [hfun, holesInts_ne_hi]

theorem enum_holes_filter_ne_lo {lo hi : Int} {hs : List Int} :
    enum ⟨.holes (lo + 1) hi hs⟩ =
      (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.intNe 0 lo, true⟩) := by
  show (holesInts (lo + 1) hi hs).map Value.int =
    ((holesInts lo hi hs).map Value.int).filter (Literal.valueHolds ⟨.intNe 0 lo, true⟩)
  rw [List.filter_map]
  congr 1
  have hfun : (Literal.valueHolds ⟨.intNe 0 lo, true⟩) ∘ Value.int =
      fun a => decide (a ≠ lo) := by
    funext a
    exact valueHolds_intNe_pos 0 lo a
  rw [hfun, holesInts_ne_lo]

theorem enum_holes_filter_le {lo hi upper : Int} {hs : List Int}
    (hupper : upper ∉ hs) (hle : upper ≤ hi) :
    enum ⟨.holes lo upper (hs.filter (fun h => decide (h < upper)))⟩ =
      (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.intLe 0 upper, true⟩) := by
  show (holesInts lo upper (hs.filter (fun h => decide (h < upper)))).map Value.int =
    ((holesInts lo hi hs).map Value.int).filter (Literal.valueHolds ⟨.intLe 0 upper, true⟩)
  rw [List.filter_map]
  congr 1
  have hfun : (Literal.valueHolds ⟨.intLe 0 upper, true⟩) ∘ Value.int =
      fun a => decide (a ≤ upper) := by
    funext a
    exact valueHolds_intLe_pos 0 upper a
  rw [hfun, holesInts_le hupper hle]

theorem enum_holes_filter_gt {lo hi upper : Int} {hs : List Int}
    (hlo : lo ≤ upper + 1) :
    enum ⟨.holes (upper + 1) hi (hs.filter (fun h => decide (upper < h)))⟩ =
      (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.intLe 0 upper, false⟩) := by
  show (holesInts (upper + 1) hi (hs.filter (fun h => decide (upper < h)))).map Value.int =
    ((holesInts lo hi hs).map Value.int).filter (Literal.valueHolds ⟨.intLe 0 upper, false⟩)
  rw [List.filter_map]
  congr 1
  have hfun : (Literal.valueHolds ⟨.intLe 0 upper, false⟩) ∘ Value.int =
      fun a => decide (upper < a) := by
    funext a
    exact valueHolds_intLe_neg 0 upper a
  rw [hfun, holesInts_gt hlo]

/-! ### The structural fast path -/

/-- Endpoint-shrink guard: the new span is still wider than 64 and still
    passes the density test. -/
def holesStepB (lo hi : Int) (hs : List Int) : Bool :=
  decide (64 < (hi - lo + 1).toNat) && decide (hs.length * 4 ≤ (hi - lo + 1).toNat)

/-- Structural filter of a hole interval by one literal.  `none` means the
    literal is not handled by an endpoint/cut shortcut and the caller
    falls back to the enumerating `filter`. -/
def filterHoles? (atom : Atom) (positive : Bool) (lo hi : Int) (hs : List Int) : Option Dom :=
  match atom, positive with
  | .boolEq _ _, _ => some empty
  | .intNe _ x, true =>
      if decide (x < lo ∨ hi < x) then
        some ⟨.holes lo hi hs⟩
      else if x == lo then
        if memHoles hs (lo + 1) then none
        else if holesStepB (lo + 1) hi hs then some ⟨.holes (lo + 1) hi hs⟩
        else none
      else if x == hi then
        if memHoles hs (hi - 1) then none
        else if holesStepB lo (hi - 1) hs then some ⟨.holes lo (hi - 1) hs⟩
        else none
      else if memHoles hs x then some ⟨.holes lo hi hs⟩
      else none
  | .intNe _ x, false =>
      if memBool ⟨.holes lo hi hs⟩ (.int x) then some (ofList [.int x]) else some empty
  | .intLe _ upper, true =>
      if hi ≤ upper then
        some ⟨.holes lo hi hs⟩
      else if upper < lo then
        some empty
      else if memHoles hs upper then none
      else if holesStepB lo upper (hs.filter fun h => decide (h < upper)) then
        some ⟨.holes lo upper (hs.filter fun h => decide (h < upper))⟩
      else none
  | .intLe _ upper, false =>
      if upper < lo then
        some ⟨.holes lo hi hs⟩
      else if hi ≤ upper then
        some empty
      else if memHoles hs (upper + 1) then none
      else if holesStepB (upper + 1) hi (hs.filter fun h => decide (upper < h)) then
        some ⟨.holes (upper + 1) hi (hs.filter fun h => decide (upper < h))⟩
      else none

theorem enum_filterHoles? {atom : Atom} {positive : Bool} {lo hi : Int}
    {hs : List Int} {e : Dom}
    (h : filterHoles? atom positive lo hi hs = some e) :
    enum e = (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨atom, positive⟩) := by
  unfold filterHoles? at h
  cases atom with
  | boolEq s b =>
      cases positive with
      | false =>
          simp only [Option.some.injEq] at h
          subst h
          rw [enum_holes_filter_boolEq, show enum (empty : Dom) = [] from rfl]
      | true =>
          simp only [Option.some.injEq] at h
          subst h
          rw [enum_holes_filter_boolEq, show enum (empty : Dom) = [] from rfl]
  | intNe s x =>
      cases positive with
      | true =>
          dsimp only at h
          by_cases hout : decide (x < lo ∨ hi < x) = true
          · rw [if_pos hout] at h
            simp only [Option.some.injEq] at h
            subst h
            exact (List.filter_eq_self.mpr (by
              intro v hv
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
              rw [valueHolds_intNe_pos]
              apply decide_eq_true
              obtain ⟨h1, h2, -⟩ := mem_holesInts.mp ha
              have hout' := of_decide_eq_true hout
              omega)).symm
          · rw [if_neg hout] at h
            by_cases hxlo : (x == lo) = true
            · rw [if_pos hxlo] at h
              have hxlo' : x = lo := beq_iff_eq.mp hxlo
              by_cases hmem : memHoles hs (lo + 1) = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB (lo + 1) hi hs = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  subst hxlo'
                  exact enum_holes_filter_ne_lo
                · rw [if_neg hstep] at h; simp at h
            · rw [if_neg hxlo] at h
              by_cases hxhi : (x == hi) = true
              · rw [if_pos hxhi] at h
                have hxhi' : x = hi := beq_iff_eq.mp hxhi
                by_cases hmem : memHoles hs (hi - 1) = true
                · rw [if_pos hmem] at h; simp at h
                · rw [if_neg hmem] at h
                  by_cases hstep : holesStepB lo (hi - 1) hs = true
                  · rw [if_pos hstep] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    subst hxhi'
                    exact enum_holes_filter_ne_hi
                  · rw [if_neg hstep] at h; simp at h
              · rw [if_neg hxhi] at h
                by_cases hmem : memHoles hs x = true
                · rw [if_pos hmem] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact (List.filter_eq_self.mpr (by
                    intro v hv
                    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
                    rw [valueHolds_intNe_pos]
                    apply decide_eq_true
                    intro hxa
                    subst hxa
                    exact (mem_holesInts.mp ha).2.2 (memHoles_iff.mp hmem))).symm
                · rw [if_neg hmem] at h; simp at h
      | false =>
          dsimp only at h
          by_cases hmem : memBool ⟨.holes lo hi hs⟩ (.int x) = true
          · rw [if_pos hmem] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [show enum (ofList [.int x]) = [.int x] from enum_ofList _]
            have hxmem : x ∈ holesInts lo hi hs := by
              have hxenum : Value.int x ∈ enum ⟨.holes lo hi hs⟩ :=
                (memBool_iff _ _).mp hmem
              obtain ⟨a, ha, heq⟩ := List.mem_map.mp hxenum
              cases heq
              exact ha
            show [.int x] =
              (enum ⟨.holes lo hi hs⟩).filter (Literal.valueHolds ⟨.intNe s x, false⟩)
            rw [show enum ⟨.holes lo hi hs⟩ =
              (holesInts lo hi hs).map Value.int from rfl]
            rw [List.filter_map]
            have hfun : (Literal.valueHolds ⟨.intNe s x, false⟩) ∘ Value.int =
                fun a => decide (a = x) := by
              funext a
              exact valueHolds_intNe_neg s x a
            rw [hfun]
            have hfilt : (holesInts lo hi hs).filter (fun a => decide (a = x)) = [x] := by
              apply eq_of_pairwise_lt_of_mem_iff
              · exact List.Pairwise.filter _ (pairwise_holesInts ..)
              · exact List.pairwise_cons.mpr ⟨by intro b hb; simp at hb, by simp⟩
              · intro y
                simp only [List.mem_filter, decide_eq_true_iff, List.mem_singleton]
                constructor
                · rintro ⟨-, rfl⟩
                  rfl
                · rintro rfl
                  exact ⟨hxmem, rfl⟩
            rw [hfilt]
            rfl
          · rw [if_neg hmem] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [show enum (empty : Dom) = [] from rfl]
            exact (List.filter_eq_nil_iff.mpr (by
              intro v hv
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
              rw [valueHolds_intNe_neg, decide_eq_true_iff]
              intro hax
              subst hax
              have htrue : memBool ⟨.holes lo hi hs⟩ (.int a) = true :=
                (memBool_iff _ _).mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
              rw [htrue] at hmem
              simp at hmem)).symm
  | intLe s upper =>
      cases positive with
      | true =>
          dsimp only at h
          by_cases htop : hi ≤ upper
          · rw [if_pos htop] at h
            simp only [Option.some.injEq] at h
            subst h
            exact (List.filter_eq_self.mpr (by
              intro v hv
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
              rw [valueHolds_intLe_pos]
              apply decide_eq_true
              obtain ⟨-, hhi, -⟩ := mem_holesInts.mp ha
              omega)).symm
          · rw [if_neg htop] at h
            by_cases hbot : upper < lo
            · rw [if_pos hbot] at h
              simp only [Option.some.injEq] at h
              subst h
              rw [show enum (empty : Dom) = [] from rfl]
              exact (List.filter_eq_nil_iff.mpr (by
                intro v hv
                obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
                rw [valueHolds_intLe_pos, decide_eq_true_iff]
                obtain ⟨hlo, -, -⟩ := mem_holesInts.mp ha
                omega)).symm
            · rw [if_neg hbot] at h
              by_cases hmem : memHoles hs upper = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB lo upper (hs.filter fun h => decide (h < upper)) = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_holes_filter_le
                  · intro hu
                    exact hmem (memHoles_iff.mpr hu)
                  · omega
                · rw [if_neg hstep] at h; simp at h
      | false =>
          dsimp only at h
          by_cases hbot : upper < lo
          · rw [if_pos hbot] at h
            simp only [Option.some.injEq] at h
            subst h
            exact (List.filter_eq_self.mpr (by
              intro v hv
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
              rw [valueHolds_intLe_neg]
              apply decide_eq_true
              obtain ⟨hlo, -, -⟩ := mem_holesInts.mp ha
              omega)).symm
          · rw [if_neg hbot] at h
            by_cases htop : hi ≤ upper
            · rw [if_pos htop] at h
              simp only [Option.some.injEq] at h
              subst h
              rw [show enum (empty : Dom) = [] from rfl]
              exact (List.filter_eq_nil_iff.mpr (by
                intro v hv
                obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
                rw [valueHolds_intLe_neg, decide_eq_true_iff]
                obtain ⟨-, hhi, -⟩ := mem_holesInts.mp ha
                omega)).symm
            · rw [if_neg htop] at h
              by_cases hmem : memHoles hs (upper + 1) = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB (upper + 1) hi (hs.filter fun h => decide (upper < h)) = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_holes_filter_gt
                  omega
                · rw [if_neg hstep] at h; simp at h

theorem wf_filterHoles? {atom : Atom} {positive : Bool} {lo hi : Int}
    {hs : List Int} {e : Dom}
    (hd : WF ⟨.holes lo hi hs⟩) (h : filterHoles? atom positive lo hi hs = some e) : WF e := by
  obtain ⟨hsorted, hbounds, hspan, hdens⟩ := hd
  unfold filterHoles? at h
  cases atom with
  | boolEq s b =>
      cases positive with
      | false =>
          simp only [Option.some.injEq] at h
          subst h
          exact WF_ofList _
      | true =>
          simp only [Option.some.injEq] at h
          subst h
          exact WF_ofList _
  | intNe s x =>
      cases positive with
      | true =>
          dsimp only at h
          by_cases hout : decide (x < lo ∨ hi < x) = true
          · rw [if_pos hout] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨hsorted, hbounds, hspan, hdens⟩
          · rw [if_neg hout] at h
            by_cases hxlo : (x == lo) = true
            · rw [if_pos hxlo] at h
              by_cases hmem : memHoles hs (lo + 1) = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB (lo + 1) hi hs = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  simp only [holesStepB, Bool.and_eq_true, decide_eq_true_iff] at hstep
                  refine ⟨hsorted, ?_, hstep.1, hstep.2⟩
                  intro y hy
                  obtain ⟨h1, h2⟩ := hbounds y hy
                  have hyne : y ≠ lo + 1 := by
                    intro heq
                    exact absurd (memHoles_iff.mpr (heq ▸ hy)) (by simp [hmem])
                  exact ⟨by omega, h2⟩
                · rw [if_neg hstep] at h; simp at h
            · rw [if_neg hxlo] at h
              by_cases hxhi : (x == hi) = true
              · rw [if_pos hxhi] at h
                by_cases hmem : memHoles hs (hi - 1) = true
                · rw [if_pos hmem] at h; simp at h
                · rw [if_neg hmem] at h
                  by_cases hstep : holesStepB lo (hi - 1) hs = true
                  · rw [if_pos hstep] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    simp only [holesStepB, Bool.and_eq_true, decide_eq_true_iff] at hstep
                    refine ⟨hsorted, ?_, hstep.1, hstep.2⟩
                    intro y hy
                    obtain ⟨h1, h2⟩ := hbounds y hy
                    have hyne : y ≠ hi - 1 := by
                      intro heq
                      exact absurd (memHoles_iff.mpr (heq ▸ hy)) (by simp [hmem])
                    exact ⟨h1, by omega⟩
                  · rw [if_neg hstep] at h; simp at h
              · rw [if_neg hxhi] at h
                by_cases hmem : memHoles hs x = true
                · rw [if_pos hmem] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact ⟨hsorted, hbounds, hspan, hdens⟩
                · rw [if_neg hmem] at h; simp at h
      | false =>
          dsimp only at h
          by_cases hmem : memBool ⟨.holes lo hi hs⟩ (.int x) = true
          · rw [if_pos hmem] at h
            simp only [Option.some.injEq] at h
            subst h
            exact WF_ofList _
          · rw [if_neg hmem] at h
            simp only [Option.some.injEq] at h
            subst h
            exact WF_ofList _
  | intLe s upper =>
      cases positive with
      | true =>
          dsimp only at h
          by_cases htop : hi ≤ upper
          · rw [if_pos htop] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨hsorted, hbounds, hspan, hdens⟩
          · rw [if_neg htop] at h
            by_cases hbot : upper < lo
            · rw [if_pos hbot] at h
              simp only [Option.some.injEq] at h
              subst h
              exact WF_ofList _
            · rw [if_neg hbot] at h
              by_cases hmem : memHoles hs upper = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB lo upper (hs.filter fun h => decide (h < upper)) = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  simp only [holesStepB, Bool.and_eq_true, decide_eq_true_iff] at hstep
                  refine ⟨List.Pairwise.filter _ hsorted, ?_, hstep.1, hstep.2⟩
                  intro y hy
                  obtain ⟨hyhs, hylt⟩ := List.mem_filter.mp hy
                  exact ⟨(hbounds y hyhs).1, of_decide_eq_true hylt⟩
                · rw [if_neg hstep] at h; simp at h
      | false =>
          dsimp only at h
          by_cases hbot : upper < lo
          · rw [if_pos hbot] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨hsorted, hbounds, hspan, hdens⟩
          · rw [if_neg hbot] at h
            by_cases htop : hi ≤ upper
            · rw [if_pos htop] at h
              simp only [Option.some.injEq] at h
              subst h
              exact WF_ofList _
            · rw [if_neg htop] at h
              by_cases hmem : memHoles hs (upper + 1) = true
              · rw [if_pos hmem] at h; simp at h
              · rw [if_neg hmem] at h
                by_cases hstep : holesStepB (upper + 1) hi (hs.filter fun h => decide (upper < h)) = true
                · rw [if_pos hstep] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  simp only [holesStepB, Bool.and_eq_true, decide_eq_true_iff] at hstep
                  refine ⟨List.Pairwise.filter _ hsorted, ?_, hstep.1, hstep.2⟩
                  intro y hy
                  obtain ⟨hyhs, hygt⟩ := List.mem_filter.mp hy
                  have hygt' : upper < y := of_decide_eq_true hygt
                  have hyne : y ≠ upper + 1 := by
                    intro heq
                    exact absurd (memHoles_iff.mpr (heq ▸ hyhs)) (by simp [hmem])
                  exact ⟨by omega, (hbounds y hyhs).2⟩
                · rw [if_neg hstep] at h; simp at h

/-! ### Bit masks for the `.small` structural filter -/

/-- The 64-bit mask with only bit `k` cleared. -/
def clearBitMask (k : Nat) : UInt64 := UInt64.ofNat (2 ^ 64 - (2 ^ k + 1))

/-- The 64-bit mask with the low `n` bits set. -/
def lowBitsMask (n : Nat) : UInt64 := UInt64.ofNat (2 ^ n - 1)

theorem clearBitMask_toNat {k : Nat} :
    (clearBitMask k).toNat = 2 ^ 64 - (2 ^ k + 1) := by
  unfold clearBitMask
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  exact Nat.sub_lt (Nat.two_pow_pos 64) (Nat.add_pos_left (Nat.two_pow_pos k) 1)

theorem clearBitMask_testBit {k j : Nat} (hk : k < 64) (hj : j < 64) :
    (clearBitMask k).toNat.testBit j = decide (j ≠ k) := by
  rw [clearBitMask_toNat, Nat.testBit_two_pow_sub_succ]
  · rw [Nat.testBit_two_pow]
    have hj' : decide (j < 64) = true := decide_eq_true hj
    rw [hj']
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hkj : ¬k = j := fun h => hjk h.symm
      simp [hjk, hkj]
  · exact Nat.pow_lt_pow_right (by decide) hk

theorem lowBitsMask_toNat {n : Nat} (hn : n ≤ 64) :
    (lowBitsMask n).toNat = 2 ^ n - 1 := by
  unfold lowBitsMask
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hn
  omega

theorem lowBitsMask_testBit {n j : Nat} (hn : n ≤ 64) (_hj : j < 64) :
    (lowBitsMask n).toNat.testBit j = decide (j < n) := by
  rw [lowBitsMask_toNat hn, Nat.testBit_two_pow_sub_one]

/-- A masked bitset enumerates exactly the surviving packed integers. -/
theorem smallInts_and {off : Int} {bits mask : UInt64} {q : Int → Bool}
    (hmask : ∀ j, j < 64 → ((mask.toNat.testBit j = true) ↔ q (off + (j : Int)) = true)) :
    smallInts off (bits &&& mask) = (smallInts off bits).filter q := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_smallInts ..
  · exact List.Pairwise.filter _ (pairwise_smallInts ..)
  · intro x
    rw [mem_smallInts_int, List.mem_filter, mem_smallInts_int]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [UInt64.toNat_and, Nat.testBit_and] at h3
      have hk : (x - off).toNat < 64 := by
        have h' : (((x - off).toNat : Int)) < 64 := by
          rw [Int.toNat_of_nonneg (by omega)]
          exact h2
        exact_mod_cast h'
      have h3' := (Bool.and_eq_true ..).mp h3
      have hq : q x = true := by
        have h := (hmask (x - off).toNat hk).mp h3'.2
        have hx : off + (((x - off).toNat : Nat) : Int) = x := by
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        rwa [hx] at h
      exact ⟨⟨h1, h2, h3'.1⟩, hq⟩
    · rintro ⟨⟨h1, h2, h3⟩, hq⟩
      have hk : (x - off).toNat < 64 := by
        have h' : (((x - off).toNat : Int)) < 64 := by
          rw [Int.toNat_of_nonneg (by omega)]
          exact h2
        exact_mod_cast h'
      have hm : mask.toNat.testBit (x - off).toNat = true := by
        apply (hmask _ hk).mpr
        have hx : off + (((x - off).toNat : Nat) : Int) = x := by
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        rwa [hx]
      refine ⟨h1, h2, ?_⟩
      rw [UInt64.toNat_and, Nat.testBit_and, h3, hm]
      rfl

/-- The masked form of `enum` for the small integer case. -/
theorem enum_small_and {off : Int} {bits mask : UInt64} {l : Literal}
    (hmask : ∀ j, j < 64 →
      ((mask.toNat.testBit j = true) ↔ l.valueHolds (.int (off + (j : Int))) = true)) :
    enum ⟨.small false off (bits &&& mask)⟩ =
      (enum ⟨.small false off bits⟩).filter l.valueHolds := by
  show (smallInts off (bits &&& mask)).map Value.int =
    ((smallInts off bits).map Value.int).filter l.valueHolds
  rw [List.filter_map]
  congr 1
  exact smallInts_and hmask

theorem enum_small_self {off : Int} {bits : UInt64} {l : Literal}
    (h : ∀ i, i ∈ smallInts off bits → l.valueHolds (.int i) = true) :
    enum ⟨.small false off bits⟩ =
      (enum ⟨.small false off bits⟩).filter l.valueHolds := by
  exact (List.filter_eq_self.mpr (by
    intro v hv
    show l.valueHolds v = true
    have hv' : v ∈ (smallInts off bits).map Value.int := hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv'
    exact h i hi)).symm

theorem enum_small_nil {off : Int} {bits : UInt64} {l : Literal}
    (h : ∀ i, i ∈ smallInts off bits → l.valueHolds (.int i) = false) :
    enum (empty : Dom) = (enum ⟨.small false off bits⟩).filter l.valueHolds := by
  rw [show enum (empty : Dom) = [] from rfl]
  exact (List.filter_eq_nil_iff.mpr (by
    intro v hv
    show ¬l.valueHolds v = true
    have hv' : v ∈ (smallInts off bits).map Value.int := hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv'
    rw [h i hi]
    simp)).symm

/-- The two-bit filter of a Boolean bitset. -/
def boolMask (bits : UInt64) (p0 p1 : Bool) : UInt64 :=
  UInt64.ofNat ((if p0 && bits.toNat.testBit 0 then 1 else 0) +
    (if p1 && bits.toNat.testBit 1 then 2 else 0))

theorem boolMask_toNat_le_three (bits : UInt64) (p0 p1 : Bool) :
    (boolMask bits p0 p1).toNat ≤ 3 := by
  unfold boolMask
  rw [UInt64.toNat_ofNat']
  have hle : (if p0 && bits.toNat.testBit 0 then 1 else 0) +
      (if p1 && bits.toNat.testBit 1 then 2 else 0) ≤ 3 := by
    split <;> split <;> omega
  exact Nat.le_trans (Nat.mod_le _ _) hle

theorem smallBools_eq (bits : UInt64) :
    smallBools bits =
      (if bits.toNat.testBit 0 then [Value.bool false] else []) ++
      (if bits.toNat.testBit 1 then [Value.bool true] else []) := by
  cases h0 : bits.toNat.testBit 0 <;> cases h1 : bits.toNat.testBit 1 <;>
    simp [smallBools, List.range_succ, h0, h1]

theorem smallBools_zero : smallBools (0 : UInt64) = [] := rfl

theorem smallBools_one : smallBools (1 : UInt64) = [Value.bool false] := rfl

theorem smallBools_two : smallBools (2 : UInt64) = [Value.bool true] := rfl

theorem smallBools_three :
    smallBools (3 : UInt64) = [Value.bool false, Value.bool true] := rfl

/-- `true` exactly on `.bool true`. -/
def isTrueB : Value → Bool
  | .bool true => true
  | _ => false

theorem smallBools_boolMask (bits : UInt64) (p0 p1 : Bool) :
    smallBools (boolMask bits p0 p1) =
      (smallBools bits).filter (fun v => if isTrueB v then p1 else p0) := by
  cases h0 : bits.toNat.testBit 0 <;> cases h1 : bits.toNat.testBit 1 <;>
    cases p0 <;> cases p1 <;>
    simp [boolMask, smallBools_eq, h0, h1, isTrueB, Nat.testBit_succ]

theorem smallBools_boolMask_lit (bits : UInt64) (l : Literal) :
    smallBools (boolMask bits (l.valueHolds (.bool false)) (l.valueHolds (.bool true))) =
      (smallBools bits).filter l.valueHolds := by
  rw [smallBools_boolMask]
  apply List.filter_congr
  intro v hv
  obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
  cases b <;> rfl

theorem smallLe_iff (u off : Int)
    (hu : off + (((u - off).toNat : Nat) : Int) = u) (j : Nat) :
    j < (u - off).toNat + 1 ↔ off + (j : Int) ≤ u := by
  have hk : ((u - off).toNat : Int) = u - off := by omega
  constructor
  · intro h
    have h' : (j : Int) < ((u - off).toNat : Int) + 1 := by exact_mod_cast h
    omega
  · intro h
    have h' : (j : Int) < ((u - off).toNat : Int) + 1 := by omega
    have h'' : (j : Int) < (((u - off).toNat + 1 : Nat) : Int) := by
      push_cast
      exact h'
    exact Int.ofNat_lt.mp h''

/-- Structural filter of a `.small` domain.  `none` means the caller
    falls back to the enumerating `filter`. -/
def filterSmall? (isBool : Bool) (off : Int) (bits : UInt64)
    (atom : Atom) (positive : Bool) : Option Dom :=
  match isBool with
  | true =>
      let p0 := Literal.valueHolds ⟨atom, positive⟩ (.bool false)
      let p1 := Literal.valueHolds ⟨atom, positive⟩ (.bool true)
      let m := boolMask bits p0 p1
      if m.toNat = 0 then some empty
      else some ⟨.small true 0 m⟩
  | false =>
      match atom, positive with
      | .boolEq _ _, _ => some empty
      | .intNe _ x, true =>
          if decide (x < off ∨ off + 64 ≤ x) then some ⟨.small false off bits⟩
          else
            let k := (x - off).toNat
            if bits.toNat.testBit k then
              if k = 0 then none
              else some ⟨.small false off (bits &&& clearBitMask k)⟩
            else some ⟨.small false off bits⟩
      | .intNe _ x, false =>
          if decide (x < off ∨ off + 64 ≤ x) then some empty
          else
            let k := (x - off).toNat
            if bits.toNat.testBit k then some ⟨.small false x 1⟩ else some empty
      | .intLe _ u, true =>
          if off + 63 ≤ u then some ⟨.small false off bits⟩
          else if u < off then some empty
          else
            let k := (u - off).toNat
            let b := bits &&& lowBitsMask (k + 1)
            if b.toNat = 0 then some empty
            else if b.toNat.testBit 0 then some ⟨.small false off b⟩
            else none
      | .intLe _ u, false =>
          if u < off then some ⟨.small false off bits⟩
          else if off + 63 ≤ u then some empty
          else none

theorem enum_filterSmall? {isBool : Bool} {off : Int} {bits : UInt64}
    {atom : Atom} {positive : Bool} {e : Dom}
    (h : filterSmall? isBool off bits atom positive = some e) :
    enum e = (enum ⟨.small isBool off bits⟩).filter
      (Literal.valueHolds ⟨atom, positive⟩) := by
  cases isBool with
  | true =>
      unfold filterSmall? at h
      dsimp only at h
      by_cases hm : (boolMask bits
          (Literal.valueHolds ⟨atom, positive⟩ (.bool false))
          (Literal.valueHolds ⟨atom, positive⟩ (.bool true))).toNat = 0
      · rw [if_pos hm] at h
        simp only [Option.some.injEq] at h
        subst h
        have hb : boolMask bits
            (Literal.valueHolds ⟨atom, positive⟩ (.bool false))
            (Literal.valueHolds ⟨atom, positive⟩ (.bool true)) = 0 := by
          apply UInt64.toNat_inj.mp
          rw [hm, UInt64.toNat_zero]
        show [] = (smallBools bits).filter (Literal.valueHolds ⟨atom, positive⟩)
        rw [← smallBools_boolMask_lit bits ⟨atom, positive⟩, hb]
        rfl
      · rw [if_neg hm] at h
        simp only [Option.some.injEq] at h
        subst h
        show smallBools (boolMask bits
          (Literal.valueHolds ⟨atom, positive⟩ (.bool false))
          (Literal.valueHolds ⟨atom, positive⟩ (.bool true))) =
          (smallBools bits).filter (Literal.valueHolds ⟨atom, positive⟩)
        exact smallBools_boolMask_lit bits ⟨atom, positive⟩
  | false =>
      unfold filterSmall? at h
      cases atom with
      | boolEq s b =>
          cases positive <;>
            simp only [Option.some.injEq] at h <;>
            subst h <;>
            (rw [show enum (empty : Dom) = [] from rfl]
             exact (List.filter_eq_nil_iff.mpr (by
               intro v hv
               show ¬Literal.valueHolds _ v = true
               have hv' : v ∈ (smallInts off bits).map Value.int := hv
               obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv'
               rw [valueHolds_boolEq_int]
               simp)).symm)
      | intNe s x =>
          cases positive with
          | true =>
              dsimp only at h
              by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
              · rw [if_pos hout] at h
                simp only [Option.some.injEq] at h
                subst h
                apply enum_small_self
                intro i hi
                rw [valueHolds_intNe_pos, decide_eq_true_iff]
                obtain ⟨h1, h2, -⟩ := mem_smallInts_int.mp hi
                have hout' : x < off ∨ off + 64 ≤ x := by simpa using hout
                omega
              · rw [if_neg hout] at h
                by_cases hbit : bits.toNat.testBit (x - off).toNat = true
                · rw [if_pos hbit] at h
                  by_cases hk0 : (x - off).toNat = 0
                  · rw [if_pos hk0] at h
                    simp at h
                  · rw [if_neg hk0] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                    have hk64 : (x - off).toNat < 64 := by
                      have h' : (((x - off).toNat : Int)) < 64 := by
                        rw [Int.toNat_of_nonneg (by omega)]
                        omega
                      exact_mod_cast h'
                    have hx : off + (((x - off).toNat : Nat) : Int) = x := by
                      rw [Int.toNat_of_nonneg (by omega)]
                      omega
                    apply enum_small_and
                    intro j hj
                    rw [clearBitMask_testBit hk64 hj, valueHolds_intNe_pos,
                      decide_eq_true_iff, decide_eq_true_iff]
                    constructor
                    · intro hjk hx'
                      apply hjk
                      omega
                    · intro hne hjk
                      apply hne
                      omega
                · rw [if_neg hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_small_self
                  intro i hi
                  rw [valueHolds_intNe_pos, decide_eq_true_iff]
                  intro hix
                  have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                  have hk64 : (x - off).toNat < 64 := by
                    have h' : (((x - off).toNat : Int)) < 64 := by
                      rw [Int.toNat_of_nonneg (by omega)]
                      omega
                    exact_mod_cast h'
                  have hx : off + (((x - off).toNat : Nat) : Int) = x := by
                    rw [Int.toNat_of_nonneg (by omega)]
                    omega
                  have hxmem : x ∈ smallInts off bits := hix ▸ hi
                  rw [← hx, mem_smallInts_iff hk64] at hxmem
                  exact hbit hxmem
          | false =>
              dsimp only at h
              by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
              · rw [if_pos hout] at h
                simp only [Option.some.injEq] at h
                subst h
                apply enum_small_nil
                intro i hi
                rw [valueHolds_intNe_neg]
                apply decide_eq_false
                intro hix
                obtain ⟨h1, h2, -⟩ := mem_smallInts_int.mp hi
                have hout' : x < off ∨ off + 64 ≤ x := by simpa using hout
                omega
              · rw [if_neg hout] at h
                by_cases hbit : bits.toNat.testBit (x - off).toNat = true
                · rw [if_pos hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  -- singleton
                  have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                  have hxmem : x ∈ smallInts off bits := by
                    have hk64 : (x - off).toNat < 64 := by
                      have h' : (((x - off).toNat : Int)) < 64 := by
                        rw [Int.toNat_of_nonneg (by omega)]
                        omega
                      exact_mod_cast h'
                    have hx : off + (((x - off).toNat : Nat) : Int) = x := by
                      rw [Int.toNat_of_nonneg (by omega)]
                      omega
                    rw [← hx, mem_smallInts_iff hk64]
                    exact hbit
                  have hsingle : enum ⟨.small false x 1⟩ = [Value.int x] := by
                    show (smallInts x 1).map Value.int = [Value.int x]
                    have hs : smallInts x (1 : UInt64) = [x] := by
                      have hb : (1 : UInt64) = UInt64.ofNat (intsToBits x [x]) := by
                        rw [show intsToBits x [x] = 1 by simp [intsToBits]]
                        rfl
                      rw [hb]
                      exact smallInts_intsToBits (lo := x) (L := [x])
                        (by simp) (by simp) (by simp)
                    rw [hs]
                    rfl
                  rw [hsingle]
                  show [Value.int x] = ((smallInts off bits).map Value.int).filter
                    (Literal.valueHolds ⟨.intNe s x, false⟩)
                  rw [List.filter_map]
                  have hqf : (Literal.valueHolds ⟨.intNe s x, false⟩) ∘ Value.int =
                      fun a => decide (a = x) := by
                    funext a
                    exact valueHolds_intNe_neg s x a
                  rw [hqf]
                  have hfilt : (smallInts off bits).filter (fun a => decide (a = x)) =
                      [x] := by
                    apply eq_of_pairwise_lt_of_mem_iff
                    · exact List.Pairwise.filter _ (pairwise_smallInts ..)
                    · exact List.pairwise_singleton ..
                    · intro y
                      rw [List.mem_filter, decide_eq_true_iff, List.mem_singleton]
                      constructor
                      · rintro ⟨-, rfl⟩
                        rfl
                      · rintro rfl
                        exact ⟨hxmem, rfl⟩
                  rw [hfilt]
                  rfl
                · rw [if_neg hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_small_nil
                  intro i hi
                  rw [valueHolds_intNe_neg]
                  apply decide_eq_false
                  intro hix
                  have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                  have hk64 : (x - off).toNat < 64 := by
                    have h' : (((x - off).toNat : Int)) < 64 := by
                      rw [Int.toNat_of_nonneg (by omega)]
                      omega
                    exact_mod_cast h'
                  have hx : off + (((x - off).toNat : Nat) : Int) = x := by
                    rw [Int.toNat_of_nonneg (by omega)]
                    omega
                  have himem : i ∈ smallInts off bits := hi
                  rw [hix, ← hx, mem_smallInts_iff hk64] at himem
                  exact hbit himem
      | intLe s u =>
          cases positive with
          | true =>
              dsimp only at h
              by_cases htop : off + 63 ≤ u
              · rw [if_pos htop] at h
                simp only [Option.some.injEq] at h
                subst h
                apply enum_small_self
                intro i hi
                rw [valueHolds_intLe_pos, decide_eq_true_iff]
                obtain ⟨h1, h2, -⟩ := mem_smallInts_int.mp hi
                omega
              · rw [if_neg htop] at h
                by_cases hbot : u < off
                · rw [if_pos hbot] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_small_nil
                  intro i hi
                  rw [valueHolds_intLe_pos]
                  apply decide_eq_false
                  obtain ⟨h1, -, -⟩ := mem_smallInts_int.mp hi
                  omega
                · rw [if_neg hbot] at h
                  by_cases hz : (bits &&& lowBitsMask ((u - off).toNat + 1)).toNat = 0
                  · rw [if_pos hz] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    have hb : (bits &&& lowBitsMask ((u - off).toNat + 1)) = 0 := by
                      apply UInt64.toNat_inj.mp
                      rw [hz, UInt64.toNat_zero]
                    have hle : (u - off).toNat + 1 ≤ 64 := by
                      have h' : ((u - off).toNat : Int) + 1 ≤ 64 := by
                        rw [Int.toNat_of_nonneg (by omega)]
                        omega
                      exact_mod_cast h'
                    have hu : off + (((u - off).toNat : Nat) : Int) = u := by
                      rw [Int.toNat_of_nonneg (by omega)]
                      omega
                    have hmain := enum_small_and (l := ⟨.intLe s u, true⟩)
                      (bits := bits) (mask := lowBitsMask ((u - off).toNat + 1))
                      (by
                        intro j hj
                        rw [lowBitsMask_testBit hle hj, valueHolds_intLe_pos,
                          decide_eq_true_iff, decide_eq_true_iff]
                        exact smallLe_iff u off hu j)
                    rw [hb] at hmain
                    exact hmain
                  · rw [if_neg hz] at h
                    by_cases hb0 : (bits &&& lowBitsMask ((u - off).toNat + 1)).toNat.testBit 0 = true
                    · rw [if_pos hb0] at h
                      simp only [Option.some.injEq] at h
                      subst h
                      have hle : (u - off).toNat + 1 ≤ 64 := by
                        have h' : ((u - off).toNat : Int) + 1 ≤ 64 := by
                          rw [Int.toNat_of_nonneg (by omega)]
                          omega
                        exact_mod_cast h'
                      have hu : off + (((u - off).toNat : Nat) : Int) = u := by
                        rw [Int.toNat_of_nonneg (by omega)]
                        omega
                      apply enum_small_and
                      intro j hj
                      rw [lowBitsMask_testBit hle hj, valueHolds_intLe_pos,
                        decide_eq_true_iff, decide_eq_true_iff]
                      exact smallLe_iff u off hu j
                    · rw [if_neg hb0] at h
                      simp at h
          | false =>
              dsimp only at h
              by_cases hbot : u < off
              · rw [if_pos hbot] at h
                simp only [Option.some.injEq] at h
                subst h
                apply enum_small_self
                intro i hi
                rw [valueHolds_intLe_neg, decide_eq_true_iff]
                obtain ⟨h1, -, -⟩ := mem_smallInts_int.mp hi
                omega
              · rw [if_neg hbot] at h
                by_cases htop : off + 63 ≤ u
                · rw [if_pos htop] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  apply enum_small_nil
                  intro i hi
                  rw [valueHolds_intLe_neg]
                  apply decide_eq_false
                  obtain ⟨-, h2, -⟩ := mem_smallInts_int.mp hi
                  omega
                · rw [if_neg htop] at h
                  simp at h

theorem wf_filterSmall? {isBool : Bool} {off : Int} {bits : UInt64}
    {atom : Atom} {positive : Bool} {e : Dom}
    (hd : WF ⟨.small isBool off bits⟩)
    (h : filterSmall? isBool off bits atom positive = some e) : WF e := by
  cases isBool with
  | true =>
      unfold filterSmall? at h
      dsimp only at h
      by_cases hm : (boolMask bits
          (Literal.valueHolds ⟨atom, positive⟩ (.bool false))
          (Literal.valueHolds ⟨atom, positive⟩ (.bool true))).toNat = 0
      · rw [if_pos hm] at h
        simp only [Option.some.injEq] at h
        subst h
        exact WF_ofList _
      · rw [if_neg hm] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, by omega, boolMask_toNat_le_three ..⟩
  | false =>
      obtain ⟨hbits0, hbit0⟩ := hd
      unfold filterSmall? at h
      cases atom with
      | boolEq s b =>
          cases positive <;>
            (simp only [Option.some.injEq] at h; subst h; exact WF_ofList _)
      | intNe s x =>
          cases positive with
          | true =>
              dsimp only at h
              by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
              · rw [if_pos hout] at h
                simp only [Option.some.injEq] at h
                subst h
                exact ⟨hbits0, hbit0⟩
              · rw [if_neg hout] at h
                have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                by_cases hbit : bits.toNat.testBit (x - off).toNat = true
                · rw [if_pos hbit] at h
                  by_cases hk0 : (x - off).toNat = 0
                  · rw [if_pos hk0] at h
                    simp at h
                  · rw [if_neg hk0] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    have hk64 : (x - off).toNat < 64 := by
                      have h' : (((x - off).toNat : Int)) < 64 := by
                        rw [Int.toNat_of_nonneg (by omega)]
                        omega
                      exact_mod_cast h'
                    have hb0 : (bits &&& clearBitMask (x - off).toNat).toNat.testBit 0 = true := by
                      rw [UInt64.toNat_and, Nat.testBit_and, hbit0,
                        clearBitMask_testBit hk64 (by decide)]
                      have : ¬(0 = (x - off).toNat) := by omega
                      simp [this]
                    exact ⟨fun hz => by rw [hz] at hb0; simp at hb0, hb0⟩
                · rw [if_neg hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact ⟨hbits0, hbit0⟩
          | false =>
              dsimp only at h
              by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
              · rw [if_pos hout] at h
                simp only [Option.some.injEq] at h
                subst h
                exact WF_ofList _
              · rw [if_neg hout] at h
                by_cases hbit : bits.toNat.testBit (x - off).toNat = true
                · rw [if_pos hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact ⟨by decide, by decide⟩
                · rw [if_neg hbit] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact WF_ofList _
      | intLe s u =>
          cases positive with
          | true =>
              dsimp only at h
              by_cases htop : off + 63 ≤ u
              · rw [if_pos htop] at h
                simp only [Option.some.injEq] at h
                subst h
                exact ⟨hbits0, hbit0⟩
              · rw [if_neg htop] at h
                by_cases hbot : u < off
                · rw [if_pos hbot] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact WF_ofList _
                · rw [if_neg hbot] at h
                  by_cases hz : (bits &&& lowBitsMask ((u - off).toNat + 1)).toNat = 0
                  · rw [if_pos hz] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    exact WF_ofList _
                  · rw [if_neg hz] at h
                    by_cases hb0 : (bits &&& lowBitsMask ((u - off).toNat + 1)).toNat.testBit 0 = true
                    · rw [if_pos hb0] at h
                      simp only [Option.some.injEq] at h
                      subst h
                      exact ⟨hz, hb0⟩
                    · rw [if_neg hb0] at h
                      simp at h
          | false =>
              dsimp only at h
              by_cases hbot : u < off
              · rw [if_pos hbot] at h
                simp only [Option.some.injEq] at h
                subst h
                exact ⟨hbits0, hbit0⟩
              · rw [if_neg hbot] at h
                by_cases htop : off + 63 ≤ u
                · rw [if_pos htop] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  exact WF_ofList _
                · rw [if_neg htop] at h
                  simp at h

/-- The literal filter on `Dom` (the S2 interface).  On a hole interval
    the four integer literal shapes are handled structurally: an absent or
    endpoint `intNe` shortens the interval, an `intLe` cuts one side, and an
    `intNe` of negative polarity collapses to a singleton (or empty).  All
    other cases fall back to the exact enumerating `filter`. -/
def filterLit (l : Literal) (d : Dom) : Dom :=
  match d.rep with
  | .small isBool off bits =>
      (filterSmall? isBool off bits l.atom l.positive).getD (filter l.valueHolds d)
  | .holes lo hi hs =>
      (filterHoles? l.atom l.positive lo hi hs).getD (filter l.valueHolds d)
  | .general _ => filter l.valueHolds d

theorem enum_filterLit (l : Literal) (d : Dom) :
    enum (filterLit l d) = (enum d).filter l.valueHolds := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases l with
          | mk atom positive =>
              unfold filterLit
              dsimp only
              cases hf : filterSmall? isBool off bits atom positive with
              | none =>
                  simp only [Option.getD_none]
                  exact enum_filter _ _
              | some e =>
                  simp only [Option.getD_some]
                  exact enum_filterSmall? hf
      | general vs => exact enum_filter _ _
      | holes lo hi hs =>
          cases l with
          | mk atom positive =>
              unfold filterLit
              dsimp only
              cases hf : filterHoles? atom positive lo hi hs with
              | none =>
                  simp only [Option.getD_none]
                  exact enum_filter _ _
              | some e =>
                  simp only [Option.getD_some]
                  exact enum_filterHoles? hf

theorem memBool_filterLit {l : Literal} {d : Dom} {v : Value} :
    memBool (filterLit l d) v = true ↔ memBool d v = true ∧ l.valueHolds v = true := by
  rw [memBool_iff, enum_filterLit, memBool_iff, List.mem_filter]

theorem wf_filterLit (l : Literal) {d : Dom} (hd : WF d) :
    WF (filterLit l d) := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases l with
          | mk atom positive =>
              unfold filterLit
              dsimp only
              cases hf : filterSmall? isBool off bits atom positive with
              | none =>
                  simp only [Option.getD_none]
                  exact wf_filter _ _ hd
              | some e =>
                  simp only [Option.getD_some]
                  exact wf_filterSmall? hd hf
      | general vs =>
          unfold filterLit
          dsimp only
          exact wf_filter _ _ hd
      | holes lo hi hs =>
          cases l with
          | mk atom positive =>
              unfold filterLit
              dsimp only
              cases hf : filterHoles? atom positive lo hi hs with
              | none =>
                  simp only [Option.getD_none]
                  exact wf_filter _ _ hd
              | some e =>
                  simp only [Option.getD_some]
                  exact wf_filterHoles? hd hf


theorem card_filterLit_le (l : Literal) (d : Dom) : card (filterLit l d) ≤ card d := by
  rw [card_eq_length_enum, card_eq_length_enum, enum_filterLit]
  exact List.length_filter_le _ _

/-- Structural literal filter with the enumerating `filter`'s fixed point:
    when the literal keeps every value the original domain is returned.
    This keeps `filterFrame`/`filterSlots` definitionally stable on the
    no-drop branch (the equality-sensitive UIP proof cone relies on it)
    while the drop branch stays structural. -/
def filterLitKeep (l : Literal) (d : Dom) : Dom :=
  let d' := filterLit l d
  if d'.card = d.card then d else d'

/-- Dropping a value strictly shortens a list. -/
private theorem length_filter_lt_of_mem_false {α : Type} {p : α → Bool} {l : List α}
    {a : α} (ha : a ∈ l) (hp : p a = false) :
    (l.filter p).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      rw [List.filter_cons]
      split
      · rename_i hpb
        simp only [List.length_cons]
        cases ha with
        | head => rw [hp] at hpb; cases hpb
        | tail _ hb =>
            have := ih hb
            omega
      · rename_i hpb
        simp only [List.length_cons]
        cases ha with
        | head => exact Nat.lt_succ_of_le (List.length_filter_le p bs)
        | tail _ hb =>
            have := ih hb
            omega

/-- Exact enumeration of the fixed-point filter. -/
theorem enum_filterLitKeep (l : Literal) (d : Dom) :
    enum (filterLitKeep l d) = (enum d).filter l.valueHolds := by
  unfold filterLitKeep
  dsimp only
  by_cases h : (filterLit l d).card = d.card
  · rw [if_pos h]
    have hlen : ((enum d).filter l.valueHolds).length = (enum d).length := by
      rw [← card_eq_length_enum, ← h, card_eq_length_enum, enum_filterLit]
    have hall : ∀ v ∈ enum d, l.valueHolds v = true := by
      intro v hv
      cases hb : l.valueHolds v with
      | false =>
          have hlt := length_filter_lt_of_mem_false (p := l.valueHolds) hv hb
          omega
      | true => rfl
    exact (List.filter_eq_self.mpr hall).symm
  · rw [if_neg h, enum_filterLit]

/-- The fixed-point filter has the enumerating filter's length. -/
theorem length_filterLitKeep_eq (l : Literal) (d : Dom) :
    (filterLitKeep l d).length = (d.filter l.valueHolds).length := by
  rw [length_eq_card, card_eq_length_enum, length_eq_card, card_eq_length_enum,
    enum_filterLitKeep, ← enum_filter]

/-- Membership in the fixed-point filter. -/
theorem mem_filterLitKeep_iff {l : Literal} {d : Dom} {v : Value} :
    v ∈ filterLitKeep l d ↔ v ∈ d ∧ l.valueHolds v = true := by
  change Dom.memBool (filterLitKeep l d) v = true ↔
    Dom.memBool d v = true ∧ l.valueHolds v = true
  rw [memBool_iff, enum_filterLitKeep, List.mem_filter, ← memBool_iff]

/-- The fixed-point filter never increases the cardinality. -/
theorem card_filterLitKeep_le (l : Literal) (d : Dom) :
    card (filterLitKeep l d) ≤ card d := by
  unfold filterLitKeep
  dsimp only
  split
  · exact Nat.le_refl _
  · exact card_filterLit_le l d

/-- The fixed-point filter is the identity when the literal keeps every
    enumerated value. -/
theorem filterLitKeep_eq_self_of_forall {l : Literal} {d : Dom}
    (h : ∀ v ∈ enum d, l.valueHolds v = true) : filterLitKeep l d = d := by
  unfold filterLitKeep
  dsimp only
  have hcard : (filterLit l d).card = d.card := by
    rw [card_eq_length_enum, card_eq_length_enum, enum_filterLit]
    exact congrArg List.length (List.filter_eq_self.mpr h)
  rw [if_pos hcard]

theorem enum_filterLit_eq_filter_of {l : Literal} {d : Dom} {p : Value → Bool}
    (h : ∀ v ∈ enum d, l.valueHolds v = p v) :
    enum (filterLit l d) = (enum d).filter p := by
  rw [enum_filterLit]
  exact List.filter_congr h

theorem enum_eq_filter_of_forall {p : Value → Bool} {d : Dom}
    (h : ∀ v ∈ enum d, p v = true) :
    enum d = (enum d).filter p :=
  (List.filter_eq_self.mpr h).symm

theorem eq_int_of_mem_smallInts_enum {off : Int} {bits : UInt64} {v : Value}
    (h : v ∈ enum ⟨.small false off bits⟩) : ∃ i : Int, v = .int i := by
  change v ∈ (smallInts off bits).map Value.int at h
  obtain ⟨i, -, heq⟩ := List.mem_map.mp h
  exact ⟨i, heq.symm⟩

/-- Remove every value structurally equal to `x`.  The compact cases
    dispatch to the structural literal filter; mismatched value/domain
    sorts are the identity, and `.general` keeps the enumerating
    fallback. -/
def removeVal (x : Value) (d : Dom) : Dom :=
  match d.rep with
  | .small isBool _off _bits =>
      match isBool, x with
      | true, .bool b => filterLit ⟨.boolEq 0 b, false⟩ d
      | false, .int i => filterLit ⟨.intNe 0 i, true⟩ d
      | _, _ => d
  | .holes _lo _hi _hs =>
      match x with
      | .int i => filterLit ⟨.intNe 0 i, true⟩ d
      | _ => d
  | .general _vs => filter (fun v => !(v.eqB x)) d

theorem enum_removeVal (x : Value) (d : Dom) :
    enum (removeVal x d) = (enum d).filter (fun v => !(v.eqB x)) := by
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
        cases isBool with
        | true =>
            cases x with
            | bool b =>
                simp only [removeVal]
                apply enum_filterLit_eq_filter_of
                intro v hv
                obtain ⟨b', rfl⟩ := eq_bool_of_mem_smallBools hv
                cases b' <;> cases b <;> rfl
            | int i =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
                rfl
            | setOfInt s =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
                rfl
            | array xs =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
                rfl
        | false =>
            cases x with
            | bool b =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨a, rfl⟩ := eq_int_of_mem_smallInts_enum hv
                rfl
            | int i =>
                simp only [removeVal]
                apply enum_filterLit_eq_filter_of
                intro v hv
                obtain ⟨a, rfl⟩ := eq_int_of_mem_smallInts_enum hv
                rw [valueHolds_intNe_pos]
                by_cases h : a = i <;> simp [Value.eqB, h]
            | setOfInt s =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨a, rfl⟩ := eq_int_of_mem_smallInts_enum hv
                rfl
            | array xs =>
                simp only [removeVal]
                apply enum_eq_filter_of_forall
                intro v hv
                obtain ⟨a, rfl⟩ := eq_int_of_mem_smallInts_enum hv
                rfl
    | holes lo hi hs =>
        cases x with
        | bool b =>
            simp only [removeVal]
            apply enum_eq_filter_of_forall
            intro v hv
            obtain ⟨a, rfl⟩ := eq_int_of_mem_holes_enum hv
            rfl
        | int i =>
            simp only [removeVal]
            apply enum_filterLit_eq_filter_of
            intro v hv
            obtain ⟨a, rfl⟩ := eq_int_of_mem_holes_enum hv
            rw [valueHolds_intNe_pos]
            by_cases h : a = i <;> simp [Value.eqB, h]
        | setOfInt s =>
            simp only [removeVal]
            apply enum_eq_filter_of_forall
            intro v hv
            obtain ⟨a, rfl⟩ := eq_int_of_mem_holes_enum hv
            rfl
        | array xs =>
            simp only [removeVal]
            apply enum_eq_filter_of_forall
            intro v hv
            obtain ⟨a, rfl⟩ := eq_int_of_mem_holes_enum hv
            rfl
    | general vs =>
        simp only [removeVal]
        exact enum_filter _ _

theorem wf_removeVal (x : Value) (d : Dom) (hd : WF d) : WF (removeVal x d) := by
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
        cases isBool with
        | true =>
            cases x with
            | bool b =>
                simp only [removeVal]
                exact wf_filterLit _ hd
            | int i =>
                simp only [removeVal]
                exact hd
            | setOfInt s =>
                simp only [removeVal]
                exact hd
            | array xs =>
                simp only [removeVal]
                exact hd
        | false =>
            cases x with
            | bool b =>
                simp only [removeVal]
                exact hd
            | int i =>
                simp only [removeVal]
                exact wf_filterLit _ hd
            | setOfInt s =>
                simp only [removeVal]
                exact hd
            | array xs =>
                simp only [removeVal]
                exact hd
    | holes lo hi hs =>
        cases x with
        | bool b =>
            simp only [removeVal]
            exact hd
        | int i =>
            simp only [removeVal]
            exact wf_filterLit _ hd
        | setOfInt s =>
            simp only [removeVal]
            exact hd
        | array xs =>
            simp only [removeVal]
            exact hd
    | general vs =>
        simp only [removeVal]
        exact wf_filter _ _ hd

theorem card_removeVal_le (x : Value) (d : Dom) : card (removeVal x d) ≤ card d := by
  rw [card_eq_length_enum, card_eq_length_enum, enum_removeVal]
  exact List.length_filter_le _ _


end Dom

/-!
## Obligation ledger (D0-domain-design.md §6, 26 obligations)

Status legend: DISCHARGED (this stage proves it as stated, modulo the
constructor inventory), PARTIAL (the representation-level half is
proved; the named consumer-side restatement remains), PENDING (not in
this stage's scope; interface recorded).

Delivered API (all `Dom.*`).  Stage 1: `enum`, `WF`, `ofList`, `empty`,
`memBool` (+`memBool_iff`), `card` (+`card_eq_length_enum`,
`card_eq_zero_iff`), `domInts`, `minInt?`/`maxInt?` (+ the
`_eq_some_iff`/`_eq_none_iff` characterizations against the integer
views of `enum`), `filter` (+`enum_filter` for a predicate parameter),
`removeVal`, `ofDomain`/`toDomain` (+`enum_getD`, `enum_getElem?`,
`enum_ofDomain`), `FitsD` (+`fits_toDomain_iff`), `massD`
(+`massD_eq_map_length`), `frameDomainsD` (+`frameDomainsD_enum`,
`frameDomainsD_getD`), `allAssigns` bridges, `intViewableB`, `allIntB`,
`allBoolB`, `shapeTypedB_iff`, `intViewNodup_small`, plus the exactness
core `enum_ofList`/`WF_ofList`/`ofList_enum_eq_of_WF`/
`enum_injective_of_WF`.  Stage 2 adds: the `Rep.holes` variant with
`memHoles`/`holesInts` (+`mem_holesInts`, `mem_holes_enum_int`,
`pairwise_holesInts`), `ofHoles?` (+`ofHoles?_spec`, `enum_ofHoles?`,
`WF_ofHoles?`), `ofList_enum_holes`, `holesCard` (+
`holesCard_eq_of_WF`, `holesCard_eq_card_of_WF`), the bound fast paths
(`fastCond_lo`/`fastCond_hi`, `holes_min_mem`/`holes_min_le`/
`holes_max_mem`/`holes_max_ge`) and the conservation laws
`minInt?_eq_domInts_min`/`maxInt?_eq_domInts_max`/`domInts_eq_intView`,
`hasTrueB`/`hasFalseB` (+`_iff`, `_eq_any`), `Summary`/`summary`/
`summary_conservation`, `valueIntView_eq_value_intView`,
`filterLit`/`enum_filterLit`/`memBool_filterLit`,
`filterSlotsD`/`enum_filterSlotsD`/`filterSlotsD_length`/
`filterSlotsD_mass_le`, `filterFrameD`/`filterFrameD_enum`,
`massD_eq_frameMass`, `intViewNodup_holes`.  Stage 3 adds: the
compiler shapes `ofBoolShape` (+`enum_`/`WF_`/`ofBoolShape_eq_ofList`),
`ofIntRange` (+`enum_ofIntRange`, `WF_ofIntRange`,
`ofIntRange_eq_ofList`), `ofSetElemsShape` (+`enum_`/`WF_` and the
admissibility branches `ofSetElemsShape_small`/`ofSetElemsShape_holes`),
the window helpers `rangeInts` (+`_pairwise`/`_mem`/`_length`/`_lo_le`/
`_all_lt`) and `wf_small_intsToBits`, the gate facts
`card_pos_iff`/`intViewableB_holes`/`allIntB_holes`/`shapeTypedB_holes`.
The S4 summary bridge lives in the leaf module
`LeanFzn/Solver/Propagation/CompactDomainScan.lean` (see the DAG note
in that file): `SlotSum.ofSummary`,
`slotSumOfDomain_enum_{minInt,maxInt,hasTrue,hasFalse}`,
`slotSumOfDomain_enum`, `sumsOfArray_enum`.

Track 1 — exact equivalence:
 1. `memBool_iff` (D1): DISCHARGED for all three constructors
    (`small true`, `small false`, `holes`, `general`) and every `Value`
    constructor; `memBool` on `holes` is the O(#holes) endpoint test
    `lo <= i <= hi && i not a hole`.
 2. Round trip: DISCHARGED.  `enum (ofList xs) = xs` for *every* list
    (`enum_ofList`, exact, not merely a permutation; the `holes` case is
    `enum_ofHoles?` + `holesInts_holesInts`), and `ofList (enum d) = d`
    on `WF` (`ofList_enum_eq_of_WF`, holes case `ofList_enum_holes`).
    `WF` is the canonicality predicate; `ofHoles?` enters `holes` only
    for ascending, duplicate-free lists with span > 64 and
    `holes * 4 <= span`, and `WF` mirrors exactly those conditions.
 3. `enum_filterLit` (D3): DISCHARGED.  `filterLit` is structural on
    `.small` (`filterSmall?`: Boolean masks via `boolMask`, endpoint and
    interior `intNe` via `clearBitMask`, low `intLe` cuts via
    `lowBitsMask`, negative-`intNe` singletons) and on `.holes`
    (`filterHoles?`: endpoint/interior `intNe`, bound cuts, Boolean
    emptiness, negative-`intNe` singleton), falling back to
    `filter l.valueHolds` outside the guarded shapes;
    `enum_filterLit` stays unconditional, `wf_filterLit` preserves `WF`
    under `WF d`, and `card_filterLit_le` bounds the mass.
    `LiteralEval` supplies `Literal`/`valueHolds`; `FrameFilter` now
    calls `filterLit` (see the S2 note below).
 4. `enum_splitHead`, bounds filters, `single?`, card/min/max vs
    `domMinI`/`domMaxI`: PARTIAL.  `card_eq_length_enum`,
    `card_eq_zero_iff`, `minInt?_eq_some_iff`, `maxInt?_eq_some_iff`,
    `enum_removeVal` delivered structurally: `filterLit` on matching
    bool/int sorts, the identity on mismatched value/domain sorts, and
    the enumerating fallback on `.general`, with `wf_removeVal` and
    `card_removeVal_le`; on `holes` the bounds are the endpoint
    tests (O(#holes)) with the enumeration scan as fallback, and
    `holesCard` gives the D0 arithmetic `span - #holes` form
    (`holesCard_eq_card_of_WF`).  The literal `minInt? d = domMinI
    (enum d)` restatement still waits for the `Propagate.lean` import
    (S2); the conservation forms `minInt?_eq_domInts_min`/
    `maxInt?_eq_domInts_max` are the state-free content.
    `splitHead`/`single?` belong to S5.
 5. `Frame.denote_eq` and `filterSlots_length`/`filterSlots_mass_le`
    transports: DISCHARGED at the frame level: `frameDomainsD_enum`,
    `frameDomainsD_getD`, `allAssigns_frameDomainsD`,
    `enum_filterSlotsD`, `filterSlotsD_length`, `filterSlotsD_mass_le`
    and `filterFrameD_enum` mirror `Frame.domains`/`filterSlots`/
    `filterFrame` exactly (the `filterFrame` case-split is reproduced
    definitionally).
 6. `Frame.mass = Σ card` and branchCost/frontierCost: PARTIAL.
    `massD_eq_map_length` and `massD_eq_frameMass` delivered; the
    cost transports are S5.
 7. `Dom.sum` vs `SlotSum` and `literalImpossibleFast`: DISCHARGED
    for the summary fold (stage 3).  The four-field query surface
    (`minInt?`/`maxInt?`/`hasTrueB`/`hasFalseB`, bundled as
    `Dom.Summary`) plus `summary_conservation` is here; the fold-level
    induction against the real `SlotSum.step` is
    `CompactDomainScan.slotSumOfDomain_enum` (fieldwise
    `slotSumOfDomain_enum_{minInt,maxInt,hasTrue,hasFalse}` and the
    array form `sumsOfArray_enum`), so the scan's summaries are
    computed from `Dom` without enumerating.  `literalImpossibleFast`
    itself is S4.
 8. `eqB_sound`/`subsetB_sound` and the watch chain: PENDING (S4).
    Frozen interface: `Dom.eqB d d' := valuesEqB (enum d) (enum d')`,
    `Dom.subsetB d d' := (enum d).all (memBool d')`; both are one-sided
    soundness statements (`= true` direction only), matching D0 §5.2(6).
 9. Component equality transports (`productiveFast_eq`,
    `scanDatabaseFast_eq`, `scanDatabaseWatchIdx_fst_eq`,
    `nextPruningEventSched_fst_eq`, `backjumpStepFast_eq`): PENDING
    (S4/S5); none of their statements is touched here.

Track 2 — representation refinement:
10. `WF` preservation: DISCHARGED for the operations that produce
    domains (`WF_ofList`, `wf_filter`); `card`/bounds/queries are
    observations.  New operations must ship with a `WF` proof.
11. Ascending enumeration, exact cardinality: DISCHARGED.
    `pairwise_smallInts`/`pairwise_holesInts` (+ `pairwise_scanInts`,
    `smallInts_eq_cons`), `card_eq_length_enum`,
    `card_eq_zero_iff : card d = 0 <-> enum d = []` and the gate form
    `card_pos_iff : 0 < card d <-> enum d ≠ []` delivered; the
    `holes` cardinality has both the scan form (`card`) and the D0
    arithmetic form (`holesCard`, exact on `WF`).
12. Frame coverage (`FrameCovers`, `FrontierCovers`, `covers_split`):
    PENDING (S2/S5); the projection equation is delivered.
13. `Assignment.Fits`/`allAssigns` transport: DISCHARGED at the list
    level (`fits_toDomain_iff`, `allAssigns_toDomain`,
    `allAssigns_frameDomainsD`); `FrameCovers` instantiates it.
14. Restoration coherence (checkpoints, `resumeSibling`/`resumePending`,
    `syncAll`): PENDING (S5); no restoration surface is defined here.
15. Watch-table invariants (`WatchOK`, `WatchTableOK`, `guardB_spec`):
    PENDING (S4).  The unwired index must migrate with the same
    one-sided `eqB`/`subsetB` certificates (obligation 8).
16. Compiler exactness (`varDomain_values_iff`, `declSlots_mem`,
    `fits_mem_allAssigns`): PARTIAL (was PENDING).  The construction
    interface is delivered: `ofBoolShape` for `boolDom`,
    `ofIntRange` for `var lo..hi` (no wide materialization;
    `ofIntRange_eq_ofList` identifies it with the `ofList` normal form
    of `setElems (.interval lo hi)`), and `ofSetElemsShape` for
    `var {...}` with the exact admissibility branches
    (`ofSetElemsShape_small`/`ofSetElemsShape_holes`) and the total
    fallback laws (`enum_ofSetElemsShape`, `WF_ofSetElemsShape`).  The
    S6 work left is the `Compiler/Domain.lean` restatement
    (`varDomain`/`declSlot` emit `Dom`, `varDomain_values_iff` rewrites
    through `enum_ofBoolShape`/`enum_ofIntRange`/
    `enum_ofSetElemsShape`).

Track 3 — alternative search: obligations 17–21 are NOT STARTED and
NOT NEEDED at this stage: nothing here changes search order or
multiplicity.  `enum` is exact (`enum_ofList`) and `filter` satisfies
(D3) with list equality, so these stages are strictly
trace-preserving.

Track 4 — stronger propagation:
22. `Dom.sum` correctness against `SlotSum.step`: DISCHARGED (stage
    3).  `summary_conservation` (content) plus
    `CompactDomainScan.slotSumOfDomain_enum`/`sumsOfArray_enum` (the
    fold induction against the real `SlotSum.step`) prove that
    `slotSumOfDomain (enum d) = SlotSum.ofSummary (summary d)`, so the
    S4 scan may compute its summaries from `Dom` directly.
23. O(1) impossibility predicates with `memBool` fallback: PENDING
    (S4); `memBool` is the fallback tier, and the hole bounds are
    already O(#holes).
24. `PropagationContract` unchanged: PENDING (S2); no contract is
    edited here.
25. Bound/explanation producers (`rootFacts`, `narrowLo`/`narrowHi`,
    `snapLit`, `linExtract`, `syncCands`): PENDING (S2/S4);
    `minInt?`/`maxInt?` (with `minInt?_eq_domInts_min`/
    `maxInt?_eq_domInts_max`) are the state-free semantic anchors.
26. `domPruningOkB`/`mixedKitGateB` gate equality: PARTIAL.  Shape
    facts delivered for all constructors (`intViewableB_iff`,
    `allIntB_iff`, `allBoolB_iff`, `shapeTypedB_iff`,
    `intViewNodup_small`, `intViewNodup_holes`) plus the O(1) hole
    witnesses `intViewableB_holes`/`allIntB_holes`/`shapeTypedB_holes`
    and the nonemptiness form `card_pos_iff`; the gate-level
    equalities are S4–S6, where the compact cases answer them without
    a scan.

Exact next-stage interface:
 * S1 (`Core/Types.lean` alias): DONE.  `Domain` is `Dom`, and the
   runtime frames are compact.  The import graph now has
   `LiteralEval -> CompactDomain -> FrameFilter ->
   CompactDomainBridges`; nothing below `FrameFilter` imports it.
 * S2 (`FrameFilter.lean`): DONE.  `filterLit`/`filterLitKeep` live
   here; the positional `filterSlotsD`/`filterFrameD`/`frameDomainsD`/
   `massD` bridges live in `CompactDomainBridges.lean`.  The preserved
   statements are `enum_filterLit`, `enum_filterSlotsD`,
   `filterFrameD_enum`, `frameDomainsD_enum`,
   `massD_eq_map_length`/`massD_eq_frameMass`.
 * S4 (scan/index): replace the `SlotSum` construction over
   `Frame.domains` by `Dom.summary`.  The bridge is proved in the leaf
   module `CompactDomainScan.lean` (`slotSumOfDomain_enum`,
   `sumsOfArray_enum`; the scan's summary of `enum d` is
   `SlotSum.ofSummary (Dom.summary d)`), so S4 can either keep the
   companion as the transport module or inline its two definitions and
   delete it.  `literalImpossibleFast` and the remaining scan
   consumers are untouched here.
 * S6 (compiler): `Compiler/Domain.lean` swaps `VarDomain.values` for
   the delivered shapes: `ofBoolShape` for `boolDom`, `ofIntRange` for
   `intRange` (no wide materialization; `enum_ofIntRange` gives exactly
   `(setElems (.interval lo hi)).map Value.int`), `ofSetElemsShape` for
   `intSet xs` (total; the admissibility conditions are those of
   `ofSetElemsShape_small`/`ofSetElemsShape_holes`), and
   `varDomain_values_iff` rewrites through those enumeration laws; for
   `intSet` inputs that are not admissible the fallback laws
   (`enum_ofSetElemsShape`, `WF_ofSetElemsShape`) keep the statement
   unconditional.
 * S7 (public route / dispatcher switch): no new statements; the
   differential oracle is `enum_ofList`/`ofList_enum_eq_of_WF` (the
   `ofList` canonicalization of an enumeration is exact on `WF`), so
   legacy and compact operations can be compared on the same inputs
   throughout the migration.
 * Optional next increment of this file: structural `.general` `filter`
   paths and the hole-insertion/bound-bumping shapes left outside the
   guarded `.holes`/`.small` filters; the laws are already fixed by
   `enum_filter`/`enum_removeVal` and need no restatement.
-/

end LeanFzn.Solver.Propagation

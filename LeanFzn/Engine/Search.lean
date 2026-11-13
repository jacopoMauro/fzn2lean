/-
File: LeanFzn/Engine/Search.lean

N9: the Core search loop.  Entry gate + domain conversion (with the
in-range/converted-domain guard that makes every propagator's initial
`hinit` obligation realisable), seed clauses, root propagation, CDCL
decisions, first-UIP conflicts, learned clauses and backjumping, and a
final `fitsB`/`accepts` check.  The loop is fuel-bounded and total; every
internal doubt returns `.gaveUp`, never a claim.

Soundness is proved here without state invariants: the only `.unsat`
leaf is an entailed empty clause produced by N8 `analyze`, and the only
`.sat` leaf re-checks `fitsB`/`accepts`.  N7's `Good`/`InitInv` are used
to justify the entry state and are available to callers, but the search
soundness argument itself needs no invariant threading.
-/
import LeanFzn.Engine.Queue
import LeanFzn.Engine.Analyze
import LeanFzn.Engine.Reduce
import LeanFzn.Engine.Proofs.PruneSound
import LeanFzn.Engine.Proofs.Queue.Root
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.AllDiff
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Linear
import LeanFzn.Engine.Props.Arith
import LeanFzn.Engine.Props.Order
import LeanFzn.Engine.Props.LinearExt
import LeanFzn.Engine.Props.BoolExt
import LeanFzn.Engine.Props.Element
import LeanFzn.Engine.Props.SetIn
import LeanFzn.Compiler.SeedClauses
import LeanFzn.Solver.Propagation.EngineCore
import LeanFzn.Solver.Propagation.Gates
import LeanFzn.Integration.Config.Parse
import LeanFzn.Integration.Config.Annotations

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

namespace LeanFzn.Engine

/-! ## Domain conversion and the entry guard -/

/-- Convert a list of compiled domains, appending one converted domain at a
time.  The accumulator is the converted prefix; a `none` anywhere is the
only entry give-up beyond the executable gate. -/
def convertDomainsAux (ds : List Dom) (acc : Array DomC) : Option (Array DomC) :=
  match ds with
  | [] => some acc
  | d :: ds =>
      match DomC.ofDom? d with
      | none => none
      | some c => convertDomainsAux ds (acc.push c)

/-- Convert every compiled domain. -/
def convertDomains (ds : List Dom) : Option (Array DomC) :=
  convertDomainsAux ds #[]

/-- The conversion spec: the accumulator's entries are preserved and each
source domain is converted to the corresponding appended entry. -/
theorem convertDomainsAux_spec (ds : List Dom) :
    ∀ (acc : Array DomC) (cs : Array DomC), convertDomainsAux ds acc = some cs →
      cs.size = acc.size + ds.length ∧
      (∀ s, s < acc.size → cs.getD s DomC.empty = acc.getD s DomC.empty) ∧
      (∀ s, s < ds.length →
        DomC.ofDom? (ds.getD s Dom.empty) = some (cs.getD (acc.size + s) DomC.empty)) := by
  induction ds with
  | nil =>
      intro acc cs h
      simp only [convertDomainsAux, Option.some.injEq] at h
      subst h
      refine ⟨by simp, ?_, ?_⟩
      · intro s _; rfl
      · intro s hs; exact absurd hs (Nat.not_lt_zero s)
  | cons d ds ih =>
      intro acc cs h
      simp only [convertDomainsAux] at h
      split at h
      · simp at h
      · rename_i c hc
        obtain ⟨hsize, hpre, hpost⟩ := ih (acc.push c) cs h
        refine ⟨?_, ?_, ?_⟩
        · rw [hsize, Array.size_push, List.length_cons]
          omega
        · intro s hs
          have hs' : s < (acc.push c).size := by rw [Array.size_push]; omega
          rw [hpre s hs']
          rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
          rw [if_neg (by omega)]
        · intro s hs
          cases s with
          | zero =>
              have h0 : cs.getD acc.size DomC.empty = c := by
                have h1 := hpre acc.size (by simp)
                rw [h1]
                simp
              simpa [List.getD_cons_zero, Nat.add_zero, h0] using hc
          | succ k =>
              have hk : k < ds.length := by simpa using hs
              have hk' := hpost k hk
              have hsize' : (acc.push c).size + k = acc.size + (k + 1) := by
                rw [Array.size_push]; omega
              rw [← hsize']
              simpa [List.getD_cons_succ] using hk'

/-- From a successful conversion, every in-range compiled domain is the
converted one.  This is the `hinit` source used by `initState`. -/
theorem convertDomains_spec {ds : List Dom} {cs : Array DomC}
    (h : convertDomains ds = some cs) :
    cs.size = ds.length ∧
    (∀ s, s < ds.length →
      DomC.ofDom? (ds.getD s Dom.empty) = some (cs.getD s DomC.empty)) := by
  obtain ⟨hsize, -, hpost⟩ :=
    convertDomainsAux_spec ds #[] cs (by simpa [convertDomains] using h)
  refine ⟨by simpa using hsize, ?_⟩
  intro s hs
  simpa using hpost s hs

/-- Convert every compiled domain exactly once per `initState`.  The result
mirrors `p.domains`, so a readiness test can index it instead of running
`DomC.ofDom?` on the `List` for every `(constraint, slot)` pair. -/
def convertedDomains (p : CompiledProblem DomConstraint) : Array (Option DomC) :=
  p.domainsArray.map DomC.ofDom?

/-- Looking up the conversion mirror is the same as converting the compiled
domain at that slot. -/
theorem convertedDomains_getD (p : CompiledProblem DomConstraint) (s : Nat) :
    (convertedDomains p).getD s none =
      DomC.ofDom? (p.domains.getD s Dom.empty) := by
  unfold convertedDomains
  rw [Array.getD_eq_getElem?_getD, Array.getElem?_map]
  by_cases hs : s < p.domainsArray.size
  · rw [Array.getElem?_eq_getElem hs, Option.map_some, Option.getD_some,
      ← domainsArray_getD_eq p s]
    rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hs]
    rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hs)]
    simp only [Option.map_none, Option.getD_none]
    have hlen : p.domains.length ≤ s := by
      rw [← domainsArray_size p]
      exact Nat.le_of_not_lt hs
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
    rfl

/-- Per-slot readiness against a precomputed conversion mirror. -/
def slotReadyConvB (converted : Array (Option DomC)) (init : Array DomC) (s : Nat) : Bool :=
  decide (converted.getD s none = some (init.getD s DomC.empty))

/-- Total per-slot readiness test: the compiled domain at `s` converts to
exactly the converted initial domain at `s`.  Out-of-range or malformed
slots fail this equality (`DomC.ofDom? Dom.empty = none`). -/
def slotReadyB (p : CompiledProblem DomConstraint) (init : Array DomC) (s : Nat) : Bool :=
  decide (DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))

/-- Bool-to-Prop spec of `slotReadyB`. -/
theorem slotReadyB_spec {p : CompiledProblem DomConstraint} {init : Array DomC} {s : Nat}
    (h : slotReadyB p init s = true) :
    DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) :=
  of_decide_eq_true h

/-- The mirror-indexed readiness test is exactly `slotReadyB`; this keeps
concrete readiness evaluations reducing through the original definition. -/
@[simp] theorem slotReadyConvB_convertedDomains (p : CompiledProblem DomConstraint)
    (init : Array DomC) (s : Nat) :
    slotReadyConvB (convertedDomains p) init s = slotReadyB p init s := by
  unfold slotReadyConvB slotReadyB
  rw [convertedDomains_getD]

/-- Bool-to-Prop spec of the mirror-indexed readiness test. -/
theorem slotReadyConvB_spec {p : CompiledProblem DomConstraint} {init : Array DomC} {s : Nat}
    (h : slotReadyConvB (convertedDomains p) init s = true) :
    DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) := by
  rw [slotReadyConvB, convertedDomains_getD] at h
  exact of_decide_eq_true h

/-- Total initial-state readiness test: every slot read by every constraint
is in range and its converted domain matches `init`.  The conversion mirror
is computed once per call rather than once per `(constraint, slot)`. -/
def initReady (p : CompiledProblem DomConstraint) (init : Array DomC) : Bool :=
  let converted := convertedDomains p
  p.constraints.toArray.all fun dc =>
    (dcSlotsFull dc).toArray.all fun s => slotReadyConvB converted init s

/-- Bool-to-Prop spec of `initReady`: it yields the per-constraint `hinit`
obligation of N6/N6b. -/
theorem initReady_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    (h : initReady p init = true) :
    ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) := by
  intro dc hdc s hs
  have h1 : (p.constraints.toArray.all fun dc =>
      (dcSlotsFull dc).toArray.all fun s =>
        slotReadyConvB (convertedDomains p) init s) = true := h
  have h2 := (Array.all_eq_true'.mp h1) dc (List.mem_toArray.mpr hdc)
  exact slotReadyConvB_spec ((Array.all_eq_true'.mp h2) s (List.mem_toArray.mpr hs))

/-- N7's total `InitInv` follows from the conversion and the guard.  (The
guard is not needed: conversion alone yields the in-range equality, and
out-of-range slots are empty on both sides.) -/
theorem initInv_of_convertDomains {p : CompiledProblem DomConstraint} {init : Array DomC}
    (hconv : convertDomains p.domains = some init) : InitInv p init := by
  intro s
  by_cases hs : s < p.domains.length
  · have hspec := (convertDomains_spec hconv).2 s hs
    rw [hspec]
    simp
  · have hge : p.domains.length ≤ s := Nat.le_of_not_lt hs
    have hpd : p.domains.getD s Dom.empty = Dom.empty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    have hsize : init.size = p.domains.length := (convertDomains_spec hconv).1
    have hid : init.getD s DomC.empty = DomC.empty := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [hpd, DomC.ofDom?_empty, hid]
    rfl

/-! ## The propagator table -/

/-- The dedicated sound propagators: the `Ne`, Boolean, bounded-linear and
arithmetic families, and the generic `propCheckV2With` for every other
family.  Each carries the explicit constraint-membership proof, and every
domain-reading propagator also carries the initial-domain `hinit` obtained
from `initReady`.  `boolClauseSlot` is additionally seeded as an ordinary
clause, so it has both a clause and a dedicated event-driven propagator. -/
def propsOf (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .neSlot i j =>
        nePropWith p T init i j
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .allDiff is =>
        allDiffPropWith p T init is
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            simpa [dcSlotsFull] using h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolClauseSlot ps ns =>
        boolClausePropWith p T ps ns
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLe cs is b =>
        linLePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .plusSlot i j k =>
        plusPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .timesSlot i j k =>
        timesPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minSlot i j k =>
        minPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxSlot i j k =>
        maxPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .absSlot i k =>
        absPropWith p T i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minPair o0 o1 r =>
        minPairPropWith p T o0 o1 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxPair o0 o1 r =>
        maxPairPropWith p T o0 o1 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minGen os r =>
        minGenPropWith p T os r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxGen os r =>
        maxGenPropWith p T os r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .divGen o1 o2 r =>
        divPropWith p T o1 o2 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .modGen o1 o2 r =>
        modPropWith p T o1 o2 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .eqSlot i j =>
        eqPropWith p T init i j
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leSlot i j =>
        lePropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltSlot i j =>
        ltPropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstHi i c =>
        leConstHiPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstLo i c =>
        leConstLoPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstHi i c =>
        ltConstHiPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstLo i c =>
        ltConstLoPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .bool2intSlot i k =>
        bool2intPropWith p T i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .eqReifSlot i j r =>
        eqReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leReifSlot i j r =>
        leReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .neReifSlot i j r =>
        neReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linEq cs is b =>
        linEqPropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNe cs is b =>
        linNePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linEqReif cs is b r =>
        linEqReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLeReif cs is b r =>
        linLeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNeReif cs is b r =>
        linNeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolNotSlot i j =>
        boolNotPropChoice p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolAndSlot i j k =>
        boolAndPropChoice p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolOrSlot i j k =>
        boolOrPropChoice p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolEqSlot i j =>
        boolEqPropChoice p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayBoolAndSlot is k =>
        arrayBoolAndPropFast p T is k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayIntElementSlot xs i k =>
        arrayIntElementPropWith p T xs i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarIntElementSlot is i k =>
        arrayVarIntElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarBoolElementSlot is i k =>
        arrayVarBoolElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .setInReifSlot i s r =>
        setInReifPropWith p T i s r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- Every propagator registered by `propsOf` satisfies the pruning
contract: each explicit family wrapper supplies the per-family
`*_prune_lit_none` fact, and the generic fallback never prunes. -/
theorem propsOf_pruneSound (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    PropsSound p T (propsOf p T init hinit) := by
  intro id pr hid
  have hpr : pr ∈ propsOf p T init hinit := by
    rw [Array.mem_iff_getElem?]
    exact ⟨id, hid⟩
  unfold propsOf at hpr
  rw [Array.mem_map] at hpr
  obtain ⟨x, _, hxpr⟩ := hpr
  rw [← hxpr]
  split
  case h_1 i j heq =>
    exact nePropWith_pruneSound init i j _ (heq ▸ List.mem_toArray.mp x.2)
  case h_2 is heq =>
    exact allDiffPropWith_pruneSound init is _ (heq ▸ List.mem_toArray.mp x.2)
  case h_3 ps ns heq =>
    exact boolClausePropWith_pruneSound ps ns (heq ▸ List.mem_toArray.mp x.2)
  case h_4 cs is b heq =>
    exact linLePropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_5 i j k heq =>
    exact plusPropWith_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_6 i j k heq =>
    exact timesPropWith_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_7 i j k heq =>
    exact minPropWith_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_8 i j k heq =>
    exact maxPropWith_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_9 i k heq =>
    exact absPropWith_pruneSound i k (heq ▸ List.mem_toArray.mp x.2)
  case h_10 o0 o1 r heq =>
    exact minPairPropWith_pruneSound o0 o1 r (heq ▸ List.mem_toArray.mp x.2)
  case h_11 o0 o1 r heq =>
    exact maxPairPropWith_pruneSound o0 o1 r (heq ▸ List.mem_toArray.mp x.2)
  case h_12 os r heq =>
    exact minGenPropWith_pruneSound os r (heq ▸ List.mem_toArray.mp x.2)
  case h_13 os r heq =>
    exact maxGenPropWith_pruneSound os r (heq ▸ List.mem_toArray.mp x.2)
  case h_14 o1 o2 r heq =>
    exact divPropWith_pruneSound o1 o2 r (heq ▸ List.mem_toArray.mp x.2)
  case h_15 o1 o2 r heq =>
    exact modPropWith_pruneSound o1 o2 r (heq ▸ List.mem_toArray.mp x.2)
  case h_16 i j heq =>
    exact eqPropWith_pruneSound init i j _ (heq ▸ List.mem_toArray.mp x.2)
  case h_17 i j heq =>
    exact lePropWith_pruneSound i j (heq ▸ List.mem_toArray.mp x.2)
  case h_18 i j heq =>
    exact ltPropWith_pruneSound i j (heq ▸ List.mem_toArray.mp x.2)
  case h_19 i c heq =>
    exact leConstHiPropWith_pruneSound i c (heq ▸ List.mem_toArray.mp x.2)
  case h_20 i c heq =>
    exact leConstLoPropWith_pruneSound i c (heq ▸ List.mem_toArray.mp x.2)
  case h_21 i c heq =>
    exact ltConstHiPropWith_pruneSound i c (heq ▸ List.mem_toArray.mp x.2)
  case h_22 i c heq =>
    exact ltConstLoPropWith_pruneSound i c (heq ▸ List.mem_toArray.mp x.2)
  case h_23 i k heq =>
    exact bool2intPropWith_pruneSound i k (heq ▸ List.mem_toArray.mp x.2)
  case h_24 i j r heq =>
    exact eqReifPropWith_pruneSound i j r (heq ▸ List.mem_toArray.mp x.2)
  case h_25 i j r heq =>
    exact leReifPropWith_pruneSound i j r (heq ▸ List.mem_toArray.mp x.2)
  case h_26 i j r heq =>
    exact neReifPropWith_pruneSound i j r (heq ▸ List.mem_toArray.mp x.2)
  case h_27 cs is b heq =>
    exact linEqPropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_28 cs is b heq =>
    exact linNePropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_29 cs is b r heq =>
    exact linEqReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_30 cs is b r heq =>
    exact linLeReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_31 cs is b r heq =>
    exact linNeReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_32 i j heq =>
    exact boolNotPropChoice_pruneSound i j (heq ▸ List.mem_toArray.mp x.2)
  case h_33 i j k heq =>
    exact boolAndPropChoice_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_34 i j k heq =>
    exact boolOrPropChoice_pruneSound i j k (heq ▸ List.mem_toArray.mp x.2)
  case h_35 i j heq =>
    exact boolEqPropChoice_pruneSound i j (heq ▸ List.mem_toArray.mp x.2)
  case h_36 is k heq =>
    exact arrayBoolAndPropFast_pruneSound is k (heq ▸ List.mem_toArray.mp x.2)
  case h_37 xs i k heq =>
    exact arrayIntElementPropWith_pruneSound xs i k (heq ▸ List.mem_toArray.mp x.2)
  case h_38 is i k heq =>
    exact arrayVarIntElementPropWith_pruneSound is i k (heq ▸ List.mem_toArray.mp x.2)
  case h_39 is i k heq =>
    exact arrayVarBoolElementPropWith_pruneSound is i k (heq ▸ List.mem_toArray.mp x.2)
  case h_40 i s r heq =>
    exact setInReifPropWith_pruneSound p T i s r
      (heq ▸ List.mem_toArray.mp x.2)
  case h_41 =>
    exact propCheckV2With_pruneSound p T x.val init
      (hinit x.val (List.mem_toArray.mp x.2)) (List.mem_toArray.mp x.2)

/-- Intern a denotation-level clause and add it to the database. -/
def addClauseDen (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    EngineState p T × EClause p T × Nat :=
  let res := st.table.internArray ls.toArray
  let e := EClause.ofLits p T res.1 (by
    have h' := LitTable.decodeClause_internArray_snd (T := st.table) (ls := ls.toArray)
    have hdec : T.decodeClause res.1 = ls := by
      change res.2.decodeClause res.1 = ls
      simpa using h'
    rw [hdec]
    exact h)
  let (db, id) := st.db.add e
  ({ st with table := res.2, db := db }, e, id)

/-- Entailment of a seed clause from its membership in `seedClauses`. -/
theorem seedEntailed (p : CompiledProblem DomConstraint) {c : Clause}
    (hc : c ∈ seedClauses p.constraints) : Entailed p c :=
  fun _a _ha hacc =>
    seedClauses_entailed (fun dc hdc => List.all_eq_true.mp hacc dc hdc) c hc

/-- Add every seed clause to the database. -/
def addSeedClausesFrom (p : CompiledProblem DomConstraint) (T : LitTable)
    (cs : List {c : Clause // c ∈ seedClauses p.constraints})
    (st : EngineState p T) : EngineState p T :=
  cs.foldl (fun st x => (addClauseDen p T st x.1 (seedEntailed p x.2)).1) st

/-- Add all `bool_clause` seeds, then report the first live empty clause.
Adding all seeds (rather than stopping at the first empty one) keeps the
entry simple; `ClauseDB.emptyConflict?_spec` supplies the soundness
content of the returned clause. -/
def addSeedClauses (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) : EngineState p T × Option (EClause p T) :=
  let st' := addSeedClausesFrom p T (seedClauses p.constraints).attach st
  (st', st'.db.emptyConflict?)

theorem addClauseDen_doms (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.doms = st.doms := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_trail (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.trail = st.trail := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_changeIndex (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.changeIndex = st.changeIndex := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_reasonCap (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.reasonCap = st.reasonCap := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_levelStart (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.levelStart = st.levelStart := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_level (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.level = st.level := by
  unfold addClauseDen
  dsimp only

theorem addClauseDen_histInv {init : Array DomC} {st : EngineState p T}
    (hh : HistInv init st) (ls : List Literal) (h : Entailed p ls) :
    HistInv init (addClauseDen p T st ls h).1 := by
  apply HistInv.congr hh
  · exact addClauseDen_doms p T st ls h
  · exact addClauseDen_trail p T st ls h
  · intro s
    simp only [EngineState.changeList, addClauseDen_changeIndex p T st ls h]
  · exact addClauseDen_changeIndex p T st ls h
  · exact addClauseDen_levelStart p T st ls h
  · exact addClauseDen_level p T st ls h
  · exact addClauseDen_reasonCap p T st ls h

theorem addSeedClausesFrom_doms (p : CompiledProblem DomConstraint) (T : LitTable)
    (cs : List {c : Clause // c ∈ seedClauses p.constraints})
    (st : EngineState p T) :
    (addSeedClausesFrom p T cs st).doms = st.doms := by
  unfold addSeedClausesFrom
  induction cs generalizing st with
  | nil => rfl
  | cons x rest ih =>
      rw [List.foldl_cons, ih]
      exact addClauseDen_doms p T st x.1 (seedEntailed p x.2)

theorem addSeedClausesFrom_histInv {init : Array DomC} {st : EngineState p T}
    (cs : List {c : Clause // c ∈ seedClauses p.constraints})
    (hh : HistInv init st) :
    HistInv init (addSeedClausesFrom p T cs st) := by
  unfold addSeedClausesFrom
  induction cs generalizing st with
  | nil => exact hh
  | cons x rest ih =>
      rw [List.foldl_cons]
      exact ih (addClauseDen_histInv hh x.1 (seedEntailed p x.2))

theorem addSeedClauses_fst_doms (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) :
    (addSeedClauses p T st).1.doms = st.doms := by
  unfold addSeedClauses
  exact addSeedClausesFrom_doms p T _ st

theorem addSeedClauses_fst_histInv {init : Array DomC} {st : EngineState p T}
    (hh : HistInv init st) :
    HistInv init (addSeedClauses p T st).1 := by
  unfold addSeedClauses
  exact addSeedClausesFrom_histInv _ hh

/-- Adding an interned clause changes only the table and the database. -/
theorem addClauseDen_props (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    (addClauseDen p T st ls h).1.props = st.props := by
  unfold addClauseDen
  dsimp only

/-- Replacing the clause database with an invariant one preserves `RootInv`. -/
theorem dbUpdate_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (db : ClauseDB p T) (hdb : db.Inv) (hlits : db.LitsWF st.table) :
    RootInv p T init { st with db := db } :=
  RootInv.of_eq (st' := { st with db := db }) h rfl rfl (fun _ => rfl) rfl rfl
    rfl rfl h.table_inv hlits hdb

/-- Root propagation leaves the database unchanged. -/
theorem propagateUnits_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init
      { st with db := (st.db.propagateUnits p T st.doms).1 } := by
  refine dbUpdate_rootInv h _ (ClauseDB.propagateUnits_inv st.db st.doms h.db_inv) ?_
  rw [ClauseDB.propagateUnits_fst]
  exact h.lits_wf

/-- Adding one interned clause preserves `RootInv`. -/
theorem addClauseDen_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (ls : List Literal) (he : Entailed p ls) :
    RootInv p T init (addClauseDen p T st ls he).1 := by
  refine RootInv.of_eq (st' := (addClauseDen p T st ls he).1) h
    (addClauseDen_doms p T st ls he) (addClauseDen_trail p T st ls he) ?_
    (addClauseDen_changeIndex p T st ls he) (addClauseDen_levelStart p T st ls he)
    (addClauseDen_level p T st ls he) (addClauseDen_reasonCap p T st ls he) ?_ ?_ ?_
  · intro s
    simp only [EngineState.changeList, addClauseDen_changeIndex p T st ls he]
  · unfold addClauseDen
    dsimp only
    exact LitTable.internArray_inv h.table_inv ls.toArray
  · unfold addClauseDen
    dsimp only
    refine ClauseDB.LitsWF.add
      (ClauseDB.LitsWF.mono_table
        (LitTable.internArray_append_only st.table ls.toArray) h.lits_wf) _ ?_
    intro l hl
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp (by simpa using hl)
    exact LitTable.internArray_wf h.table_inv.table_wf ls.toArray i l hi
  · unfold addClauseDen
    dsimp only
    exact ClauseDB.add_inv st.db _ h.db_inv

theorem addSeedClausesFrom_props (p : CompiledProblem DomConstraint) (T : LitTable)
    (cs : List {c : Clause // c ∈ seedClauses p.constraints})
    (st : EngineState p T) :
    (addSeedClausesFrom p T cs st).props = st.props := by
  unfold addSeedClausesFrom
  induction cs generalizing st with
  | nil => rfl
  | cons x rest ih =>
      rw [List.foldl_cons, ih]
      exact addClauseDen_props p T st x.1 (seedEntailed p x.2)

theorem addSeedClausesFrom_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {cs : List {c : Clause // c ∈ seedClauses p.constraints}}
    (h : RootInv p T init st) :
    RootInv p T init (addSeedClausesFrom p T cs st) := by
  unfold addSeedClausesFrom
  induction cs generalizing st with
  | nil => exact h
  | cons x rest ih =>
      rw [List.foldl_cons]
      exact ih (addClauseDen_rootInv h x.1 (seedEntailed p x.2))

theorem addSeedClauses_fst_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init (addSeedClauses p T st).1 := by
  unfold addSeedClauses
  exact addSeedClausesFrom_rootInv h

theorem addSeedClauses_fst_props (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) :
    (addSeedClauses p T st).1.props = st.props := by
  unfold addSeedClauses
  exact addSeedClausesFrom_props p T _ st

/-- The problem seen by entry/root propagation: the same box and
constraints, with the seed clauses as its clause list. -/
def propagationProblem (p : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := p.names
    domains := p.domains
    constraints := p.constraints
    objective := ()
    clauses := seedClauses p.constraints }

/-- The fresh arrays of the initial state, before registration. -/
def initStateBase (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) : EngineState p T :=
  { table := T
    doms := doms
    trail := #[]
    levelStart := #[0]
    level := 0
    changeIndex := Array.replicate doms.size (#[] : Array Nat)
    db := {}
    reasons := #[]
    reasonCap := #[0]
    props := props
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := ⟨Array.replicate doms.size (0.0 : Float)⟩
    activityInc := 1.0
    activityHeap := #[]
    phases := #[]
    restarts := 0
    slotWeight := Array.replicate doms.size 0
    stats := {} }

/-- The state construction after domain conversion: register the
propagators/subscribers and enqueue them. -/
def initStateCore (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) : EngineState p T :=
  (List.range props.size).foldl (fun st i => enqueueProp st i)
    (registerProps (initStateBase p T doms props))

theorem initStateBase_histInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    HistInv doms (initStateBase p T doms props) := by
  refine ⟨slotHistory_init doms (initStateBase p T doms props) rfl rfl ?_,
    trailInv_init (st := initStateBase p T doms props) rfl rfl rfl ?_ rfl⟩
  · intro s
    simp only [EngineState.changeList, initStateBase, Array.getD]
    by_cases hs : s < doms.size <;> simp [hs]
  · intro s
    simp only [EngineState.changeList, initStateBase, Array.getD]
    by_cases hs : s < doms.size <;> simp [hs]

/-- Build the initial state, or `none` when the entry fragment rejects the
problem (gate failure, failed conversion, or the `initReady` guard). -/
def initState (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  if !gateOkFast (propagationProblem p) then none
  else
    match convertDomains p.domains with
    | none => none
    | some doms =>
        if hready : initReady p doms = true then
          let hinitAll := initReady_spec hready
          let props := propsOf p T doms hinitAll
          some (initStateCore p T doms props)
        else none

/-- Build the initial state from an already converted domain array.  This is
`initState` with the conversion match supplied by the caller.  The conversion
equality is a proof argument only; the executable path still runs the entry
gate and the `initReady` guard. -/
def initStatePrepared (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (_hconv : convertDomains p.domains = some doms) :
    Option (EngineState p T) :=
  if !gateOkFast (propagationProblem p) then none
  else
    if hready : initReady p doms = true then
      let hinitAll := initReady_spec hready
      let props := propsOf p T doms hinitAll
      some (initStateCore p T doms props)
    else none

/-- The prepared entry equals the ordinary entry when the supplied domains are
the conversion result. -/
theorem initStatePrepared_eq {p : CompiledProblem DomConstraint} {T : LitTable}
    {doms : Array DomC} (hconv : convertDomains p.domains = some doms) :
    initStatePrepared p T doms hconv = initState p T := by
  unfold initStatePrepared initState
  rw [hconv]

theorem initStateBase_table (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    (initStateBase p T doms props).table = T := rfl

/-- The constructed state keeps the converted domains. -/
theorem initStateCore_doms (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    (initStateCore p T doms props).doms = doms := by
  unfold initStateCore
  rw [list_foldl_doms (l := List.range props.size)
    (f := fun st i => enqueueProp st i) (hf := fun st i => enqueueProp_doms st i)]
  rw [registerProps_doms]
  rfl

/-- The constructed state satisfies the history/trail invariants. -/
theorem initStateCore_histInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    HistInv doms (initStateCore p T doms props) := by
  unfold initStateCore
  exact range_enqueueProp_histInv
    (registerProps_histInv (initStateBase_histInv p T doms props)) props.size

theorem initState_histInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : initState p T = some st) :
    HistInv st.doms st := by
  unfold initState at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [initStateCore_doms]
        exact initStateCore_histInv p T _ _
      · simp at h

/-- The initial state carries the conversion equation for every in-range
slot. -/
theorem initState_initConv {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : initState p T = some st) :
    InitConv p st.doms := by
  unfold initState at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_doms]
            exact ⟨(convertDomains_spec hc).2⟩
          · simp [hr] at h
  | false => simp [hg] at h

/-! ### Root invariant at entry -/

theorem array_foldl_trail {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).trail = st.trail) (st : EngineState p T) :
    (l.foldl f st).trail = st.trail := by
  rw [← Array.foldl_toList]
  exact list_foldl_trail l.toList f hf st

theorem array_foldl_changeIndex {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).changeIndex = st.changeIndex) (st : EngineState p T) :
    (l.foldl f st).changeIndex = st.changeIndex := by
  rw [← Array.foldl_toList]
  exact list_foldl_changeIndex l.toList f hf st

theorem array_foldl_reasonCap {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).reasonCap = st.reasonCap) (st : EngineState p T) :
    (l.foldl f st).reasonCap = st.reasonCap := by
  rw [← Array.foldl_toList]
  exact list_foldl_reasonCap l.toList f hf st

theorem array_foldl_levelStart {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).levelStart = st.levelStart) (st : EngineState p T) :
    (l.foldl f st).levelStart = st.levelStart := by
  rw [← Array.foldl_toList]
  exact list_foldl_levelStart l.toList f hf st

theorem array_foldl_level {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).level = st.level) (st : EngineState p T) :
    (l.foldl f st).level = st.level := by
  rw [← Array.foldl_toList]
  exact list_foldl_level l.toList f hf st

theorem list_foldl_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, RootInv p T init st → RootInv p T init (f st a)) :
    ∀ st, RootInv p T init st → RootInv p T init (l.foldl f st) := by
  intro st h
  induction l generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih (f st x) (hf st x h)

theorem registerProps_go_trail (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).trail = st.trail := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).trail = st.trail
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_trail
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_trail]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_changeIndex (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).changeIndex = st.changeIndex := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).changeIndex = st.changeIndex
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_changeIndex
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_changeIndex]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_reasonCap (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).reasonCap = st.reasonCap := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).reasonCap = st.reasonCap
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_reasonCap
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_reasonCap]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_levelStart (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).levelStart = st.levelStart := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).levelStart = st.levelStart
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_levelStart
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_levelStart]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_level (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).level = st.level := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).level = st.level
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_level
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_level]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_table (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).table = st.table := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).table = st.table
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          rw [← Array.foldl_toList]
          exact list_foldl_table _ _ (fun st' x => by
            rcases x with ⟨sv, k'⟩
            dsimp only
            simp only [ensureSubs_table]) _
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_db (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).db = st.db := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).db = st.db
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          rw [← Array.foldl_toList]
          exact list_foldl_db _ _ (fun st' x => by
            rcases x with ⟨sv, k'⟩
            dsimp only
            simp only [ensureSubs_db]) _
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_trail (st : EngineState p T) :
    (registerProps st).trail = st.trail :=
  registerProps_go_trail st.props.size 0 st

theorem registerProps_changeIndex (st : EngineState p T) :
    (registerProps st).changeIndex = st.changeIndex :=
  registerProps_go_changeIndex st.props.size 0 st

theorem registerProps_levelStart (st : EngineState p T) :
    (registerProps st).levelStart = st.levelStart :=
  registerProps_go_levelStart st.props.size 0 st

theorem registerProps_level (st : EngineState p T) :
    (registerProps st).level = st.level :=
  registerProps_go_level st.props.size 0 st

theorem registerProps_reasonCap (st : EngineState p T) :
    (registerProps st).reasonCap = st.reasonCap :=
  registerProps_go_reasonCap st.props.size 0 st

theorem registerProps_table (st : EngineState p T) :
    (registerProps st).table = st.table :=
  registerProps_go_table st.props.size 0 st

theorem registerProps_db (st : EngineState p T) :
    (registerProps st).db = st.db :=
  registerProps_go_db st.props.size 0 st

/-- The state construction leaves the literal table at the parameter `T`. -/
theorem initStateCore_table (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    (initStateCore p T doms props).table = T := by
  unfold initStateCore
  rw [list_foldl_table (l := List.range props.size)
    (f := fun st i => enqueueProp st i) (hf := fun st i => enqueueProp_table st i)]
  rw [registerProps_table]
  exact initStateBase_table p T doms props


theorem registerProps_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init (registerProps st) := by
  refine RootInv.of_eq (st' := registerProps st) h
    (registerProps_doms st) (registerProps_trail st) ?_
    (registerProps_changeIndex st) (registerProps_levelStart st)
    (registerProps_level st) (registerProps_reasonCap st) ?_ ?_ ?_
  · intro s
    simp only [EngineState.changeList, registerProps_changeIndex]
  · rw [registerProps_table]
    exact h.table_inv
  · rw [registerProps_table, registerProps_db]
    exact h.lits_wf
  · rw [registerProps_db]
    exact h.db_inv

theorem enqueueProp_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) (id : Nat) :
    RootInv p T init (enqueueProp st id) := by
  refine RootInv.of_eq (st' := enqueueProp st id) h
    (enqueueProp_doms st id) (enqueueProp_trail st id) ?_
    (enqueueProp_changeIndex st id) (enqueueProp_levelStart st id)
    (enqueueProp_level st id) (enqueueProp_reasonCap st id) ?_ ?_ ?_
  · intro s
    simp only [EngineState.changeList, enqueueProp_changeIndex]
  · rw [enqueueProp_table]
    exact h.table_inv
  · rw [enqueueProp_table, enqueueProp_db]
    exact h.lits_wf
  · rw [enqueueProp_db]
    exact h.db_inv

theorem range_enqueueProp_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) (n : Nat) :
    RootInv p T init ((List.range n).foldl (fun st i => enqueueProp st i) st) :=
  list_foldl_rootInv (List.range n) (fun st i => enqueueProp st i)
    (fun st i hh => enqueueProp_rootInv hh i) st h

theorem initStateBase_rootInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) (hT : T.Inv)
    (hinv : InitInv p doms) (hconv : InitConv p doms) :
    RootInv p T doms (initStateBase p T doms props) := by
  refine ⟨initStateBase_histInv p T doms props, hinv, hT, ?_, ?_, ?_, hconv, ?_⟩
  · intro id sc hget l hl
    simp [initStateBase] at hget
  · intro i j e1 e2 hi hj hij
    simp [initStateBase] at hi
  · intro i e hi hlev
    simp [initStateBase] at hi
  · simpa only [ClauseDB.empty, initStateBase] using (ClauseDB.inv_empty (p := p) (T := T))

theorem initStateCore_props (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) :
    (initStateCore p T doms props).props = props := by
  unfold initStateCore
  rw [list_foldl_props _ _ (fun st i => enqueueProp_props st i)]
  exact registerProps_props _

theorem initStateCore_rootInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (props : Array (PropV2 p T)) (hT : T.Inv)
    (hinv : InitInv p doms) (hconv : InitConv p doms) :
    RootInv p T doms (initStateCore p T doms props) := by
  unfold initStateCore
  exact range_enqueueProp_rootInv
    (registerProps_rootInv (initStateBase_rootInv p T doms props hT hinv hconv))
    props.size

theorem initState_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : initState p T = some st) (hT : T.Inv) :
    RootInv p T st.doms st := by
  unfold initState at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_doms]
            exact initStateCore_rootInv p T doms _ hT
              (initInv_of_convertDomains hc) ⟨(convertDomains_spec hc).2⟩
          · simp [hr] at h
  | false => simp [hg] at h

/-- The entry state's literal table is the table parameter. -/
theorem initState_table {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : initState p T = some st) : st.table = T := by
  unfold initState at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact initStateCore_table p T _ _
      · simp at h

theorem initState_propsSound {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : initState p T = some st) :
    PropsSound p T st.props := by
  unfold initState at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_props]
            exact propsOf_pruneSound p T doms _
          · simp [hr] at h
  | false => simp [hg] at h

/-! ## Decisions -/

/-- Annotation priority vector as an array; unannotated slots score 0. -/
def annotPrioArray (p : CompiledProblem DomConstraint) : Array Nat :=
  (annotPrio p.source p.names).toArray

/-! ## Conflict activity (N12)

`activity` is a pure policy score: it is read by `selectSlot` under
`--var=act|domwdeg` and never feeds a verdict.  Instead of decaying every
stored score on each conflict, the bump increment grows geometrically
(`inc := inc / activityDecay`), so only the learned clause's slots are
touched.  Scores and the increment are rescaled by `activityScaleDown`
when the increment passes `activityScaleUp`; a global rescale preserves
the selection order.  Up to floating-point rounding the order is the same
as the former per-conflict decay: at conflict `k` every score is the old
score divided by `activityDecay^(k-1)`.  A linear scan over `activity` is
used for selection; `activityHeap` is left untouched (see the N12 report). -/

/-- Per-conflict multiplicative activity decay (0.95).  Kept as the
increment ratio; the literal is written by bits because
`Float.ofScientific` with a large exponent goes through the GMP-backed
model and must never be evaluated in the hot loop. -/
def activityDecay : Float := Float.ofBits 0x3FEE666666666666

/-- Rescale threshold for the growing increment: `1e100`. -/
def activityScaleUp : Float := Float.ofBits 0x54B249AD2594C37D

/-- Rescale factor: `1e-100`. -/
def activityScaleDown : Float := Float.ofBits 0x2B2BFF2EE48E0530

/-- Activity of a slot, or `0` outside the array. -/
def activityGet (st : EngineState p T) (s : Nat) : Float :=
  (st.activity.get? s).getD 0.0

/-- The bump contributed by one occurrence of slot `s`: `1` under `act` and
`1 / |dom(s)|` under `domwdeg`. -/
def activityBump (st : EngineState p T) (o : SearchConfig) (s : Nat) : Float :=
  match o.var with
  | .domwdeg =>
      let n := (st.doms.getD s DomC.empty).size
      if n == 0 then 1.0 else 1.0 / n.toFloat
  | _ => 1.0

/-- Bump the slots of the learned clause by the current increment, grow the
    increment, and rescale all scores when it exceeds `activityScaleUp`.
    Deterministic: `Array.foldl` visits the literals in learned-clause order. -/
def bumpActivity (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : EngineState p T :=
  let bumped := lits.foldl (fun (a : FloatArray) (l : PLit) =>
    let s := atomSlot l.lit.atom
    let old := (a.get? s).getD 0.0
    a.set! s (old + st.activityInc * activityBump st o s)) st.activity
  let st := { st with
    activity := bumped
    activityInc := st.activityInc / activityDecay }
  if st.activityInc > activityScaleUp then
    { st with
      activity := ⟨st.activity.data.map fun a => a * activityScaleDown⟩
      activityInc := st.activityInc * activityScaleDown }
  else st

/-- Conflict-driven bumping is active only for the two activity
strategies; every other `--var` route leaves `activity` untouched.  `wdeg`
uses its own `slotWeight` scores, bumped in `drain` at each conflict. -/
def bumpActivityIf (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : EngineState p T :=
  match o.var with
  | .act | .domwdeg => bumpActivity st o lits
  | _ => st

/-- Weighted degree of a slot, or `0` outside the score array. -/
def weightGet (st : EngineState p T) (s : Nat) : Nat :=
  (st.slotWeight[s]?).getD 0

/-- Bump the weighted-degree score of every slot mentioned by a conflict
explanation clause.  This is policy data for `--var=wdeg`: it is never read
by a verdict or a soundness argument.  Slots outside the initialised score
array are ignored rather than resized, so this is total and panic-free. -/
def bumpWeightLits (st : EngineState p T) (lits : Array PLit) :
    EngineState p T :=
  let w := lits.foldl (fun (a : Array Nat) (l : PLit) =>
    let s := l.slot
    if s < a.size then a.set! s (a.getD s 0 + 1) else a) st.slotWeight
  { st with slotWeight := w }

theorem bumpWeightLits_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (lits : Array PLit) :
    HistInv init (bumpWeightLits st lits) :=
  HistInv.congr h rfl rfl (fun _ => rfl) rfl rfl rfl rfl

/-- Select the next unfixed slot.  `minc` is the default; `annot` uses the
priority vector and falls back to `minc` inside a band; `act` and `domwdeg`
take the highest activity and break ties by `minc` (smallest domain, then
lowest index); `wdeg` minimises `size / (weight + 1)`, tie-breaking by
smallest domain and then lowest index.  The scan only ever considers
unfixed, nonempty slots. -/
def selectSlot (p : CompiledProblem DomConstraint) (st : EngineState p T)
    (o : SearchConfig) (prio : Array Nat) : Option Nat :=
  let rec go (i : Nat) (best : Option Nat) (bestSize : Nat) (bestAct : Float)
      (bestPrio : Nat) (bestWeight : Nat) : Option Nat :=
    if h : i < st.doms.size then
      let d := st.doms[i]
      let sz := d.size
      if sz != 1 && !d.isEmpty then
        let better : Bool :=
          match best with
          | none => true
          | some _ =>
              if o.var == .act || o.var == .domwdeg then
                let ai := activityGet st i
                if ai != bestAct then decide (ai > bestAct)
                else decide (sz < bestSize)
              else if o.var == .wdeg then
                let wi := weightGet st i
                let lhs := sz * (bestWeight + 1)
                let rhs := bestSize * (wi + 1)
                if lhs != rhs then decide (lhs < rhs)
                else decide (sz < bestSize)
              else if o.var == .annot then
                let pi := prio.getD i 0
                if pi != bestPrio then decide (pi > bestPrio)
                else decide (sz < bestSize)
              else decide (sz < bestSize)
        if better then
          go (i + 1) (some i) sz (activityGet st i) (prio.getD i 0)
            (if o.var == .wdeg then weightGet st i else bestWeight)
        else go (i + 1) best bestSize bestAct bestPrio bestWeight
      else go (i + 1) best bestSize bestAct bestPrio bestWeight
    else best
  termination_by st.doms.size - i
  go 0 none 0 0.0 0 0

/-- Descending search for a member at or below `v`, at most `k` steps. -/
def findMemberDown (d : DomC) (v : Int) : Nat → Option Int
  | 0 => none
  | k + 1 => if d.memIntView v then some v else findMemberDown d (v - 1) k

/-- Ascending search for a member at or above `v`, at most `k` steps. -/
def findMemberUp (d : DomC) (v : Int) : Nat → Option Int
  | 0 => none
  | k + 1 => if d.memIntView v then some v else findMemberUp d (v + 1) k

/-- The value pinned by a value-presentation literal: `s ≤ lo` fixes the
    domain minimum, `¬(s ≤ hi-1)` fixes its maximum, `¬(s ≠ v)` fixes `v`,
    and `s = b` fixes the Boolean. -/
def decidedValue? (l : Literal) : Option Value :=
  match l.atom, l.positive with
  | .boolEq _ b, true => some (.bool b)
  | .intLe _ k, true => some (.int k)
  | .intLe _ k, false => some (.int (k + 1))
  | .intNe _ v, false => some (.int v)
  | _, _ => none

/-- The saved-phase literal of a value that is still in the domain, or
    `none` when the saved value has been removed (or has the wrong type).
    The returned literal pins the slot to that value and uses the same
    presentation form as `selectValue` would: the domain minimum is a
    `posLe`, the maximum a `negLe`, and an interior value a `negNe`.
    Hence re-deciding the phase that an ascending strategy would choose is
    observationally inert. -/
def phaseLiteral (s : Nat) (d : DomC) (v : Value) : Option Literal :=
  match d, v with
  | .bool _, .bool b =>
      if d.mem (.bool b) then some (posBool s b) else none
  | .bool _, _ => none
  | _, .int i =>
      if d.memIntView i then
        match d.lo?, d.hi? with
        | some lo, some hi =>
            if i == lo then some (posLe s lo)
            else if i == hi then some (negLe s (hi - 1))
            else some (negNe s i)
        | _, _ => some (negNe s i)
      else none
  | _, _ => none

/-- Value presentation.  `min`/`act`/`annot`/`incumbent` take the low end,
`max` the high end, `median` fixes a central member.  Boolean domains use
their two-valued order.  Under `act` the saved phase is tried first when it
is still a domain member, but only under the dynamic variable strategies
(`act`/`domwdeg`/`wdeg`); the static `minc`/`annot` paths keep their pre-N12
behaviour (phase saving measurably regresses `minc/act`, see the N12
record).  Under `incumbent` the saved phase is the previous round's
incumbent, it is tried first for every variable strategy, and the decision
loop does not overwrite it, so it stays a fixed per-round guide rather than
accumulating phase saving.  Every other value strategy is unchanged. -/
def selectValue (s : Nat) (d : DomC) (o : SearchConfig) (ord : AnnValOrder)
    (saved : Option Value) : Option Literal :=
  let phase : Option Literal :=
    if o.val == .incumbent ||
        (o.val == .act &&
          (o.var == .act || o.var == .domwdeg || o.var == .wdeg)) then
      match saved with
      | some v => phaseLiteral s d v
      | none => none
    else none
  match phase with
  | some l => some l
  | none =>
    match d with
    | .bool bits =>
        let canFalse := (bits &&& 1) != 0
        let canTrue := (bits &&& 2) != 0
        if o.val == .max then
          if canTrue then some (posBool s true)
          else if canFalse then some (posBool s false) else none
        else
          if canFalse then some (posBool s false)
          else if canTrue then some (posBool s true) else none
    | _ =>
        match d.lo?, d.hi? with
        | some lo, some hi =>
            if lo == hi then none
            else if o.val == .split then
              let m := lo + (hi - lo) / 2
              if ord == .max || ord == .reverseSplit then some (negLe s m)
              else some (posLe s m)
            else
              let useMax := o.val == .max || ord == .max || ord == .reverseSplit
              let useMedian := o.val == .median || ord == .median
              if useMax then some (negLe s (hi - 1))
              else if useMedian then
                let m := lo + (hi - lo) / 2
                match findMemberDown d m 64 with
                | some v => some (negNe s v)
                | none =>
                    match findMemberUp d (m + 1) 64 with
                    | some v => some (negNe s v)
                    | none => some (posLe s lo)
              else some (posLe s lo)
        | _, _ => none

/-- Choose a decision literal together with the value it pins, or `none`
    when all slots are fixed.  The value is stored as the slot's saved phase
    by the caller. -/
def selectDecision (p : CompiledProblem DomConstraint) (st : EngineState p T)
    (o : SearchConfig) (prio : Array Nat) (orders : List AnnValOrder) :
    Option (PLit × Option Value) :=
  match selectSlot p st o prio with
  | none => none
  | some s =>
      let d := st.doms.getD s DomC.empty
      match selectValue s d o (orders.getD s .none) st.phases[s]? with
      | none => none
      | some l =>
          -- Interval splits decide a set, not a single value; only a
          -- value-pinning literal contributes a saved phase.
          if o.val == .split then some (pLit l, none)
          else (decidedValue? l).map fun v => (pLit l, some v)

/-! ## Split-decision coverage and reduction (P2.2) -/

/-- A nonempty integer-kind domain contains the value returned by `lo?`. -/
theorem DomC.mem_of_lo?_intKind {d : DomC} (hWF : d.WF)
    (hk : d.intKindB = true) {lo : Int} (h : d.lo? = some lo) :
    d.mem (.int lo) = true := by
  cases d with
  | bool bits => simp [DomC.intKindB] at hk
  | bounds blo bhi =>
      rw [DomC.lo?.eq_2] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        obtain rfl := Option.some.inj h
        have hle : ¬ bhi < blo := by simpa using hlt
        have hge : blo ≤ bhi := by omega
        simp [DomC.mem, hge]
  | bitset blo words =>
      exact bitset_mem_int_of_lo?_eq h
  | boundsHoles blo bhi holes =>
      rw [DomC.lo?.eq_4] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        have hpair := hWF.1
        have hrange : ∀ x ∈ holes.toList, blo ≤ x := fun x hx => (hWF.2 x hx).1
        have hRangeHi : ∀ x ∈ holes.toList, x ≤ bhi := fun x hx => (hWF.2 x hx).2
        obtain ⟨hlo, hhi, hnotmem⟩ := goHoleLo_some_not_mem hpair hrange hRangeHi h
        have hm : memHoleRange holes lo = false :=
          (memHoleRange_eq_false_iff hpair).mpr hnotmem
        simp [DomC.mem, hlo, hhi, hm]
  | sparse values =>
      rw [DomC.lo?.eq_5] at h
      have hmem : lo ∈ values.toList := by
        obtain ⟨hpos, hx0⟩ := arrayHead?_eq_some h
        rw [← hx0]
        exact Array.mem_toList_iff.mpr
          (Array.mem_of_getElem? (Array.getElem?_eq_getElem hpos))
      simp only [DomC.mem]
      exact (memHoleRange_eq_true_iff hWF).mpr hmem

/-- A nonempty integer-kind domain contains the value returned by `hi?`. -/
theorem DomC.mem_of_hi?_intKind {d : DomC} (hWF : d.WF)
    (hk : d.intKindB = true) {hi : Int} (h : d.hi? = some hi) :
    d.mem (.int hi) = true := by
  cases d with
  | bool bits => simp [DomC.intKindB] at hk
  | bounds blo bhi =>
      rw [DomC.hi?.eq_2] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        obtain rfl := Option.some.inj h
        have hle : ¬ bhi < blo := by simpa using hlt
        have hge : blo ≤ bhi := by omega
        simp [DomC.mem, hge]
  | bitset blo words =>
      exact bitset_mem_int_of_hi?_eq h
  | boundsHoles blo bhi holes =>
      rw [DomC.hi?.eq_4] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        have hpair := hWF.1
        have hrangeLo : ∀ x ∈ holes.toList, blo ≤ x := fun x hx => (hWF.2 x hx).1
        have hrangeHi : ∀ x ∈ holes.toList, x ≤ bhi := fun x hx => (hWF.2 x hx).2
        obtain ⟨hlo, hhi, hnotmem⟩ :=
          goHoleHi_some_spec3 hrangeLo hrangeHi hpair h
        have hm : memHoleRange holes hi = false :=
          (memHoleRange_eq_false_iff hpair).mpr hnotmem
        simp [DomC.mem, hlo, hhi, hm]
  | sparse values =>
      rw [DomC.hi?.eq_5] at h
      have hmem : hi ∈ values.toList := by
        obtain ⟨hpos, hx0⟩ := arrayLast?_eq_some h
        rw [← hx0]
        exact Array.mem_toList_iff.mpr
          (Array.mem_of_getElem? (Array.getElem?_eq_getElem hpos))
      simp only [DomC.mem]
      exact (memHoleRange_eq_true_iff hWF).mpr hmem

/-- The two sides of a split literal cover every integer member of a domain:
`x ≤ m` and `x > m` exhaust all integer views. -/
theorem split_mem_cover {d : DomC} (hWF : d.WF) (s : Nat) (m : Int) (v : Value)
    (hm : d.mem v = true) :
    (d.applyLit (posLe s m)).mem v = true ∨
      (d.applyLit (negLe s m)).mem v = true := by
  obtain ⟨i, hi⟩ := DomC.mem_intView_exists hm
  rw [DomC.mem_applyLit d (posLe s m) hWF v,
    DomC.mem_applyLit d (negLe s m) hWF v]
  by_cases hle : i ≤ m
  · left
    refine ⟨hm, ?_⟩
    change Literal.valueHolds ⟨.intLe s m, true⟩ v = true
    rw [valueHolds_intLe_pos_iff]
    exact ⟨i, hi, hle⟩
  · right
    refine ⟨hm, ?_⟩
    change Literal.valueHolds ⟨.intLe s m, false⟩ v = true
    rw [valueHolds_intLe_neg_iff]
    exact ⟨i, hi, by omega⟩

/-- The `x ≤ m` side drops the upper endpoint of a nonfixed domain. -/
theorem split_left_reduces {d : DomC} (hWF : d.WF) (hk : d.intKindB = true)
    (s : Nat) {lo hi m : Int} (hlo : d.lo? = some lo) (hhi : d.hi? = some hi)
    (hm : m < hi) :
    ∃ v, d.mem v = true ∧ (d.applyLit (posLe s m)).mem v = false := by
  refine ⟨.int hi, DomC.mem_of_hi?_intKind hWF hk hhi, ?_⟩
  have hnot : ¬ (d.applyLit (posLe s m)).mem (.int hi) = true := by
    rw [DomC.mem_applyLit d (posLe s m) hWF (.int hi)]
    rintro ⟨-, hv⟩
    change Literal.valueHolds ⟨.intLe s m, true⟩ (.int hi) = true at hv
    rw [valueHolds_intLe_pos_iff] at hv
    obtain ⟨j, hj, hjm⟩ := hv
    simp [Value.intView] at hj
    omega
  simpa using hnot

/-- The `x > m` side drops the lower endpoint of a nonfixed domain. -/
theorem split_right_reduces {d : DomC} (hWF : d.WF) (hk : d.intKindB = true)
    (s : Nat) {lo hi m : Int} (hlo : d.lo? = some lo) (hhi : d.hi? = some hi)
    (hm : lo ≤ m) :
    ∃ v, d.mem v = true ∧ (d.applyLit (negLe s m)).mem v = false := by
  refine ⟨.int lo, DomC.mem_of_lo?_intKind hWF hk hlo, ?_⟩
  have hnot : ¬ (d.applyLit (negLe s m)).mem (.int lo) = true := by
    rw [DomC.mem_applyLit d (negLe s m) hWF (.int lo)]
    rintro ⟨-, hv⟩
    change Literal.valueHolds ⟨.intLe s m, false⟩ (.int lo) = true at hv
    rw [valueHolds_intLe_neg_iff] at hv
    obtain ⟨j, hj, hjm⟩ := hv
    simp [Value.intView] at hj
    omega
  simpa using hnot

/-- The mid split point of a nonempty interval stays strictly below the upper
endpoint and at or above the lower endpoint. -/
theorem split_mid_spec {lo hi : Int} (hlt : lo < hi) :
    lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < hi := by
  have hnonneg : 0 ≤ (hi - lo) / 2 :=
    Int.ediv_nonneg (by omega) (by decide)
  have hmul : ((hi - lo) / 2) * 2 ≤ hi - lo :=
    Int.ediv_mul_le (hi - lo) (by decide)
  have hqlt : (hi - lo) / 2 < hi - lo := by
    by_cases h : (hi - lo) / 2 < hi - lo
    · exact h
    · exfalso
      have hge : hi - lo ≤ (hi - lo) / 2 := by omega
      omega
  omega

/-- The fixed assignment in slot order, or `none` if a slot is not fixed. -/
def fixedAssignment (st : EngineState p T) : Option (List Value) :=
  let rec go (i : Nat) (acc : List Value) : Option (List Value) :=
    if h : i < st.doms.size then
      match st.doms[i].fixedValue with
      | some v => go (i + 1) (v :: acc)
      | none => none
    else some acc.reverse
  termination_by st.doms.size - i
  go 0 []

/-! ## Restart schedules (N12)

Restarts are a policy step: they backjump to level 0, keep the learned
clause database, activity and saved phases, and continue the same `search`
recursion.  They never produce a verdict: every leaf is the same
`search_sat`/`search_unsat` leaf as before. -/

/-- Bounded power-of-two block search for the Luby sequence. -/
def lubyPow (fuel i p : Nat) : Nat :=
  match fuel with
  | 0 => p
  | f + 1 => if i < 2 * p then p else lubyPow f i (2 * p)

/-- Fuel-bounded Luby value at the 1-indexed position `i`:
`1, 1, 2, 1, 1, 2, 4, ...`.  `64` block steps cover every position below
`2^64`, far beyond any restart count reachable under `coreFuel`. -/
def lubyAux : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, i =>
      let p := lubyPow f i 1
      let j := i - p
      if j + 1 = p then p else lubyAux f (j + 1)

/-- The Luby restart unit sequence value at `i` (1-indexed). -/
def luby (i : Nat) : Nat := lubyAux 64 i

/-- The conflict threshold of the next restart. -/
def restartThreshold (o : SearchConfig) (restarts : Nat) : Nat :=
  match o.restart with
  | .luby => o.restartBase * luby (restarts + 1)
  | .geom => o.restartBase * 2 ^ restarts
  | .none => 0

/-- Is a restart due after the conflict just recorded?  `none` never
restarts; `luby` uses `restartBase * luby (restarts + 1)`; `geom` uses
`restartBase * 2^restarts`.  The comparison uses conflicts since the last
restart, not the cumulative counter. -/
def restartDue (o : SearchConfig) (st : EngineState p T) : Bool :=
  o.restart != .none && o.restartBase > 0 &&
    st.stats.conflicts - st.lastRestartConflict >= restartThreshold o st.restarts

/-- Has the configured per-round conflict budget been reached?  `none` never
caps the loop.  The check sits at the top of the search loop, so a capped run
stops before its next drain with the conflict counter exactly at the budget
(or above it when the root carries a seed conflict). -/
def conflictLimitHit (o : SearchConfig) (st : EngineState p T) : Bool :=
  match o.conflictLimit with
  | none => false
  | some n => n ≤ st.stats.conflicts

/-- Terminal give-up with a diagnostic cause.  The cause is statistics
metadata only and never participates in a verdict. -/
def giveUpWith (st : EngineState p T) (cause : String) :
    CoreResult × EngineState p T :=
  (.gaveUp, { st with stats := { st.stats with gaveUp := 1, gaveUpCause := cause } })

@[simp] theorem giveUpWith_fst (st : EngineState p T) (cause : String) :
    (giveUpWith st cause).1 = .gaveUp := rfl

/-! ### Invariant preservation for the policy-only steps

The analysis needs `SlotHistory` for the current state.  Every step between
two analysis calls only touches domains when it records a trail entry, so the
history and trail invariants are preserved by the pure bookkeeping steps. -/

theorem bumpActivity_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (o : SearchConfig) (lits : Array PLit) :
    HistInv init (bumpActivity st o lits) := by
  refine ⟨SlotHistory.congr h.1 ?_ ?_ ?_, TrailInv.congr h.2 ?_ ?_ ?_ ?_ ?_⟩
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · intro s; dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;>
      simp [hsc, EngineState.changeList]
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · dsimp only [bumpActivity]
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]
  · dsimp only [bumpActivity]
    split <;> rfl

theorem bumpActivityIf_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (o : SearchConfig) (lits : Array PLit) :
    HistInv init (bumpActivityIf st o lits) := by
  cases hv : o.var with
  | act => simpa [bumpActivityIf, hv] using bumpActivity_histInv h o lits
  | domwdeg => simpa [bumpActivityIf, hv] using bumpActivity_histInv h o lits
  | wdeg => simpa [bumpActivityIf, hv] using h
  | minc => simpa [bumpActivityIf, hv] using h
  | annot => simpa [bumpActivityIf, hv] using h
  | obj => simpa [bumpActivityIf, hv] using h

theorem maybeReduce_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) : HistInv init (maybeReduce st) := by
  unfold maybeReduce
  split
  · exact ⟨SlotHistory.congr h.1 rfl rfl (fun s => rfl),
      TrailInv.congr h.2 rfl rfl rfl rfl rfl⟩
  · exact h

theorem newLevel_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) : HistInv init (newLevel st) :=
  ⟨SlotHistory.congr h.1 rfl rfl (fun s => rfl), newLevel_trailInv h.2⟩

/-- Reclaiming the transient-reason suffix changes only the `reasons` and
`stats` fields, so the search-shape invariant transports without unfolding the
bound computation. -/
theorem trimReasonsStats_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) : HistInv init st.trimReasonsStats := by
  obtain ⟨hslot, htrail⟩ := h
  exact ⟨SlotHistory.congr hslot rfl rfl (fun s => rfl),
    TrailInv.congr htrail rfl rfl rfl rfl rfl⟩

/-! ## R1: root-invariant transport for the CDCL loop

The root invariant records that every level-zero trail entry is a unit
consequence, together with the table/database structural invariants that
turn watched-clause propagations into entailed units.  Every transition of
the loop below either leaves the logical state alone (policy counters) or
has a dedicated transport lemma.  All proofs here are erased at runtime. -/

/-- The activity bump changes only policy counters. -/
theorem bumpActivity_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (o : SearchConfig) (lits : Array PLit) :
    RootInv p T init (bumpActivity st o lits) := by
  refine h.congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp only [bumpActivity] <;>
    by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;>
      simp [hsc, EngineState.changeList]

theorem bumpActivityIf_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (o : SearchConfig) (lits : Array PLit) :
    RootInv p T init (bumpActivityIf st o lits) := by
  cases hv : o.var with
  | act => simpa [bumpActivityIf, hv] using bumpActivity_rootInv h o lits
  | domwdeg => simpa [bumpActivityIf, hv] using bumpActivity_rootInv h o lits
  | wdeg => simpa [bumpActivityIf, hv] using h
  | minc => simpa [bumpActivityIf, hv] using h
  | annot => simpa [bumpActivityIf, hv] using h
  | obj => simpa [bumpActivityIf, hv] using h

theorem bumpActivity_props (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : (bumpActivity st o lits).props = st.props := by
  dsimp only [bumpActivity]
  by_cases hsc : activityScaleUp < st.activityInc / activityDecay <;> simp [hsc]

theorem bumpActivityIf_props (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : (bumpActivityIf st o lits).props = st.props := by
  cases hv : o.var with
  | act => simpa [bumpActivityIf, hv] using bumpActivity_props st o lits
  | domwdeg => simpa [bumpActivityIf, hv] using bumpActivity_props st o lits
  | wdeg => simp [bumpActivityIf, hv]
  | minc => simp [bumpActivityIf, hv]
  | annot => simp [bumpActivityIf, hv]
  | obj => simp [bumpActivityIf, hv]

theorem maybeReduce_props (st : EngineState p T) :
    (maybeReduce st).props = st.props := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_changeIndex (st : EngineState p T) :
    (maybeReduce st).changeIndex = st.changeIndex := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_levelStart (st : EngineState p T) :
    (maybeReduce st).levelStart = st.levelStart := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_reasonCap (st : EngineState p T) :
    (maybeReduce st).reasonCap = st.reasonCap := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem newLevel_props (st : EngineState p T) :
    (newLevel st).props = st.props := by
  unfold newLevel
  rfl

/-- Clause-database reduction preserves every component of the root
invariant. -/
theorem maybeReduce_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init (maybeReduce st) := by
  refine RootInv.of_eq (st' := maybeReduce st) h (maybeReduce_doms st)
    (maybeReduce_trail st) ?_ (maybeReduce_changeIndex st)
    (maybeReduce_levelStart st) (maybeReduce_level st) (maybeReduce_reasonCap st) ?_ ?_ ?_
  · intro s
    simp only [EngineState.changeList, maybeReduce_changeIndex]
  · rw [maybeReduce_table]
    exact h.table_inv
  · rw [maybeReduce_table]
    exact maybeReduce_litsWF h.lits_wf
  · exact maybeReduce_inv st h.db_inv

/-- Updating only the statistics record preserves the root invariant. -/
theorem RootInv.setStats {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (stats : EngineStats) :
    RootInv p T init { st with stats := stats } :=
  h.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl

/-- Adding a learned clause and setting its LBD preserves the root invariant.
The clause literals must be interned in the live table. -/
theorem RootInv.addLearned {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    {lc : EClause p T} (hwf : ∀ l ∈ lc.lits.toList, st.table.WF l)
    (lbd : Nat) :
    RootInv p T init
      { st with db := (st.db.add lc).1.setLbd (st.db.add lc).2 lbd } := by
  refine RootInv.of_eq (st' :=
    { st with db := (st.db.add lc).1.setLbd (st.db.add lc).2 lbd })
    h rfl rfl (fun _ => rfl) rfl rfl rfl rfl ?_ ?_ ?_
  · exact h.table_inv
  · exact ClauseDB.LitsWF.setLbd (ClauseDB.LitsWF.add h.lits_wf lc hwf) _ _
  · exact ClauseDB.setLbd_inv _ _ _ (ClauseDB.add_inv _ _ h.db_inv)



/-- `giveUpWith` only updates the statistics record. -/
theorem giveUpWith_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (cause : String) : RootInv p T init (giveUpWith st cause).2 :=
  h.setStats _

/-- `giveUpWith` does not change the propagation table. -/
theorem giveUpWith_props {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} (h : PropsSound p T st.props) (cause : String) :
    PropsSound p T (giveUpWith st cause).2.props := h

/-- A search result together with the root invariant and propagation
soundness of its terminal state.  The two proof fields are erased at runtime;
they let the incremental seed carry its database into the next round. -/
structure SearchInv (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) where
  res : CoreResult × EngineState p T
  hroot : RootInv p T init res.2
  hprops : PropsSound p T res.2.props

set_option maxHeartbeats 1600000 in
/-- Search with an explicit fuel.  Each recursive call is structurally on a
smaller `Nat`, so the loop is total without `partial`.  The analysis is
computed before the conflict counter is bumped (the analysis reads only
the domains/table/level, never the stats), which keeps the soundness
proof's hypotheses syntactically simple. -/
def search (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) (st : EngineState p T)
    (pending : Array Pending) (hroot : RootInv p T init st)
    (hpending : PendingRoot p st pending)
    (hprops : PropsSound p T st.props) :
    Nat → SearchInv p T init
  | 0 => ⟨giveUpWith st "search fuel exhausted", giveUpWith_rootInv hroot _,
          giveUpWith_props hprops "search fuel exhausted"⟩
  | f + 1 =>
      if conflictLimitHit o st then
        ⟨giveUpWith st "conflict limit reached", giveUpWith_rootInv hroot _,
          giveUpWith_props hprops "conflict limit reached"⟩
      else
        let res := drain p T st pending (f + 1)
        let st1 := res.st
        have hroot1 : RootInv p T init st1 :=
          drain_rootInv st pending (f + 1) hroot hpending hprops
        have hprops1 : PropsSound p T st1.props :=
          hprops.congr (drain_props (p := p) (T := T) pending (f + 1) (Frame.refl st))
        let st := st1
        if res.failed then
          ⟨giveUpWith st "pending pruning application failed", giveUpWith_rootInv hroot1 _,
            giveUpWith_props hprops1 "pending pruning application failed"⟩
        else
          match res.conflict with
          | some c =>
              let a := analyze p T init st hroot1.conv hroot1.hist.1 hroot1 c res.fuel
              have hspec : AnalysisSpec p T st a :=
                analyze_spec hroot1.conv hroot1.hist.1 hroot1 c res.fuel
              -- The conflict clause is the failing propagation's explanation;
              -- charge its slots in the weighted-degree policy.  This happens
              -- after analysis (which does not read the policy) so the proof
              -- sees the same state that `analyze` was applied to.
              let st := bumpWeightLits st c.lits
              have hroot2 : RootInv p T init st :=
                hroot1.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl
              let st := { st with stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
              have hroot3 : RootInv p T init st :=
                hroot2.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl
              if !a.ok then
                ⟨giveUpWith st a.why, giveUpWith_rootInv hroot3 _,
                giveUpWith_props hprops1 a.why⟩
              else
                match hlearn : a.learned with
                | none =>
                    ⟨giveUpWith st "analysis returned no learned clause",
                    giveUpWith_rootInv hroot3 _,
                    giveUpWith_props hprops1 "analysis returned no learned clause"⟩
                | some lc0 =>
                    if lc0.lits.isEmpty then
                      -- The learned empty clause is entailed unconditionally
                      -- (`analyze_empty_unsat`), so this is a root refutation
                      -- even when the conflict was found above level 0.
                      ⟨(.unsat, st), hroot3, hprops1⟩
                    else
                      have hprops2 : PropsSound p T (bumpActivityIf st o a.bumpLits).props :=
                        hprops1.congr (bumpActivityIf_props st o a.bumpLits)
                      let st := bumpActivityIf st o a.bumpLits
                      have hroot4 : RootInv p T init st :=
                        bumpActivityIf_rootInv hroot3 o a.bumpLits
                      let r := canonClause st lc0
                      have hroot5 : RootInv p T init r.2 :=
                        canonClause_rootInv hroot4 lc0
                      have hprops3 : PropsSound p T r.2.props :=
                        hprops2.congr (canonClause_props st lc0)
                      have hwf : ∀ q ∈ r.1.lits.toList, r.2.table.WF q := by
                        intro q hq
                        obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp (by simpa using hq)
                        exact canonClause_wf st lc0 hroot4.table_wf i q hi
                      let lc := r.1
                      let st := r.2
                      let rdb := st.db.add lc
                      let id := rdb.2
                      let db := rdb.1.setLbd id a.lbd
                      let st := { st with db := db }
                      have hroot6 : RootInv p T init st :=
                        hroot5.addLearned hwf a.lbd
                      let st := { st with
                        stats := { st.stats with
                          learned := st.stats.learned + 1
                          learnedLitsBefore := st.stats.learnedLitsBefore + a.litsBefore
                          learnedLitsAfter := st.stats.learnedLitsAfter + lc.lits.size
                          learnedUnits := st.stats.learnedUnits +
                            (if lc.lits.size ≤ 1 then 1 else 0) } }
                      have hroot7 : RootInv p T init st :=
                        hroot6.setStats _
                      if hge : a.backjump >= st.level then
                        -- A non-asserting clause cannot guide this level.  A
                        -- root restart here was measured to turn the early
                        -- give-up into a timeout, so keep the explicit cause.
                        ⟨giveUpWith st "non-progressing backjump", giveUpWith_rootInv hroot7 _,
                          giveUpWith_props hprops3 "non-progressing backjump"⟩
                      else
                        let hlt : a.backjump < st.level := Nat.lt_of_not_le hge
                        have hprops4 : PropsSound p T (backjump st a.backjump).props :=
                          hprops3.congr (backjump_props st a.backjump)
                        let st0 := backjump st a.backjump
                        have hroot8 : RootInv p T init st0 :=
                          hroot7.backjump hlt
                        let st := st0.trimReasonsStats
                        have hroot9 : RootInv p T init st :=
                          hroot8.trimReasonsStats
                        match hassert : a.asserting with
                        | some l =>
                            have hpending' : PendingRoot p st
                                #[{ lit := l, reason := .learned id, count := true }] := by
                              intro h0 item hit
                              simp only [List.mem_singleton] at hit
                              subst item
                              have hbj : a.backjump = 0 := by
                                have hlev : st.level = a.backjump := by
                                  rw [trimReasonsStats_level,
                                    backjump_level_eq_of_lt hlt]
                                omega
                              exact hspec.unit_at_root lc0 l hlearn hassert hbj
                            search p T init o prio orders st
                              #[{ lit := l, reason := .learned id, count := true }]
                              hroot9 hpending' hprops4 f
                        | none =>
                            -- No current-level literal: the learned clause is
                            -- falsified at the backjump level; Core makes no
                            -- claim here (give up).
                            ⟨giveUpWith st "missing asserting literal", giveUpWith_rootInv hroot9 _,
                              giveUpWith_props hprops4 "missing asserting literal"⟩
          | none =>
              -- Selection first: when a slot is selectable its decision is
              -- exactly the old `maybeReduce`/restart/`selectDecision` path,
              -- while the full `fixedAssignment` list is built only when no
              -- slot can be selected (every slot fixed, or an empty domain).
              match selectDecision p st o prio orders with
              | some (l, vopt) =>
                  have hprops2 : PropsSound p T (maybeReduce st).props :=
                    hprops1.congr (maybeReduce_props st)
                  let st := maybeReduce st
                  have hroot2 : RootInv p T init st := maybeReduce_rootInv hroot1
                  if hrs : restartDue o st && st.level > 0 then
                    -- Restart at a decision boundary: every learned clause from
                    -- the preceding conflict has already been asserted and
                    -- drained, so this only discards the current decision stack.
                    let st := { st with restarts := st.restarts + 1 }
                    let st := { st with lastRestartConflict := st.stats.conflicts }
                    have hroot3 : RootInv p T init st :=
                      hroot2.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl
                    have hpos : 0 < st.level := by
                      have h2 := (Bool.and_eq_true_iff.mp hrs).2
                      simpa using of_decide_eq_true h2
                    have hprops3 : PropsSound p T (backjump st 0).props :=
                      hprops2.congr (backjump_props st 0)
                    let st0 := backjump st 0
                    have hroot4 : RootInv p T init st0 :=
                      hroot3.backjump hpos
                    let st := st0.trimReasonsStats
                    have hroot5 : RootInv p T init st :=
                      hroot4.trimReasonsStats
                    have hpending' : PendingRoot p st #[] := by
                      intro h0 item hit
                      simp at hit
                    search p T init o prio orders st #[] hroot5 hpending' hprops3 f
                  else
                    let s := atomSlot l.lit.atom
                    -- Under `incumbent` the phase array is the round's
                    -- fixed seed, so a decision must not overwrite it with
                    -- the value chosen this round.  The other strategies
                    -- keep ordinary phase saving.
                    let phases :=
                      match vopt with
                      | some v =>
                          if o.val == .incumbent then st.phases
                          else st.phases.setGrow s v default
                      | none => st.phases
                    let st := { st with
                      phases := phases
                      stats := { st.stats with
                        decisions := st.stats.decisions + 1
                        maxLevel := max st.stats.maxLevel (st.level + 1) } }
                    have hroot3 : RootInv p T init st :=
                      hroot2.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl
                    have hprops3 : PropsSound p T (newLevel st).props :=
                      hprops2.congr (newLevel_props st)
                    let st := newLevel st
                    have hroot4 : RootInv p T init st := hroot3.newLevel
                    have hpending' : PendingRoot p st
                        #[{ lit := l, reason := .decision, count := false }] := by
                      intro h0 item hit
                      simp only [List.mem_singleton] at hit
                      subst item
                      simp [st, newLevel] at h0
                    search p T init o prio orders st
                      #[{ lit := l, reason := .decision, count := false }]
                      hroot4 hpending' hprops3 f
              | none =>
                  match fixedAssignment st with
                  | some a =>
                      if fitsB (domProblem p) a then
                        if accepts p a then ⟨(.sat a, st), hroot1, hprops1⟩
                        else ⟨giveUpWith st "final assignment rejected by the constraints",
                          giveUpWith_rootInv hroot1 _,
                          giveUpWith_props hprops1 "final assignment rejected by the constraints"⟩
                      else ⟨giveUpWith st "final assignment outside the converted box",
                        giveUpWith_rootInv hroot1 _,
                        giveUpWith_props hprops1 "final assignment outside the converted box"⟩
                  | none =>
                      -- No selectable slot but some slot is not fixed (an empty
                      -- domain): keep the old reduce/restart-then-give-up path.
                      have hprops2 : PropsSound p T (maybeReduce st).props :=
                        hprops1.congr (maybeReduce_props st)
                      let st := maybeReduce st
                      have hroot2 : RootInv p T init st := maybeReduce_rootInv hroot1
                      if hrs : restartDue o st && st.level > 0 then
                        let st := { st with restarts := st.restarts + 1 }
                        let st := { st with lastRestartConflict := st.stats.conflicts }
                        have hroot3 : RootInv p T init st :=
                          hroot2.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl
                        have hpos : 0 < st.level := by
                          have h2 := (Bool.and_eq_true_iff.mp hrs).2
                          simpa using of_decide_eq_true h2
                        have hprops3 : PropsSound p T (backjump st 0).props :=
                          hprops2.congr (backjump_props st 0)
                        let st0 := backjump st 0
                        have hroot4 : RootInv p T init st0 :=
                          hroot3.backjump hpos
                        let st := st0.trimReasonsStats
                        have hroot5 : RootInv p T init st :=
                          hroot4.trimReasonsStats
                        have hpending' : PendingRoot p st #[] := by
                          intro h0 item hit
                          simp at hit
                        search p T init o prio orders st #[] hroot5 hpending' hprops3 f
                      else ⟨giveUpWith st "no selectable slot and an empty domain",
                        giveUpWith_rootInv hroot2 _,
                        giveUpWith_props hprops2 "no selectable slot and an empty domain"⟩

/-! ## Search soundness -/

set_option maxHeartbeats 1600000 in
/-- Every `.sat` result of the loop is a box member accepted by the
problem. -/
theorem search_sat (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) :
    ∀ (fuel : Nat) (st : EngineState p T) (pending : Array Pending)
      (hroot : RootInv p T init st) (hpending : PendingRoot p st pending)
      (hprops : PropsSound p T st.props) (a : List Value),
      (search p T init o prio orders st pending hroot hpending hprops fuel).res.1 = .sat a →
      a ∈ allAssigns p.domains ∧ accepts p a = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pending hroot hpending hprops a h
      simp [search] at h
  | succ f ih =>
      intro st pending hroot hpending hprops a h
      rw [search.eq_2] at h
      dsimp only at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · -- conflict: analysis
            split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · simp at h
                · split at h
                  · simp at h
                  · split at h
                    · exact ih _ _ _ _ _ _ h
                    · simp at h
          · -- no conflict: decision first, then the fixed-assignment leaf
            split at h
            · -- a slot is selectable: restart or decision
              split at h
              · exact ih _ _ _ _ _ _ h
              · exact ih _ _ _ _ _ _ h
            · -- no selectable slot: fixed assignment / empty fallback
              cases hfa : fixedAssignment (drain p T st pending (f + 1)).st with
              | none =>
                  simp only [hfa] at h
                  split at h
                  · exact ih _ _ _ _ _ _ h
                  · simp at h
              | some a' =>
                  simp only [hfa] at h
                  by_cases hfit : fitsB (domProblem p) a' = true
                  · by_cases hacc : accepts p a' = true
                    · simp [hfit, hacc] at h
                      subst h
                      exact ⟨(fitsB_iff_mem_allAssigns_problem (domProblem p) a').mp
                        hfit, hacc⟩
                    · simp [hfit, hacc] at h
                  · simp [hfit] at h

set_option maxHeartbeats 1600000 in
/-- Every `.unsat` result of the loop excludes every accepted assignment:
the only `.unsat` leaf is an entailed empty learned clause. -/
theorem search_unsat (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) :
    ∀ (fuel : Nat) (st : EngineState p T) (pending : Array Pending)
      (hroot : RootInv p T init st) (hpending : PendingRoot p st pending)
      (hprops : PropsSound p T st.props),
      (search p T init o prio orders st pending hroot hpending hprops fuel).res.1 = .unsat →
      ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pending hroot hpending hprops h
      simp [search] at h
  | succ f ih =>
      intro st pending hroot hpending hprops h
      rw [search.eq_2] at h
      dsimp only at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · -- conflict: analysis
            split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · -- entailed empty clause, at any decision level
                  rename_i hconf hok lc hlearned hemp
                  exact entailed_nil_unsat
                    (analyze_empty_unsat
                      (drain_rootInv st pending (f + 1) hroot hpending hprops).conv
                      (drain_rootInv st pending (f + 1) hroot hpending hprops).hist.1
                      (drain_rootInv st pending (f + 1) hroot hpending hprops)
                      (by simpa using hok) hlearned (by simpa using hemp))
                · split at h
                  · simp at h
                  · split at h
                    · exact ih _ _ _ _ _ h
                    · simp at h
          · -- no conflict: decision first, then the fixed-assignment leaf
            split at h
            · -- a slot is selectable: restart or decision
              split at h
              · exact ih _ _ _ _ _ h
              · exact ih _ _ _ _ _ h
            · -- no selectable slot: fixed assignment / empty fallback
              cases hfa : fixedAssignment (drain p T st pending (f + 1)).st with
              | none =>
                  simp only [hfa] at h
                  split at h
                  · exact ih _ _ _ _ _ h
                  · simp at h
              | some a' =>
                  simp only [hfa] at h
                  by_cases hfit : fitsB (domProblem p) a' = true
                  · by_cases hacc : accepts p a' = true
                    · simp [hfit, hacc] at h
                    · simp [hfit, hacc] at h
                  · simp [hfit] at h

/-! ## Entry and the Frozen Public Seam -/

/-- An empty stored-clause lookup yields an entailed empty clause. -/
theorem emptyConflict_entailed {p : CompiledProblem DomConstraint} {T : LitTable}
    {db : ClauseDB p T} {c : EClause p T}
    (h : db.emptyConflict? = some c) : Entailed p [] := by
  obtain ⟨id, sc, hsc, hdel, hsize, he⟩ := ClauseDB.emptyConflict?_spec db h
  subst he
  have hto : sc.e.lits.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hsize
  have hdec : T.decodeClause sc.e.lits = [] := by
    simp [LitTable.decodeClause, hto]
  simpa [hdec] using sc.e.ent

/-- The seed-clause entry's returned empty clause is entailed. -/
theorem addSeedClauses_empty_entailed {p : CompiledProblem DomConstraint} {T : LitTable}
    {st st' : EngineState p T} {e : EClause p T}
    (h : addSeedClauses p T st = (st', some e)) : Entailed p [] := by
  have hconf :
      (addSeedClausesFrom p T (seedClauses p.constraints).attach st).db.emptyConflict?
        = some e := by
    simpa [addSeedClauses] using congrArg Prod.snd h
  exact emptyConflict_entailed hconf

/-- The second projection form of `addSeedClauses_empty_entailed`. -/
theorem addSeedClauses_snd_entailed {p : CompiledProblem DomConstraint}
    {T : LitTable} {st : EngineState p T} {e : EClause p T}
    (h : (addSeedClauses p T st).2 = some e) : Entailed p [] := by
  cases hsc : addSeedClauses p T st with
  | mk st' o =>
      simp only [hsc, Prod.snd] at h
      subst h
      exact addSeedClauses_empty_entailed hsc

/-- Annotation orders used by `annot` value selection (a plain `def` so
the entry proof does not have to split the configuration test). -/
def configOrders (p : CompiledProblem DomConstraint) (o : SearchConfig) :
    List AnnValOrder :=
  if o.val == .annot then annotOrders p.source p.names else []

/-- Seed the saved-phase array from a previous round's incumbent.  The array
is indexed by slot, like `fixedAssignment`; a value that is absent from the
(possibly tightened) current domain is ignored by `phaseLiteral`, and a
short list simply leaves the remaining slots without a saved phase. -/
def seedPhases (st : EngineState p T) (prev : Option (List Value)) :
    EngineState p T :=
  match prev with
  | none => st
  | some a => { st with phases := a.toArray }

@[simp] theorem seedPhases_none (st : EngineState p T) :
    seedPhases st none = st := rfl

@[simp] theorem seedPhases_some (st : EngineState p T) (a : List Value) :
    seedPhases st (some a) = { st with phases := a.toArray } := rfl

theorem seedPhases_doms (st : EngineState p T) (prev : Option (List Value)) :
    (seedPhases st prev).doms = st.doms := by
  cases prev with
  | none => rfl
  | some a => rfl

theorem seedPhases_histInv {st : EngineState p T} (h : HistInv st.doms st)
    (prev : Option (List Value)) :
    HistInv (seedPhases st prev).doms (seedPhases st prev) := by
  cases prev with
  | none => simpa using h
  | some a =>
      exact HistInv.congr (st' := { st with phases := a.toArray }) h rfl rfl
        (fun s => rfl) rfl rfl rfl rfl

/-- Saved-phase seeding changes only the phase array. -/
theorem seedPhases_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (prev : Option (List Value)) :
    RootInv p T init (seedPhases st prev) := by
  cases prev with
  | none => simpa using h
  | some a =>
      exact RootInv.of_eq (st' := seedPhases st (some a)) h rfl rfl
        (fun _ => rfl) rfl rfl rfl rfl h.table_inv h.lits_wf h.db_inv

theorem seedPhases_table (st : EngineState p T) (prev : Option (List Value)) :
    (seedPhases st prev).table = st.table := by
  cases prev with
  | none => rfl
  | some a => rfl

theorem seedPhases_props (st : EngineState p T) (prev : Option (List Value)) :
    (seedPhases st prev).props = st.props := by
  cases prev with
  | none => rfl
  | some a => rfl

theorem dbUpdate_histInv {st : EngineState p T} (h : HistInv st.doms st)
    (db : ClauseDB p T) :
    HistInv ({ st with db := db }).doms ({ st with db := db }) :=
  HistInv.congr (st' := { st with db := db }) h rfl rfl (fun s => rfl)
    rfl rfl rfl rfl

/-- Reindex the initial-domain parameter of `RootInv` along an equality of
initial-domain arrays. -/
theorem RootInv.init_congr {p : CompiledProblem DomConstraint} {T : LitTable}
    {init init' : Array DomC} {st : EngineState p T}
    (h : RootInv p T init st) (he : init' = init) : RootInv p T init' st := by
  subst he
  exact h

/-- The entry body after the initial state has been built: add the seed
clauses, run root propagation, then start the loop.  `RootInv` and
`PropsSound` are proof-only; the executable state is unchanged by the seed
clauses and the root `propagateUnits` step (both only touch the clause
database). -/
def coreSolveFrom (p : CompiledProblem DomConstraint) (T : LitTable)
    (o : SearchConfig) (st0 : EngineState p T)
    (hroot : RootInv p T st0.doms st0)
    (hprops : PropsSound p T st0.props)
    (prio : Array Nat) (orders : List AnnValOrder) (fuel : Nat) :
    CoreResult × EngineStats :=
  let sc := addSeedClauses p T st0
  let st1 : EngineState p T := sc.1
  have hroot1 : RootInv p T st1.doms st1 :=
    (addSeedClauses_fst_rootInv (p := p) (T := T) hroot).init_congr
      (by dsimp only [st1, sc]; rw [addSeedClauses_fst_doms])
  have hprops1 : PropsSound p T st1.props :=
    hprops.congr (by dsimp only [st1, sc]; rw [addSeedClauses_fst_props])
  match hsc : sc.2 with
  | some _ =>
      -- An entailed empty seed clause is a root refutation.
      let st2 := { st1 with stats := { st1.stats with conflicts := st1.stats.conflicts + 1 } }
      (.unsat, st2.stats)
  | none =>
      match st1.db.emptyConflict? with
      | some _ => (.unsat, st1.stats)
      | none =>
          let r := st1.db.propagateUnits p T st1.doms
          let st2 : EngineState p T := { st1 with db := r.1 }
          have hroot2 : RootInv p T st2.doms st2 := by
            simpa only [st2, r] using propagateUnits_rootInv hroot1
          have hprops2 : PropsSound p T st2.props := by
            simpa only [st2, r] using hprops1
          match hr2 : r.2 with
          | .none =>
              let res := search p T st2.doms o prio orders st2 #[]
                hroot2 (by intro h0 item hit; simp at hit) hprops2 fuel
              (res.res.1, res.res.2.stats)
          | .prune ps =>
              have hp : PendingRoot p st2 (pushClausePrunes #[] ps) :=
                pushClausePrunes_pendingRoot_of_entailed
                  (by intro h0 item hit; simp at hit)
                  (fun h0 q id hq =>
                    ClauseDB.propagateUnits_prunes_entailed st1.db st1.doms hr2 q id hq)
              let res := search p T st2.doms o prio orders st2
                (pushClausePrunes #[] ps) hroot2 hp hprops2 fuel
              (res.res.1, res.res.2.stats)
          | .conflict ec _ =>
              let a := analyze p T st2.doms st2 hroot2.conv hroot2.hist.1 hroot2 ec fuel
              if !a.ok then
                (.gaveUp, { st2.stats with
                  gaveUp := 1,
                  gaveUpCause := a.why })
              else
                match a.learned with
                | none => (.gaveUp, { st2.stats with
                    gaveUp := 1,
                    gaveUpCause := "root analysis returned no learned clause" })
                | some lc =>
                    if lc.lits.isEmpty then (.unsat, st2.stats)
                    else (.gaveUp, { st2.stats with
                      gaveUp := 1,
                      gaveUpCause := "root conflict learned an empty clause above level 0" })

/-- An entry state bundled with the invariants needed by the search loop.
The proof fields are erased at runtime. -/
structure EntryState (p : CompiledProblem DomConstraint) (T : LitTable) where
  st : EngineState p T
  root : RootInv p T st.doms st
  props : PropsSound p T st.props

/-- Bundle `initState` with its entry invariants. -/
def initStateBundled (p : CompiledProblem DomConstraint) :
    Option (EntryState p {}) :=
  match h : initState p {} with
  | none => none
  | some st => some ⟨st, initState_rootInv h LitTable.inv_empty, initState_propsSound h⟩

/-- Entry plus the CDCL loop over a bundled entry state.  This is the common
body of the ordinary and prepared entries. -/
def coreSolveFullWithBundled (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat)
    (init? : Option (EntryState p {})) : CoreResult × EngineStats :=
  match init? with
  | none => (.gaveUp, { gaveUp := 1, gaveUpCause := "entry guard or domain conversion failed" })
  | some es =>
      let st0 := es.st
      let stSeed := seedPhases st0 prev
      let prio := annotPrioArray p
      let orders := configOrders p o
      coreSolveFrom p {} o stSeed
        ((seedPhases_rootInv es.root prev).init_congr (seedPhases_doms st0 prev))
        (es.props.congr (seedPhases_props st0 prev))
        prio orders fuel

/-- Entry plus the CDCL loop with the saved phases seeded from a previous
incumbent, returning the terminal stats as well. -/
def coreSolveFullWith (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveFullWithBundled p o prev fuel (initStateBundled p)

/-- Bundle the prepared entry with its invariants. -/
def initStateBundledPrepared (p : CompiledProblem DomConstraint)
    (doms : Array DomC) (hconv : convertDomains p.domains = some doms) :
    Option (EntryState p {}) :=
  match h : initStatePrepared p {} doms hconv with
  | none => none
  | some st =>
      some ⟨st,
        initState_rootInv (by rw [← initStatePrepared_eq hconv]; exact h) LitTable.inv_empty,
        initState_propsSound (by rw [← initStatePrepared_eq hconv]; exact h)⟩

/-- The state projection of the ordinary bundle is the ordinary entry. -/
theorem initStateBundled_st (p : CompiledProblem DomConstraint) :
    (initStateBundled p).map EntryState.st = initState p {} := by
  unfold initStateBundled
  split
  · rename_i heq
    rw [heq]
    rfl
  · rename_i st heq
    exact heq.symm

/-- The state projection of the prepared bundle is the prepared entry. -/
theorem initStateBundledPrepared_st (p : CompiledProblem DomConstraint)
    (doms : Array DomC) (hconv : convertDomains p.domains = some doms) :
    (initStateBundledPrepared p doms hconv).map EntryState.st =
      initStatePrepared p {} doms hconv := by
  unfold initStateBundledPrepared
  split
  · rename_i heq
    rw [heq]
    rfl
  · rename_i st heq
    exact heq.symm

/-- The bundled entry's result depends only on the entry state, not on the
proof fields carrying its invariants. -/
theorem coreSolveFullWithBundled_proof_irrel (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat)
    {init1 init2 : Option (EntryState p {})}
    (h : init1.map EntryState.st = init2.map EntryState.st) :
    coreSolveFullWithBundled p o prev fuel init1 =
      coreSolveFullWithBundled p o prev fuel init2 := by
  cases init1 with
  | none =>
      cases init2 with
      | none => rfl
      | some es2 => simp [Option.map] at h
  | some es1 =>
      cases init2 with
      | none => simp [Option.map] at h
      | some es2 =>
          cases es1 with
          | mk st1 root1 props1 =>
          cases es2 with
          | mk st2 root2 props2 =>
          have hs : st1 = st2 := by simpa [EntryState.st, Option.map] using h
          subst hs
          rfl

/-- Entry plus the CDCL loop, with an already converted domain array supplied
by the caller.  All other setup is per round. -/
def coreSolveFullWithPrepared (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) (doms : Array DomC)
    (hconv : convertDomains p.domains = some doms) : CoreResult × EngineStats :=
  coreSolveFullWithBundled p o prev fuel (initStateBundledPrepared p doms hconv)

/-- The prepared entry returns exactly the ordinary entry's result when the
supplied array is the conversion result. -/
theorem coreSolveFullWithPrepared_eq (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat)
    (doms : Array DomC) (hconv : convertDomains p.domains = some doms) :
    coreSolveFullWithPrepared p o prev fuel doms hconv =
      coreSolveFullWith p o prev fuel := by
  unfold coreSolveFullWithPrepared coreSolveFullWith
  apply coreSolveFullWithBundled_proof_irrel
  rw [initStateBundledPrepared_st, initStateBundled_st, initStatePrepared_eq hconv]

/-- Entry plus the CDCL loop, returning the terminal stats as well. -/
def coreSolveFull (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveFullWith p o none fuel

/-- Core's fuel-bounded search. -/
def coreSolve (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult :=
  (coreSolveFull p o fuel).1

/-- Core's fuel-bounded search with the saved phases seeded from a previous
incumbent. -/
def coreSolveWith (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat) : CoreResult :=
  (coreSolveFullWith p o prev fuel).1

/-- The default Core fuel budget. -/
def coreFuel : Nat := 2 ^ 62

/-- Public diagnostic text for an incomplete Core run.  The cause is
statistics only; it never changes the verdict. -/
def giveUpReason (st : EngineStats) : String :=
  if st.gaveUpCause.isEmpty then "Core search incomplete (gaveUp)"
  else s!"Core search incomplete (gaveUp): {st.gaveUpCause}"

/-- The first component of `coreSolveFull` is `coreSolve`. -/
theorem coreSolveFull_fst (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : (coreSolveFull p o fuel).1 = coreSolve p o fuel := rfl

theorem coreSolveFrom_sat {p : CompiledProblem DomConstraint} {T : LitTable}
    {o : SearchConfig} {st : EngineState p T}
    {hroot : RootInv p T st.doms st} {hprops : PropsSound p T st.props}
    {prio : Array Nat} {orders : List AnnValOrder} {fuel : Nat} {a : List Value}
    (h : (coreSolveFrom p T o st hroot hprops prio orders fuel).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  simp only [coreSolveFrom] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · dsimp only at h
        exact search_sat p T _ o prio orders _ _ _ _ _ _ _ h
      · dsimp only at h
        exact search_sat p T _ o prio orders _ _ _ _ _ _ _ h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp at h

/-- Every `.sat` result of the seeded entry is a box member accepted by the
problem.  The seeded phases are policy metadata: the final `fitsB`/`accepts`
check is unchanged. -/
theorem coreSolveFullWith_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    {a : List Value}
    (h : (coreSolveFullWith p o prev fuel).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveFullWith coreSolveFullWithBundled initStateBundled at h
  dsimp only at h
  split at h
  · simp at h
  · exact coreSolveFrom_sat h

/-- Every `.sat` result of the entry is a box member accepted by the
problem. -/
theorem coreSolveFull_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : (coreSolveFull p o fuel).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFullWith_sat h

theorem coreSolveFrom_unsat {p : CompiledProblem DomConstraint} {T : LitTable}
    {o : SearchConfig} {st : EngineState p T}
    {hroot : RootInv p T st.doms st} {hprops : PropsSound p T st.props}
    {prio : Array Nat} {orders : List AnnValOrder} {fuel : Nat}
    (h : (coreSolveFrom p T o st hroot hprops prio orders fuel).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  simp only [coreSolveFrom] at h
  split at h
  · rename_i hseed
    exact entailed_nil_unsat (addSeedClauses_snd_entailed hseed)
  · split at h
    · rename_i hempty
      exact entailed_nil_unsat (emptyConflict_entailed hempty)
    · split at h
      · dsimp only at h
        exact search_unsat p T _ o prio orders _ _ _ _ _ _ h
      · dsimp only at h
        exact search_unsat p T _ o prio orders _ _ _ _ _ _ h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · rename_i hok x lc hlearned hemp
              exact entailed_nil_unsat
                (analyze_empty_unsat _ _ _ (by simpa using hok) hlearned
                  (by simpa using hemp))
            · simp at h

/-- Every `.unsat` result of the seeded entry excludes every accepted
assignment. -/
theorem coreSolveFullWith_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    (h : (coreSolveFullWith p o prev fuel).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveFullWith coreSolveFullWithBundled initStateBundled at h
  dsimp only at h
  split at h
  · simp at h
  · exact coreSolveFrom_unsat h

/-- Every `.unsat` result of the entry excludes every accepted
assignment. -/
theorem coreSolveFull_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat}
    (h : (coreSolveFull p o fuel).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFullWith_unsat h

/-- Core's SAT soundness. -/
theorem coreSolve_sat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : coreSolve p o fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFull_sat h

/-- Core's UNSAT soundness. -/
theorem coreSolve_unsat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {fuel : Nat}
    (h : coreSolve p o fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFull_unsat h

/-- Core's SAT soundness with incumbent-seeded phases. -/
theorem coreSolveWith_sat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    {a : List Value} (h : coreSolveWith p o prev fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFullWith_sat h

/-- Core's UNSAT soundness with incumbent-seeded phases. -/
theorem coreSolveWith_unsat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    (h : coreSolveWith p o prev fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFullWith_unsat h

end LeanFzn.Engine

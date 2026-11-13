/-
File: LeanFzn.Engine.Proofs.PruneSound

The pruning-soundness contract used by the root-entailment invariant (R1).

A propagator is *prune-sound* when every literal it prunes is currently
unassigned in a well-formed view and every other literal of the emitted
reason clause is currently false.  Together with `EClause.ent`, this turns
a level-0 propagation into a unit consequence of the problem: the reason
clause is satisfied by every accepted assignment, all the non-target
literals are false there, hence the target is true.

The per-family proofs are already available as the `*_prune_lit_none`
lemmas in `Engine/Props`; this module collects them into the uniform
`PropV2.PruneSound` contract.

Dependencies: the `Engine.Props` family modules (for `ViewWF` and the
per-family contracts).
DAG: Engine.Props.* -> Engine.Proofs.PruneSound -> Engine.Proofs.Queue.Root
-/
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.AllDiff
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Arith
import LeanFzn.Engine.Props.Order
import LeanFzn.Engine.Props.LinearExt
import LeanFzn.Engine.Props.BoolExt
import LeanFzn.Engine.Props.Element

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-- Every pruning emitted by one propagator names its own target: in a
well-formed view the target is unassigned and every other literal of the
decoded reason clause is false. -/
def PropV2.PruneSound (pr : PropV2 p T) : Prop :=
  ∀ view ps, ViewWF view pr.vars → pr.run view = .prune ps → ∀ q ∈ ps.toList,
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ l ∈ T.decodeClause q.2.lits, l ≠ q.1.lit →
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false

theorem PropV2.pruneSound_of_never_prunes {p : CompiledProblem DomConstraint}
    {T : LitTable} {pr : PropV2 p T}
    (h : ∀ (view : EngineView) (ps : Array (PLit × EClause p T)),
      pr.run view ≠ .prune ps) :
    pr.PruneSound := by
  intro view ps _ hrun
  exact absurd hrun (h view ps)

/-- Every propagator in the fixed propagation table built by `propsOf`
satisfies the pruning contract.  The table is created once at search entry
and never modified, so this is a static property of the array. -/
def PropsSound (p : CompiledProblem DomConstraint) (T : LitTable)
    (props : Array (PropV2 p T)) : Prop :=
  ∀ (id : Nat) (pr : PropV2 p T), props[id]? = some pr → PropV2.PruneSound pr

section Wrappers

variable {p : CompiledProblem DomConstraint} {T : LitTable}

/-- Transport `ViewWF` across an equality of the listed slots. -/
theorem viewWF_of_vars_eq {view : EngineView} {pr : PropV2 p T} {slots : Array Nat}
    (h : pr.vars = slots) (hWF : ViewWF view pr.vars) : ViewWF view slots := by
  rwa [h] at hWF

theorem ViewWF.mono {view : EngineView} {xs ys : Array Nat}
    (h : ViewWF view ys) (hsub : ∀ s ∈ xs.toList, s ∈ ys.toList) :
    ViewWF view xs := by
  intro i hi
  exact h.dom_wf (hsub xs[i] (by
    rw [Array.mem_toList_iff]
    exact Array.getElem_mem hi))

/-- The `atomSlot` function agrees with the atom's `slot` field. -/
private theorem atomSlot_eq_slot (a : Atom) : atomSlot a = a.slot := by
  cases a <;> rfl


/-! ## Arithmetic three-slot families -/

theorem plusPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.plusSlot i j k ∈ p.constraints) :
    (plusPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact plusPropWith_prune_lit_none p T i j k hmem view hWF hrun hq

theorem timesPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.timesSlot i j k ∈ p.constraints) :
    (timesPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact timesPropWith_prune_lit_none p T i j k hmem view hWF hrun hq

theorem minPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.minSlot i j k ∈ p.constraints) :
    (minPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact minPropWith_prune_lit_none p T i j k hmem view hWF hrun hq

theorem maxPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.maxSlot i j k ∈ p.constraints) :
    (maxPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact maxPropWith_prune_lit_none p T i j k hmem view hWF hrun hq

theorem absPropWith_pruneSound (i k : Nat)
    (hmem : DomConstraint.absSlot i k ∈ p.constraints) :
    (absPropWith p T i k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact absPropWith_prune_lit_none p T i k hmem view hWF hrun hq

theorem minPairPropWith_pruneSound (o0 o1 r : DomIntArg)
    (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints) :
    (minPairPropWith p T o0 o1 r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact minPairPropWith_prune_lit_none p T o0 o1 r hmem view hWF hrun hq

theorem maxPairPropWith_pruneSound (o0 o1 r : DomIntArg)
    (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints) :
    (maxPairPropWith p T o0 o1 r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact maxPairPropWith_prune_lit_none p T o0 o1 r hmem view hWF hrun hq

theorem minGenPropWith_pruneSound (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints) :
    (minGenPropWith p T os r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at hrun
      exact emptyGenPropWith_prune_lit_none p T _ hmem r _ view
        (by simpa [minGenPropWith_nil p T r hmem, emptyGenPropWith, rel3PropWith] using hWF)
        (fun s hs => minGen_slots_mem hs) hrun hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at hrun
        simp [fixGenPropWith] at hrun
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at hrun
        exact forcedValuePropWith_prune_lit_none p T _ hmem r _ _ view
          (by simpa [minGenPropWith_cons_some p T o os' r ks hmem hks,
            forcedValuePropWith, rel3PropWith] using hWF)
          (fun s hs => minGen_slots_mem hs) hrun hq

theorem maxGenPropWith_pruneSound (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints) :
    (maxGenPropWith p T os r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at hrun
      exact emptyGenPropWith_prune_lit_none p T _ hmem r _ view
        (by simpa [maxGenPropWith_nil p T r hmem, emptyGenPropWith, rel3PropWith] using hWF)
        (fun s hs => maxGen_slots_mem hs) hrun hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at hrun
        simp [fixGenPropWith] at hrun
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at hrun
        exact forcedValuePropWith_prune_lit_none p T _ hmem r _ _ view
          (by simpa [maxGenPropWith_cons_some p T o os' r ks hmem hks,
            forcedValuePropWith, rel3PropWith] using hWF)
          (fun s hs => maxGen_slots_mem hs) hrun hq

theorem divPropWith_pruneSound (o1 o2 r : DomIntArg)
    (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints) :
    (divPropWith p T o1 o2 r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact divPropWith_prune_lit_none p T o1 o2 r hmem view hWF hrun hq

theorem modPropWith_pruneSound (o1 o2 r : DomIntArg)
    (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints) :
    (modPropWith p T o1 o2 r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact modPropWith_prune_lit_none p T o1 o2 r hmem view hWF hrun hq

/-! ## Order families -/

theorem lePropWith_pruneSound (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) :
    (lePropWith p T i j hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.leSlot i j)).toArray :=
    viewWF_of_vars_eq (by simp [lePropWith]) hWF
  exact lePropWith_prune_lit_none p T i j hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem ltPropWith_pruneSound (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) :
    (ltPropWith p T i j hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.ltSlot i j)).toArray :=
    viewWF_of_vars_eq (by simp [ltPropWith]) hWF
  exact ltPropWith_prune_lit_none p T i j hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem eqPropWith_pruneSound (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) :
    (eqPropWith p T init i j hinit hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.eqSlot i j)).toArray :=
    viewWF_of_vars_eq (by simp [eqPropWith]) hWF
  exact eqPropWith_prune_lit_none p init i j hinit hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem leConstHiPropWith_pruneSound (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) :
    (leConstHiPropWith p T i c hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact leConstHiPropWith_prune_lit_none p T i c hmem view hrun hq

theorem leConstLoPropWith_pruneSound (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) :
    (leConstLoPropWith p T i c hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact leConstLoPropWith_prune_lit_none p T i c hmem view hrun hq

theorem ltConstHiPropWith_pruneSound (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) :
    (ltConstHiPropWith p T i c hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact ltConstHiPropWith_prune_lit_none p T i c hmem view hrun hq

theorem ltConstLoPropWith_pruneSound (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) :
    (ltConstLoPropWith p T i c hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact ltConstLoPropWith_prune_lit_none p T i c hmem view hrun hq

theorem bool2intPropWith_pruneSound (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) :
    (bool2intPropWith p T i k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.bool2intSlot i k)).toArray :=
    viewWF_of_vars_eq (by simp [bool2intPropWith]) hWF
  exact bool2intPropWith_prune_lit_none p T i k hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem eqReifPropWith_pruneSound (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) :
    (eqReifPropWith p T i j r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.eqReifSlot i j r)).toArray :=
    viewWF_of_vars_eq (by simp [eqReifPropWith]) hWF
  exact eqReifPropWith_prune_lit_none p T i j r hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem leReifPropWith_pruneSound (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) :
    (leReifPropWith p T i j r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.leReifSlot i j r)).toArray :=
    viewWF_of_vars_eq (by simp [leReifPropWith]) hWF
  exact leReifPropWith_prune_lit_none p T i j r hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

theorem neReifPropWith_pruneSound (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) :
    (neReifPropWith p T i j r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view (dcSlotsFull (DomConstraint.neReifSlot i j r)).toArray :=
    viewWF_of_vars_eq (by simp [neReifPropWith]) hWF
  exact neReifPropWith_prune_lit_none p T i j r hmem view
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull]))
    (hWF'.dom_wf (by simp [dcSlotsFull])) hrun hq

/-! ## Boolean support families -/

theorem boolSupportPropWith_pruneSound (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args → ∀ b, b ∈ allAssigns p.domains →
        accepts p b = true → R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args → ∀ b, b ∈ allAssigns p.domains →
        accepts p b = true → ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v)) :
    (boolSupportPropWith p T R slots hR hbool).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolSupportPropWith_prune_lit_none p T R slots hR hbool view hrun hq

theorem boolNotPropWith_pruneSound (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) :
    (boolNotPropWith p T i j hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolNotPropWith_prune_lit_none p T i j hmem view hrun hq

theorem boolAndPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) :
    (boolAndPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolAndPropWith_prune_lit_none p T i j k hmem view hrun hq

theorem boolOrPropWith_pruneSound (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) :
    (boolOrPropWith p T i j k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolOrPropWith_prune_lit_none p T i j k hmem view hrun hq

theorem boolEqPropWith_pruneSound (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) :
    (boolEqPropWith p T i j hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolEqPropWith_prune_lit_none p T i j hmem view hrun hq

theorem boolSupportDupPropWith_pruneSound (R : List Bool → Bool)
    (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args → ∀ b, b ∈ allAssigns p.domains →
        accepts p b = true → R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args → ∀ b, b ∈ allAssigns p.domains →
        accepts p b = true → ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v)) :
    (boolSupportDupPropWith p T R slots hR hbool).PruneSound := by
  intro view ps hWF hrun q hq
  exact boolSupportDupPropWith_prune_lit_none p T R slots hR hbool view hrun hq

theorem boolNotPropChoice_pruneSound (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) :
    (boolNotPropChoice p T i j hmem).PruneSound := by
  unfold boolNotPropChoice
  by_cases hd : BArgs.hasDupSlots [i, j] = true
  · simp only [hd, if_true]
    exact boolSupportDupPropWith_pruneSound boolNotR [i, j] _ _
  · simp only [hd, Bool.false_eq_true, if_false]
    exact boolNotPropWith_pruneSound i j hmem

theorem boolAndPropChoice_pruneSound (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) :
    (boolAndPropChoice p T i j k hmem).PruneSound := by
  unfold boolAndPropChoice
  by_cases hd : BArgs.hasDupSlots [i, j, k] = true
  · simp only [hd, if_true]
    exact boolSupportDupPropWith_pruneSound boolAndR [i, j, k] _ _
  · simp only [hd, Bool.false_eq_true, if_false]
    exact boolAndPropWith_pruneSound i j k hmem

theorem boolOrPropChoice_pruneSound (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) :
    (boolOrPropChoice p T i j k hmem).PruneSound := by
  unfold boolOrPropChoice
  by_cases hd : BArgs.hasDupSlots [i, j, k] = true
  · simp only [hd, if_true]
    exact boolSupportDupPropWith_pruneSound boolOrR [i, j, k] _ _
  · simp only [hd, Bool.false_eq_true, if_false]
    exact boolOrPropWith_pruneSound i j k hmem

theorem boolEqPropChoice_pruneSound (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) :
    (boolEqPropChoice p T i j hmem).PruneSound := by
  unfold boolEqPropChoice
  by_cases hd : BArgs.hasDupSlots [i, j] = true
  · simp only [hd, if_true]
    exact boolSupportDupPropWith_pruneSound boolEqR [i, j] _ _
  · simp only [hd, Bool.false_eq_true, if_false]
    exact boolEqPropWith_pruneSound i j hmem

/-! ## Element families -/

theorem arrayIntElementPropWith_pruneSound (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints) :
    (arrayIntElementPropWith p T xs i k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact arrayIntElementPropWith_prune_lit_none p T xs i k hmem view hWF hrun hq

theorem arrayVarIntElementPropWith_pruneSound (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints) :
    (arrayVarIntElementPropWith p T is i k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact arrayVarIntElementPropWith_prune_lit_none p T is i k hmem view hWF hrun hq

theorem arrayVarBoolElementPropWith_pruneSound (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints) :
    (arrayVarBoolElementPropWith p T is i k hmem).PruneSound := by
  intro view ps hWF hrun q hq
  exact arrayVarBoolElementPropWith_prune_lit_none p T is i k hmem view hWF hrun hq

/-! ## Linear families -/

theorem linLePropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints) :
    (linLePropWith p T coeffs is b hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWF' : ViewWF view is.toArray :=
      viewWF_of_vars_eq (by simp [linLePropWith]) hWF
    exact linLePropWith_prune_lit_none p T coeffs is b view hmem hsize hWF' hrun hq
  · rw [linLePropWith_run_fix_of_size_ne p T coeffs is b view hmem hlen] at hrun
    cases hrun

theorem linEqPropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints) :
    (linEqPropWith p T coeffs is b hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWFfull : ViewWF view (dcSlotsFull (DomConstraint.linEq coeffs is b)).toArray :=
      viewWF_of_vars_eq (by simp [linEqPropWith]) hWF
    have hWF' : ViewWF view is.toArray :=
      hWFfull.mono (by
        intro s hs
        simpa [dcSlotsFull] using hs)
    exact linEqPropWith_prune_lit_none p T coeffs is b view hmem hsize hWF' hrun hq
  · rw [linEqPropWith_run_fix_of_size_ne p T coeffs is b view hmem hlen] at hrun
    cases hrun

theorem linNePropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints) :
    (linNePropWith p T coeffs is b hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWFfull : ViewWF view (dcSlotsFull (DomConstraint.linNe coeffs is b)).toArray :=
      viewWF_of_vars_eq (by simp [linNePropWith]) hWF
    have hWF' : ViewWF view is.toArray :=
      hWFfull.mono (by
        intro s hs
        simpa [dcSlotsFull] using hs)
    have hguard : viewIntKindB view is.toArray = true := by
      apply Classical.byContradiction
      intro hg
      have hfix : (linNePropWith p T coeffs is b hmem).run view = .fix := by
        unfold linNePropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · rw [dif_neg hg]
      rw [hfix] at hrun
      cases hrun
    exact linNePropWith_prune_lit_none p T coeffs is b view hmem hsize hWF'
      hguard hrun hq
  · rw [linNePropWith_run_fix_of_size_ne p T coeffs is b view hmem hlen] at hrun
    cases hrun

theorem linEqReifPropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints) :
    (linEqReifPropWith p T coeffs is b r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWFfull : ViewWF view (dcSlotsFull (DomConstraint.linEqReif coeffs is b r)).toArray :=
      viewWF_of_vars_eq (by simp [linEqReifPropWith]) hWF
    have hWF' : ViewWF view is.toArray :=
      hWFfull.mono (by
        intro s hs
        have hs' : s ∈ is := by simpa using hs
        simpa [dcSlotsFull] using List.mem_append_left [r] hs')
    have hslots : slotsIntB p is = true := by
      apply Classical.byContradiction
      intro hs
      have hfix : (linEqReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linEqReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · rw [dif_neg hs]
      rw [hfix] at hrun
      cases hrun
    have hguard : viewIntKindB view is.toArray = true := by
      apply Classical.byContradiction
      intro hg
      have hfix : (linEqReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linEqReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · rw [dif_pos hslots, dif_neg hg]
      rw [hfix] at hrun
      cases hrun
    exact linEqReifPropWith_prune_lit_none p T coeffs is b r view hmem hsize
      hWF' hslots hguard hrun hq
  · rw [linEqReifPropWith_run_fix_of_size_ne p T coeffs is b r view hmem hlen] at hrun
    cases hrun

theorem linLeReifPropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints) :
    (linLeReifPropWith p T coeffs is b r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWFfull : ViewWF view (dcSlotsFull (DomConstraint.linLeReif coeffs is b r)).toArray :=
      viewWF_of_vars_eq (by simp [linLeReifPropWith]) hWF
    have hWF' : ViewWF view is.toArray :=
      hWFfull.mono (by
        intro s hs
        have hs' : s ∈ is := by simpa using hs
        simpa [dcSlotsFull] using List.mem_append_left [r] hs')
    have hslots : slotsIntB p is = true := by
      apply Classical.byContradiction
      intro hs
      have hfix : (linLeReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linLeReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · simp [dif_neg hs]
      rw [hfix] at hrun
      cases hrun
    have hguard : viewIntKindB view is.toArray = true := by
      apply Classical.byContradiction
      intro hg
      have hfix : (linLeReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linLeReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · simp [dif_pos hslots, dif_neg hg]
      rw [hfix] at hrun
      cases hrun
    exact linLeReifPropWith_prune_lit_none p T coeffs is b r view hmem hsize
      hWF' hslots hguard hrun hq
  · rw [linLeReifPropWith_run_fix_of_size_ne p T coeffs is b r view hmem hlen] at hrun
    cases hrun

theorem linNeReifPropWith_pruneSound (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints) :
    (linNeReifPropWith p T coeffs is b r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  by_cases hlen : coeffs.length = is.length
  · have hsize : coeffs.toArray.size = is.toArray.size := by simpa using hlen
    have hWFfull : ViewWF view (dcSlotsFull (DomConstraint.linNeReif coeffs is b r)).toArray :=
      viewWF_of_vars_eq (by simp [linNeReifPropWith]) hWF
    have hWF' : ViewWF view is.toArray :=
      hWFfull.mono (by
        intro s hs
        have hs' : s ∈ is := by simpa using hs
        simpa [dcSlotsFull] using List.mem_append_left [r] hs')
    have hslots : slotsIntB p is = true := by
      apply Classical.byContradiction
      intro hs
      have hfix : (linNeReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linNeReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · rw [dif_neg hs]
      rw [hfix] at hrun
      cases hrun
    have hguard : viewIntKindB view is.toArray = true := by
      apply Classical.byContradiction
      intro hg
      have hfix : (linNeReifPropWith p T coeffs is b r hmem).run view = .fix := by
        unfold linNeReifPropWith
        dsimp only
        rw [dif_pos hsize]
        split
        · rfl
        · rw [dif_pos hslots, dif_neg hg]
      rw [hfix] at hrun
      cases hrun
    exact linNeReifPropWith_prune_lit_none p T coeffs is b r view hmem hsize
      hWF' hslots hguard hrun hq
  · rw [linNeReifPropWith_run_fix_of_size_ne p T coeffs is b r view hmem hlen] at hrun
    cases hrun

theorem nePropWith_pruneSound (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.neSlot i j ∈ p.constraints) :
    (nePropWith p T init i j hinit hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view #[i, j] := by simpa [nePropWith] using hWF
  cases hdi : (view.doms.getD i DomC.empty).fixedValue with
  | none =>
    cases hdj : (view.doms.getD j DomC.empty).fixedValue with
    | none =>
      simp only [nePropWith, hdi, hdj] at hrun
      cases hrun
    | some vj =>
      simp only [nePropWith, hdi, hdj] at hrun
      split at hrun
      · rename_i hm
        split at hrun
        · rename_i hgi
          split at hrun
          · rename_i hgj
            cases hrun
            simp at hq
            obtain rfl := hq
            have h := nePropWith_prune_lit_none_symm p init i j hinit hmem view vj hdi hdj
              (hWF'.dom_wf (by simp)) hm
            refine ⟨?_, ?_⟩
            · simpa [pLit, atomSlot_neLit] using h.1
            · intro l hl hne
              have hl' : l = neLit i vj ∨ l = neLit j vj := by
                simpa [EClause.ofLiterals, EClause.ofLits, LitTable.decodeClause,
                  LitTable.decode, pLit] using hl
              rcases hl' with rfl | rfl
              · exact absurd rfl hne
              · simpa [atomSlot_neLit] using h.2
          · cases hrun
        · cases hrun
      · cases hrun
  | some vi =>
    cases hdj : (view.doms.getD j DomC.empty).fixedValue with
    | none =>
      simp only [nePropWith, hdi, hdj] at hrun
      split at hrun
      · rename_i hm
        split at hrun
        · rename_i hgi
          split at hrun
          · rename_i hgj
            cases hrun
            simp at hq
            obtain rfl := hq
            have h := nePropWith_prune_lit_none p init i j hinit hmem view vi hdi hdj
              (hWF'.dom_wf (by simp)) hm
            refine ⟨?_, ?_⟩
            · simpa [pLit, atomSlot_neLit] using h.2
            · intro l hl hne
              have hl' : l = neLit i vi ∨ l = neLit j vi := by
                simpa [EClause.ofLiterals, EClause.ofLits, LitTable.decodeClause,
                  LitTable.decode, pLit] using hl
              rcases hl' with rfl | rfl
              · simpa [atomSlot_neLit] using h.1
              · exact absurd rfl hne
          · cases hrun
        · cases hrun
      · cases hrun
    | some vj =>
      simp only [nePropWith, hdi, hdj] at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · cases hrun
          · cases hrun
        · cases hrun
      · cases hrun

theorem boolClausePropWith_pruneSound (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) :
    (boolClausePropWith p T ps ns hmem).PruneSound := by
  intro view psArr hWF hrun q hq
  unfold boolClausePropWith at hrun
  dsimp only at hrun
  by_cases hhit : (boolClauseScan view (boolClauseLits ps ns)).hit = true
  · simp only [hhit] at hrun
    cases hrun
  · have hhitf : (boolClauseScan view (boolClauseLits ps ns)).hit = false := by
      simpa using hhit
    by_cases hcount0 : (boolClauseScan view (boolClauseLits ps ns)).count = 0
    · simp only [hhitf, hcount0] at hrun
      cases hrun
    · by_cases hcount1 : (boolClauseScan view (boolClauseLits ps ns)).count = 1
      · cases hunit : (boolClauseScan view (boolClauseLits ps ns)).unit with
        | none =>
          simp only [hhitf, hcount0, hcount1, hunit] at hrun
          cases hrun
        | some u =>
          simp only [hhitf, hcount0, hcount1, hunit] at hrun
          cases hrun
          simp at hq
          obtain rfl := hq
          obtain ⟨u', hu', humem, hueval, hother⟩ :=
            boolClausePropWith_prune_lit_none p T ps ns hmem view hhitf hcount1
          have huu : u' = u := by
            rw [hu'] at hunit
            exact Option.some.inj hunit
          subst huu
          refine ⟨?_, ?_⟩
          · simpa [pLit, atomSlot_eq_slot] using hueval
          · intro l hl hne
            have hl' : l ∈ (boolClauseLits ps ns).toList := by
              simpa [EClause.ofLiterals, EClause.ofLits, LitTable.decodeClause,
                LitTable.decode, pLit] using hl
            simpa [atomSlot_eq_slot] using hother l hl' hne
      · simp only [hhitf, hcount0, hcount1] at hrun
        cases hrun

/-! ## Helper: another `curF` source exists when position `p` is not one -/

theorem anyOtherCurF_of_anyCurF {src : List BArg} {p : Nat}
    (hp : p < src.length) (hany : anyCurF src = true)
    (hpF : (src.getD p default).curF = false) :
    anyOtherCurF src p = true := by
  rw [anyCurF_eq_true] at hany
  obtain ⟨a, ha, haF⟩ := hany
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ha
  rw [anyOtherCurF_eq_true]
  refine ⟨i, hi, ?_, ?_⟩
  · have hgd : src.getD i default = a := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hget
    rw [hgd]
    exact haF
  · intro hip
    subst hip
    have hgd : src.getD i default = a := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hget
    rw [hgd] at hpF
    rw [hpF] at haF
    cases haF

/-! ## Helper: a target slot is currently full -/

theorem mem_arrayBoolAndTargets_cur {src : List BArg} {ak : BArg} {t : BTarget}
    (h : t ∈ arrayBoolAndTargets src ak)
    (hconf : arrayBoolAndConflict src ak = false) :
    ∃ a, a ∈ src ++ [ak] ∧ a.slot = t.slot ∧ a.curF = true ∧ a.curT = true := by
  have hD : ((ak.curF && anyCurF src) || (ak.curT && allCurT src)) = true := by
    cases hb : ((ak.curF && anyCurF src) || (ak.curT && allCurT src)) with
    | true => rfl
    | false =>
        exfalso
        have hc : arrayBoolAndConflict src ak = true := by
          simp [arrayBoolAndConflict, hb]
        rw [hc] at hconf
        cases hconf
  unfold arrayBoolAndTargets at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at h
  rcases h with (⟨p, hp, h⟩ | h) | h
  · rcases h with h | h
    · by_cases hf : ((src.getD p default).curF && !ak.curF) = true
      · rw [if_pos hf] at h
        simp only [List.mem_singleton] at h
        subst h
        have hf' := Bool.and_eq_true_iff.mp hf
        have hakF : ak.curF = false := by
          simpa only [Bool.not_eq_true'] using hf'.2
        have hsecond : ak.curT = true ∧ allCurT src = true := by
          rcases Bool.or_eq_true_iff.mp hD with h1 | h2
          · rw [hakF] at h1
            simp at h1
          · exact Bool.and_eq_true_iff.mp h2
        have haT : (src.getD p default).curT = true :=
          (allCurT_eq_true.mp hsecond.2) _ (BArgs.getD_mem hp)
        exact ⟨src.getD p default, List.mem_append_left _ (BArgs.getD_mem hp), rfl,
          hf'.1, haT⟩
      · rw [if_neg hf] at h
        simp at h
    · by_cases ht : ((src.getD p default).curT &&
          !((ak.curT && allCurT src) ||
            (ak.curF && anyOtherCurF src p))) = true
      · rw [if_pos ht] at h
        simp only [List.mem_singleton] at h
        subst h
        have ht' := Bool.and_eq_true_iff.mp ht
        have hnot : ((ak.curT && allCurT src) ||
            (ak.curF && anyOtherCurF src p)) = false := by
          simpa only [Bool.not_eq_true'] using ht'.2
        have hnot1 : (ak.curT && allCurT src) = false :=
          (Bool.or_eq_false_iff.mp hnot).1
        have hnot2 : (ak.curF && anyOtherCurF src p) = false :=
          (Bool.or_eq_false_iff.mp hnot).2
        have haF : (src.getD p default).curF = true := by
          apply Classical.byContradiction
          intro hf
          have hf' : (src.getD p default).curF = false := by
            cases hv : (src.getD p default).curF with
            | false => rfl
            | true => exact absurd hv hf
          rcases Bool.or_eq_true_iff.mp hD with h1 | h2
          · have hfirst := Bool.and_eq_true_iff.mp h1
            have hother : anyOtherCurF src p = true :=
              anyOtherCurF_of_anyCurF hp hfirst.2 hf'
            have hcontra : (ak.curF && anyOtherCurF src p) = true := by
              rw [hfirst.1, hother]
              rfl
            rw [hcontra] at hnot2
            cases hnot2
          · have hsecond := Bool.and_eq_true_iff.mp h2
            have hcontra : (ak.curT && allCurT src) = true := by
              rw [hsecond.1, hsecond.2]
              rfl
            rw [hcontra] at hnot1
            cases hnot1
        exact ⟨src.getD p default, List.mem_append_left _ (BArgs.getD_mem hp), rfl,
          haF, ht'.1⟩
      · rw [if_neg ht] at h
        simp at h
  · by_cases hf : (ak.curF && !anyCurF src) = true
    · rw [if_pos hf] at h
      simp only [List.mem_singleton] at h
      subst h
      have hf' := Bool.and_eq_true_iff.mp hf
      have hanyF : anyCurF src = false := by
        simpa only [Bool.not_eq_true'] using hf'.2
      have hakT : ak.curT = true := by
        rcases Bool.or_eq_true_iff.mp hD with h1 | h2
        · rw [hanyF] at h1
          simp at h1
        · exact (Bool.and_eq_true_iff.mp h2).1
      exact ⟨ak, by simp, rfl, hf'.1, hakT⟩
    · rw [if_neg hf] at h
      simp at h
  · by_cases ht : (ak.curT && !allCurT src) = true
    · rw [if_pos ht] at h
      simp only [List.mem_singleton] at h
      subst h
      have ht' := Bool.and_eq_true_iff.mp ht
      have hallF : allCurT src = false := by
        simpa only [Bool.not_eq_true'] using ht'.2
      have hakF : ak.curF = true := by
        rcases Bool.or_eq_true_iff.mp hD with h1 | h2
        · exact (Bool.and_eq_true_iff.mp h1).1
        · rw [hallF] at h2
          simp at h2
      exact ⟨ak, by simp, rfl, hakF, ht'.1⟩
    · rw [if_neg ht] at h
      simp at h

/-! ## The `array_bool_and` wrapper -/

theorem arrayBoolAndPropFast_pruneSound (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints) :
    (arrayBoolAndPropFast p T is k hmem).PruneSound := by
  intro view ps _hWF hrun q hq
  unfold arrayBoolAndPropFast at hrun
  dsimp only at hrun
  by_cases hguard : is.all (BArgs.initBoolB p) = true
  · simp only [dif_pos hguard] at hrun
    split at hrun
    · cases hrun
    · rename_i src ak plan hplan
      obtain ⟨hsrc, hak, _hdup, hplanEq⟩ := arrayBoolAndPlanOf_some hplan
      have hargs : BArgs.ofSlots view.doms (is ++ [k]) = some (src ++ [ak]) :=
        ofSlots_append_singleton is hsrc hak
      obtain ⟨hc, _hne, hforall⟩ := BPlan.out_run_prune p T plan _ _ hrun
      have hconfFalse : arrayBoolAndConflict src ak = false := by
        cases hb : arrayBoolAndConflict src ak with
        | false => rfl
        | true =>
            have hsome : plan.conflict? = some (BArgs.fixedLits (src ++ [ak])) := by
              rw [hplanEq]
              simp [arrayBoolAndPlanFast, hb]
            rw [hc] at hsome
            cases hsome
      obtain ⟨q', hq'plan, hlit, hdec, _hent⟩ := hforall q hq
      have hq' : q' ∈ arrayBoolAndPrunesFast src ak := by
        have hpr : plan.prunes = arrayBoolAndPrunesFast src ak := by
          rw [hplanEq]
          simp [arrayBoolAndPlanFast, hconfFalse]
        rwa [hpr] at hq'plan
      obtain ⟨t, ht, hq'eq⟩ := mem_arrayBoolAndPrunesFast hq'
      obtain ⟨a, hamem, haslot, haF, haT⟩ :=
        mem_arrayBoolAndTargets_cur ht hconfFalse
      have hmk : BArg.mk? view.doms a.slot = some a :=
        BArgs.ofSlots_mem_mk hargs hamem
      refine ⟨?_, ?_⟩
      · have hlit' : q.1.lit = posBool t.slot (!t.val) := by
          rw [hlit, hq'eq]
          rfl
        rw [hlit']
        have hsl : t.slot = a.slot := haslot.symm
        rw [hsl]
        simpa [posBool, atomSlot] using BArg.ofDom?_evalLit_none_full hmk haF haT (!t.val)
      · intro l hl hne
        rw [hdec] at hl
        rw [hq'eq] at hl
        simp only [BTarget.toPrune, List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact absurd (hlit.trans (by rw [hq'eq]; rfl)).symm hne
        · have hfalse := BArgs.ofSlots_eval_fixed hargs hl
          simpa [atomSlot_eq_slot] using hfalse
  · simp only [dif_neg hguard] at hrun
    cases hrun

/-! ## The `all_different` propagator -/

theorem neLit_atom_slot (s : Nat) (v : Value) : (neLit s v).atom.slot = s := by
  cases v <;> rfl

/-! ## Items -/

theorem allDiffItemOfDom?_bounds {doms : Array DomC} {s : Nat} {x : AllDiffItem}
    (h : allDiffItemOfDom? doms s = some x) :
    (doms.getD x.slot DomC.empty).lo? = some x.lo ∧
      (doms.getD x.slot DomC.empty).hi? = some x.hi := by
  unfold allDiffItemOfDom? at h
  cases hb : allDiffBounds? doms s with
  | none => simp [hb] at h
  | some q =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      unfold allDiffBounds? at hb
      dsimp only at hb
      split at hb
      · rename_i hk
        split at hb
        · rename_i hlo hhi
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact ⟨by simpa using hlo, by simpa using hhi⟩
        · cases hb
      · cases hb

theorem allDiffItem_mem_bounds {items : List AllDiffItem} {is : List Nat}
    {doms : Array DomC} {x : AllDiffItem} (hx : x ∈ items)
    (hitems : ∀ y ∈ items, y.slot ∈ is)
    (hitemsSrc : items = allDiffHallItems is doms) :
    ∃ s ∈ is, allDiffItemOfDom? doms s = some x := by
  subst hitemsSrc
  unfold allDiffHallItems at hx
  obtain ⟨s, hs, hf⟩ := List.mem_filterMap.mp (List.mem_mergeSort.mp hx)
  exact ⟨s, hs, hf⟩

/-! ## Fixed slots -/

theorem mem_allDiffFixedSlots {is : List Nat} {doms : Array DomC}
    {a : AllDiffFixed is} (h : a ∈ allDiffFixedSlots is doms) :
    (doms.getD a.slot DomC.empty).fixedValue = some a.value := by
  unfold allDiffFixedSlots at h
  obtain ⟨x, hx, hf⟩ := List.mem_filterMap.mp h
  rw [Array.getD_eq_getD_getElem?] at hf
  cases hfv : (doms[x.1]?.getD DomC.empty).fixedValue with
  | none => simp [hfv] at hf
  | some v =>
      rw [hfv] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      simpa [Array.getD_eq_getD_getElem?] using hfv

/-! ## Generic fold membership -/

theorem mem_foldl_spec {α β : Type} (step : Array β → α → Array β)
    (hstep : ∀ acc a, step acc a = acc ∨ ∃ e, step acc a = acc.push e) :
    ∀ (l : List α) (acc : Array β) {q},
      q ∈ (l.foldl step acc).toList →
      q ∈ acc.toList ∨ ∃ a ∈ l, ∃ acc', step acc' a = acc'.push q := by
  intro l
  induction l with
  | nil =>
      intro acc q h
      exact Or.inl (by simpa using h)
  | cons a as ih =>
      intro acc q h
      rw [List.foldl_cons] at h
      rcases hstep acc a with hacc | ⟨e, he⟩
      · rw [hacc] at h
        rcases ih acc h with h1 | ⟨b, hb, acc', hb'⟩
        · exact Or.inl h1
        · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, acc', hb'⟩
      · rw [he] at h
        rcases ih (acc.push e) h with h1 | ⟨b, hb, acc', hb'⟩
        · rw [Array.mem_toList_iff, Array.mem_push] at h1
          rcases h1 with h1 | h1
          · exact Or.inl (by rwa [Array.mem_toList_iff])
          · exact Or.inr ⟨a, by simp, acc, by simpa [h1] using he⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, acc', hb'⟩

/-! ## Membership of one fixed-prune step -/

theorem mem_allDiffPrunesFor (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (doms : Array DomC) (a : AllDiffFixed is)
    (hgi : (init.getD a.slot DomC.empty).mem a.value = true)
    {q : PLit × EClause p T}
    (h : q ∈ (allDiffPrunesFor p T is init hinit hmem doms a hgi).toList) :
    ∃ b ∈ is, b ≠ a.slot ∧
      (doms.getD b DomC.empty).fixedValue = none ∧
      (doms.getD b DomC.empty).mem a.value = true ∧
      (init.getD b DomC.empty).mem a.value = true ∧
      q.1.lit = neLit b a.value ∧
      T.decodeClause q.2.lits = [neLit a.slot a.value, neLit b a.value] := by
  let step : Array (PLit × EClause p T) → {s // s ∈ is} → Array (PLit × EClause p T) :=
    fun acc b =>
      if hne : b.1 ≠ a.slot then
        let db := doms.getD b.1 DomC.empty
        if _hfix : db.fixedValue = none then
          if _hm : db.mem a.value = true then
            if hgj : (init.getD b.1 DomC.empty).mem a.value = true then
              acc.push (pLit (neLit b.1 a.value),
                EClause.ofLiterals p T [neLit a.slot a.value, neLit b.1 a.value]
                  (allDiff_ne_pair_entailed p is init hinit hmem
                    a.slot b.1 a.mem b.2 (Ne.symm hne) a.value hgi hgj))
            else acc
          else acc
        else acc
      else acc
  have hstep : ∀ acc b, step acc b = acc ∨ ∃ e, step acc b = acc.push e := by
    intro acc b
    dsimp only [step]
    by_cases hne : b.1 ≠ a.slot
    · simp only [dif_pos hne]
      by_cases hfix : (doms.getD b.1 DomC.empty).fixedValue = none
      · simp only [dif_pos hfix]
        by_cases hm : (doms.getD b.1 DomC.empty).mem a.value = true
        · simp only [dif_pos hm]
          by_cases hgj : (init.getD b.1 DomC.empty).mem a.value = true
          · simp only [dif_pos hgj]
            exact Or.inr ⟨_, rfl⟩
          · simp only [dif_neg hgj]
            exact Or.inl trivial
        · simp only [dif_neg hm]
          exact Or.inl trivial
      · simp only [dif_neg hfix]
        exact Or.inl trivial
    · simp only [dif_neg hne]
      exact Or.inl trivial
  unfold allDiffPrunesFor at h
  rcases mem_foldl_spec step hstep is.attach #[] h with
    h0 | ⟨b, hb, acc, hpush⟩
  · simp at h0
  · dsimp only [step] at hpush
    by_cases hne : b.1 ≠ a.slot
    · simp only [dif_pos hne] at hpush
      by_cases hfix : (doms.getD b.1 DomC.empty).fixedValue = none
      · simp only [dif_pos hfix] at hpush
        by_cases hm : (doms.getD b.1 DomC.empty).mem a.value = true
        · simp only [dif_pos hm] at hpush
          by_cases hgj : (init.getD b.1 DomC.empty).mem a.value = true
          · simp only [dif_pos hgj] at hpush
            have hpair := (Array.push_eq_push.mp hpush).1
            refine ⟨b.1, b.2, hne, hfix, hm, hgj, ?_, ?_⟩
            · rw [← hpair]
              rfl
            · rw [← hpair]
              exact LitTable.decodeClause_map_pLit T _
          · simp only [dif_neg hgj] at hpush
            exfalso
            have hsz := congrArg Array.size hpush
            simp at hsz
        · simp only [dif_neg hm] at hpush
          exfalso
          have hsz := congrArg Array.size hpush
          simp at hsz
      · simp only [dif_neg hfix] at hpush
        exfalso
        have hsz := congrArg Array.size hpush
        simp at hsz
    · simp only [dif_neg hne] at hpush
      exfalso
      have hsz := congrArg Array.size hpush
      simp at hsz


/-- Membership in an array-append is membership in the `.toList` pieces. -/
theorem mem_toList_append_iff {α : Type} {q : α} {xs ys : Array α} :
    q ∈ (xs ++ ys).toList ↔ q ∈ xs.toList ∨ q ∈ ys.toList := by
  rw [Array.mem_toList_iff, Array.mem_append, ← Array.mem_toList_iff,
    ← Array.mem_toList_iff]

theorem allDiffCollectPrunes_aux (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (doms : Array DomC) :
    ∀ (fs : List (AllDiffFixed is)) (acc : Array (PLit × EClause p T)) {q},
      q ∈ (fs.foldl (fun acc a =>
        if hgi : (init.getD a.slot DomC.empty).mem a.value = true then
          acc ++ allDiffPrunesFor p T is init hinit hmem doms a hgi
        else acc) acc).toList →
      q ∈ acc.toList ∨ ∃ a ∈ fs, ∃ hgi,
        q ∈ (allDiffPrunesFor p T is init hinit hmem doms a hgi).toList := by
  intro fs
  induction fs with
  | nil =>
      intro acc q h
      exact Or.inl (by simpa using h)
  | cons a as ih =>
      intro acc q h
      rw [List.foldl_cons] at h
      by_cases hgi : (init.getD a.slot DomC.empty).mem a.value = true
      · simp only [dif_pos hgi] at h
        rcases ih (acc ++ allDiffPrunesFor p T is init hinit hmem doms a hgi) h with
          h1 | ⟨b, hb, hgj, hq⟩
        · rw [mem_toList_append_iff] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨a, by simp, hgi, h1⟩
        · exact Or.inr ⟨b, by simp [hb], hgj, hq⟩
      · simp only [dif_neg hgi] at h
        rcases ih acc h with h1 | ⟨b, hb, hgj, hq⟩
        · exact Or.inl h1
        · exact Or.inr ⟨b, by simp [hb], hgj, hq⟩

theorem allDiffCollectPrunes_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    {doms : Array DomC} {fs : List (AllDiffFixed is)} {q : PLit × EClause p T}
    (h : q ∈ (allDiffCollectPrunes p T is init hinit hmem doms fs).toList) :
    ∃ a ∈ fs, ∃ hgi,
      q ∈ (allDiffPrunesFor p T is init hinit hmem doms a hgi).toList := by
  rcases allDiffCollectPrunes_aux p T is init hinit hmem doms fs #[] h with
    h0 | ⟨a, ha, hgi, hq⟩
  · simp at h0
  · exact ⟨a, ha, hgi, hq⟩

/-- The fixed-value prune contract. -/
theorem allDiffPrunesFor_sound (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view is.toArray)
    {a : AllDiffFixed is} (ha : a ∈ allDiffFixedSlots is view.doms)
    {hgi : (init.getD a.slot DomC.empty).mem a.value = true}
    {q : PLit × EClause p T}
    (hq : q ∈ (allDiffPrunesFor p T is init hinit hmem view.doms a hgi).toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ l ∈ T.decodeClause q.2.lits, l ≠ q.1.lit →
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨b, hb, _hne, hfix, hm, _hgj, hlit, hdec⟩ :=
    mem_allDiffPrunesFor (p := p) (T := T) (is := is) (init := init)
      hinit hmem (doms := view.doms) (a := a) (hgi := hgi) (q := q) hq
  have hfixA : (view.doms.getD a.slot DomC.empty).fixedValue = some a.value :=
    mem_allDiffFixedSlots ha
  have hWFa : (view.doms.getD a.slot DomC.empty).WF :=
    hWF.dom_wf (by rw [Array.mem_toList_iff]; exact List.mem_toArray.mpr a.mem)
  have hWFb : (view.doms.getD b DomC.empty).WF :=
    hWF.dom_wf (by rw [Array.mem_toList_iff]; exact List.mem_toArray.mpr hb)
  refine ⟨?_, ?_⟩
  · rw [hlit, atomSlot_eq_slot, neLit_atom_slot]
    exact DomC.evalLit_neLit_none_of_not_fixed (s := b) hfix hm
  · intro l hl hne
    rw [hdec] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [atomSlot_eq_slot, neLit_atom_slot]
      exact DomC.evalLit_neLit_fixed_false (s := a.slot) hWFa hfixA
    · exact absurd hlit.symm hne


theorem posLe_atom_slot (s : Nat) (k : Int) : (posLe s k).atom.slot = s := rfl
theorem negLe_atom_slot (s : Nat) (k : Int) : (negLe s k).atom.slot = s := rfl

/-! ## Membership in the Hall prune block -/

theorem mem_allDiffHallPrunesFor (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (S : List Nat) (a b : Int)
    (hSsub : ∀ s ∈ S, s ∈ is) (hSnd : S.Nodup)
    (hlen : S.length = (b - a + 1).toNat)
    {q : PLit × EClause p T}
    (h : q ∈ (allDiffHallPrunesFor p T init is hinit hmem hint items hitems
      S a b hSsub hSnd hlen).toList) :
    ∃ x ∈ items, x.slot ∉ S ∧
      (((a ≤ x.lo ∧ x.lo ≤ b ∧ b < x.hi) ∧
          q.1.lit = negLe x.slot b ∧
          T.decodeClause q.2.lits = hallExactLits x.slot S a b) ∨
        ((a ≤ x.hi ∧ x.lo < a ∧ x.hi ≤ b) ∧
          q.1.lit = posLe x.slot (a - 1) ∧
          T.decodeClause q.2.lits = hallExactLits x.slot S a b)) := by
  let step : Array (PLit × EClause p T) → {x // x ∈ items} →
      Array (PLit × EClause p T) :=
    fun acc x =>
      let j := x.1.slot
      if hjS : j ∈ S then acc
      else
        if decide (a ≤ x.1.lo) && decide (x.1.lo ≤ b) && decide (b < x.1.hi) then
          acc.push (pLit (negLe j b),
            EClause.ofLiterals p T (hallExactLits j S a b)
              (allDiff_hall_exact_entailed p is init hinit hmem hint S j a b
                hSsub hSnd hlen (hitems x.1 x.2) hjS))
        else if decide (a ≤ x.1.hi) && decide (x.1.lo < a) && decide (x.1.hi ≤ b) then
          acc.push (pLit (posLe j (a - 1)),
            EClause.ofLiterals p T (hallExactLits j S a b)
              (allDiff_hall_exact_entailed p is init hinit hmem hint S j a b
                hSsub hSnd hlen (hitems x.1 x.2) hjS))
        else acc
  have hstep : ∀ acc x, step acc x = acc ∨ ∃ e, step acc x = acc.push e := by
    intro acc x
    dsimp only [step]
    by_cases hjS : x.1.slot ∈ S
    · simp only [dif_pos hjS]
      exact Or.inl trivial
    · simp only [dif_neg hjS]
      by_cases h1 : (decide (a ≤ x.1.lo) && decide (x.1.lo ≤ b) &&
          decide (b < x.1.hi)) = true
      · simp only [if_pos h1]
        exact Or.inr ⟨_, rfl⟩
      · simp only [if_neg h1]
        by_cases h2 : (decide (a ≤ x.1.hi) && decide (x.1.lo < a) &&
            decide (x.1.hi ≤ b)) = true
        · simp only [if_pos h2]
          exact Or.inr ⟨_, rfl⟩
        · simp only [if_neg h2]
          exact Or.inl trivial
  unfold allDiffHallPrunesFor at h
  rcases mem_foldl_spec step hstep items.attach #[] h with
    h0 | ⟨x, hx, acc, hpush⟩
  · simp at h0
  · dsimp only [step] at hpush
    by_cases hjS : x.1.slot ∈ S
    · simp only [dif_pos hjS] at hpush
      exfalso
      have hsz := congrArg Array.size hpush
      simp at hsz
    · simp only [dif_neg hjS] at hpush
      refine ⟨x.1, x.2, hjS, ?_⟩
      by_cases h1 : (decide (a ≤ x.1.lo) && decide (x.1.lo ≤ b) &&
          decide (b < x.1.hi)) = true
      · simp only [if_pos h1] at hpush
        have hpair := (Array.push_eq_push.mp hpush).1
        have h1' := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h1).1
        have h3 : decide (b < x.1.hi) = true := (Bool.and_eq_true_iff.mp h1).2
        refine Or.inl ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · exact of_decide_eq_true h1'.1
        · exact of_decide_eq_true h1'.2
        · exact of_decide_eq_true h3
        · rw [← hpair]
          rfl
        · rw [← hpair]
          exact LitTable.decodeClause_map_pLit T _
      · simp only [if_neg h1] at hpush
        by_cases h2 : (decide (a ≤ x.1.hi) && decide (x.1.lo < a) &&
            decide (x.1.hi ≤ b)) = true
        · simp only [if_pos h2] at hpush
          have hpair := (Array.push_eq_push.mp hpush).1
          have h2' := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h2).1
          have h3 : decide (x.1.hi ≤ b) = true := (Bool.and_eq_true_iff.mp h2).2
          refine Or.inr ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · exact of_decide_eq_true h2'.1
          · exact of_decide_eq_true h2'.2
          · exact of_decide_eq_true h3
          · rw [← hpair]
            rfl
          · rw [← hpair]
            exact LitTable.decodeClause_map_pLit T _
        · simp only [if_neg h2] at hpush
          exfalso
          have hsz := congrArg Array.size hpush
          simp at hsz


/-- The Hall prune contract, given that every slot of the Hall set `S`
currently sits inside `[a,b]`. -/
theorem allDiffHallPrunesFor_sound (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    {items : List AllDiffItem}
    {hitems : ∀ x ∈ items, x.slot ∈ is}
    {S : List Nat} {a b : Int}
    {hSsub : ∀ s ∈ S, s ∈ is} {hSnd : S.Nodup}
    {hlen : S.length = (b - a + 1).toNat}
    (view : EngineView) (hWF : ViewWF view is.toArray)
    (hItemsBound : ∀ x ∈ items,
      (view.doms.getD x.slot DomC.empty).lo? = some x.lo ∧
        (view.doms.getD x.slot DomC.empty).hi? = some x.hi)
    (hSbound : ∀ s ∈ S, ∃ lo hi,
      (view.doms.getD s DomC.empty).lo? = some lo ∧
        (view.doms.getD s DomC.empty).hi? = some hi ∧ a ≤ lo ∧ hi ≤ b)
    {q : PLit × EClause p T}
    (hq : q ∈ (allDiffHallPrunesFor p T init is hinit hmem hint items hitems
      S a b hSsub hSnd hlen).toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ l ∈ T.decodeClause q.2.lits, l ≠ q.1.lit →
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨x, hx, _hxS, hbranch⟩ :=
    mem_allDiffHallPrunesFor p T init is hinit hmem hint items hitems S a b
      hSsub hSnd hlen hq
  have hxb := hItemsBound x hx
  have hWFx : (view.doms.getD x.slot DomC.empty).WF :=
    hWF.dom_wf (by rw [Array.mem_toList_iff]; exact List.mem_toArray.mpr (hitems x hx))
  -- Escape literals of `S` are false.
  have hEscPos : ∀ s ∈ S,
      (view.doms.getD s DomC.empty).evalLit (posLe s (a - 1)) = some false := by
    intro s hs
    obtain ⟨lo, hi, hlo, hhi, hale, hhib⟩ := hSbound s hs
    have hWFs : (view.doms.getD s DomC.empty).WF :=
      hWF.dom_wf (by rw [Array.mem_toList_iff]; exact List.mem_toArray.mpr (hSsub s hs))
    have hle : lo ≤ hi := DomC.lo?_le_hi? _ hWFs hlo hhi
    exact evalLit_posLe_false_of_lo_gt hlo hhi (by omega) (by omega)
  have hEscNeg : ∀ s ∈ S,
      (view.doms.getD s DomC.empty).evalLit (negLe s b) = some false := by
    intro s hs
    obtain ⟨lo, hi, hlo, hhi, hale, hhib⟩ := hSbound s hs
    have hWFs : (view.doms.getD s DomC.empty).WF :=
      hWF.dom_wf (by rw [Array.mem_toList_iff]; exact List.mem_toArray.mpr (hSsub s hs))
    have hle : lo ≤ hi := DomC.lo?_le_hi? _ hWFs hlo hhi
    exact evalLit_negLe_false_of_hi_le hlo hhi hhib (by omega)
  -- The `_`-suffixed helpers handle the escape tail of a reason.
  have escape : ∀ l ∈ hallEscapeLits S a b, l ≠ q.1.lit →
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
    intro l hl _
    rw [hallEscapeLits, List.mem_flatMap] at hl
    obtain ⟨s, hs, hl'⟩ := hl
    simp only [List.mem_cons] at hl'
    rcases hl' with rfl | rfl | hl''
    · rw [atomSlot_eq_slot, posLe_atom_slot]
      exact hEscPos s hs
    · rw [atomSlot_eq_slot, negLe_atom_slot]
      exact hEscNeg s hs
    · simp at hl''
  rcases hbranch with
    ⟨⟨hae, hle, hlt⟩, hlit, hdec⟩ | ⟨⟨hae, hlt, hle⟩, hlit, hdec⟩
  · -- `negLe x.slot b` is pruned; `posLe x.slot (a-1)` is the other literal.
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eq_slot, negLe_atom_slot]
      exact evalLit_negLe_none hxb.1 hxb.2 hle hlt
    · intro l hl hne
      rw [hdec] at hl
      simp only [hallExactLits, List.mem_cons] at hl
      rcases hl with rfl | rfl | hl
      · have hle' : x.lo ≤ x.hi := DomC.lo?_le_hi? _ hWFx hxb.1 hxb.2
        rw [atomSlot_eq_slot, posLe_atom_slot]
        exact evalLit_posLe_false_of_lo_gt hxb.1 hxb.2 (by omega) (by omega)
      · exact absurd hlit.symm hne
      · exact escape l hl hne
  · -- `posLe x.slot (a-1)` is pruned; `negLe x.slot b` is the other literal.
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eq_slot, posLe_atom_slot]
      exact evalLit_posLe_none hxb.1 hxb.2 (by omega) (by omega)
    · intro l hl hne
      rw [hdec] at hl
      simp only [hallExactLits, List.mem_cons] at hl
      rcases hl with rfl | rfl | hl
      · exact absurd hlit.symm hne
      · have hle' : x.lo ≤ x.hi := DomC.lo?_le_hi? _ hWFx hxb.1 hxb.2
        rw [atomSlot_eq_slot, negLe_atom_slot]
        exact evalLit_negLe_false_of_hi_le hxb.1 hxb.2 hle (by omega)
      · exact escape l hl hne


/-- The inner Hall sweep: any prune in the accumulated array either was
already in `acc` or comes from an exact-fill block whose Hall set sits in
`[a,b]`. -/
theorem sweepGo_block (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (hndItems : (items.map AllDiffItem.slot).Nodup)
    (hsorted : List.Pairwise (fun x y => x.hi ≤ y.hi) items)
    (view : EngineView)
    (hItemsBound : ∀ x ∈ items,
      (view.doms.getD x.slot DomC.empty).lo? = some x.lo ∧
        (view.doms.getD x.slot DomC.empty).hi? = some x.hi)
    (a : Int) :
    ∀ (rest : List AllDiffItem)
      (hRest : ∀ y ∈ rest, y ∈ items.filter (fun x => decide (a ≤ x.lo)))
      (k : Nat)
      (hRestLen : k + rest.length =
        (items.filter (fun x => decide (a ≤ x.lo))).length)
      (acc : Array (PLit × EClause p T))
      (hpre : rest = (items.filter (fun x => decide (a ≤ x.lo))).drop k) {q},
      (allDiffHallSweep.goA.go p T init is hinit hmem hint items hitems hndItems
        a rest hRest k hRestLen none acc).1 = none →
      q ∈ (allDiffHallSweep.goA.go p T init is hinit hmem hint items hitems hndItems
        a rest hRest k hRestLen none acc).2.toList →
      q ∈ acc.toList ∨
        ∃ (S : List Nat) (a b : Int) (hSsub : ∀ s ∈ S, s ∈ is) (hSnd : S.Nodup),
          (∀ s ∈ S, ∃ lo hi,
            (view.doms.getD s DomC.empty).lo? = some lo ∧
              (view.doms.getD s DomC.empty).hi? = some hi ∧ a ≤ lo ∧ hi ≤ b) ∧
          ∃ hlen : S.length = (b - a + 1).toNat,
            q ∈ (allDiffHallPrunesFor p T init is hinit hmem hint items hitems
              S a b hSsub hSnd hlen).toList := by
  let cand := items.filter (fun x => decide (a ≤ x.lo))
  have hcandSort : List.Pairwise (fun x y => x.hi ≤ y.hi) cand :=
    List.Pairwise.sublist List.filter_sublist hsorted
  intro rest
  induction rest with
  | nil =>
      intro hRest k hRestLen acc hpre q hconf hq
      rw [allDiffHallSweep.goA.go.eq_1] at hq
      exact Or.inl hq
  | cons x xs ih =>
      intro hRest k hRestLen acc hpre q hconf hq
      rw [allDiffHallSweep.goA.go.eq_3] at hconf hq
      by_cases hlt : (x.hi - a + 1).toNat < k + 1
      · simp only [dif_pos hlt] at hconf
        cases hconf
      · by_cases hEq : k + 1 = (x.hi - a + 1).toNat
        · -- Exact fill: the prefix `cand.take (k+1)` is a Hall set.
          simp only [dif_neg hlt, dif_pos hEq] at hconf hq
          have hk : k < cand.length := by
            have hlen : k + (xs.length + 1) = cand.length := by
              simpa using hRestLen
            omega
          have hdrop := List.drop_eq_getElem_cons (l := cand) hk
          rw [← hpre] at hdrop
          have hxeq : x = cand[k] := (List.cons.injEq ..).mp hdrop |>.1
          have hxs : xs = cand.drop (k + 1) := by
            have htail := (List.cons.injEq ..).mp hdrop |>.2
            simpa using htail
          have hRest' : ∀ y ∈ xs, y ∈ cand :=
            fun y hy => hRest y (List.mem_cons_of_mem x hy)
          have hRestLen' : (k + 1) + xs.length = cand.length := by
            have hlen : k + (xs.length + 1) = cand.length := by
              simpa using hRestLen
            omega
          have hq' := ih hRest' (k + 1) hRestLen' _ hxs (q := q) hconf hq
          rcases hq' with hacc | ⟨S, b, hSsub', hSnd', hbound, hlen, hmem⟩
          · -- `q` lies in the block just appended.
            rw [mem_toList_append_iff] at hacc
            rcases hacc with hacc | hblk
            · exact Or.inl hacc
            · have hSsub0 : ∀ s ∈ List.map AllDiffItem.slot (List.take (k + 1) cand),
                  s ∈ is := by
                intro s hs
                obtain ⟨y, hyTake, rfl⟩ := List.mem_map.mp hs
                have hyCand : y ∈ cand :=
                  List.Sublist.subset (List.take_sublist (k + 1) cand) hyTake
                exact hitems y (List.mem_filter.mp hyCand).1
              have hSnd0 : (List.map AllDiffItem.slot (List.take (k + 1) cand)).Nodup := by
                have hsub : (List.map AllDiffItem.slot (List.take (k + 1) cand)).Sublist
                    (items.map AllDiffItem.slot) :=
                  List.Sublist.trans (List.Sublist.map _ (List.take_sublist _ cand))
                    (List.Sublist.map _ List.filter_sublist)
                exact List.Nodup.sublist hsub hndItems
              have hbound0 : ∀ s ∈ List.map AllDiffItem.slot (List.take (k + 1) cand),
                  ∃ lo hi,
                    (view.doms.getD s DomC.empty).lo? = some lo ∧
                      (view.doms.getD s DomC.empty).hi? = some hi ∧ a ≤ lo ∧ hi ≤ x.hi := by
                intro s hs
                obtain ⟨y, hyTake, rfl⟩ := List.mem_map.mp hs
                have hyCand : y ∈ cand :=
                  List.Sublist.subset (List.take_sublist (k + 1) cand) hyTake
                have hyItems : y ∈ items := (List.mem_filter.mp hyCand).1
                obtain ⟨hylo, hyhi⟩ := hItemsBound y hyItems
                refine ⟨y.lo, y.hi, hylo, hyhi, ?_, ?_⟩
                · exact of_decide_eq_true (List.mem_filter.mp hyCand).2
                · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hyTake
                  have hiCand : i < cand.length := by
                    have : i < (cand.take (k + 1)).length := hi
                    rw [List.length_take] at this
                    omega
                  by_cases hik : i = k
                  · subst hik
                    rw [← hget, List.getElem_take, hxeq]
                    omega
                  · have hiklt : i < k := by
                      have hi' : i < (cand.take (k + 1)).length := hi
                      rw [List.length_take] at hi'
                      omega
                    have hrel := List.Pairwise.rel_getElem_of_lt hiCand hk hcandSort hiklt
                    rw [← hget, List.getElem_take, hxeq]
                    exact hrel
              exact Or.inr ⟨_, a, x.hi, hSsub0, hSnd0, hbound0, _, hblk⟩
          · exact Or.inr ⟨S, b, hSsub', hSnd', hbound, hlen, hmem⟩
        · -- Not an exact fill: the recursive call carries no new block.
          simp only [dif_neg hlt, dif_neg hEq] at hconf hq
          have hk : k < cand.length := by
            have hlen : k + (xs.length + 1) = cand.length := by
              simpa using hRestLen
            omega
          have hdrop := List.drop_eq_getElem_cons (l := cand) hk
          rw [← hpre] at hdrop
          have hxs : xs = cand.drop (k + 1) := by
            have htail := (List.cons.injEq ..).mp hdrop |>.2
            simpa using htail
          have hRest' : ∀ y ∈ xs, y ∈ cand :=
            fun y hy => hRest y (List.mem_cons_of_mem x hy)
          have hRestLen' : (k + 1) + xs.length = cand.length := by
            have hlen : k + (xs.length + 1) = cand.length := by
              simpa using hRestLen
            omega
          exact ih hRest' (k + 1) hRestLen' _ hxs (q := q) hconf hq


theorem hallItems_sorted (is : List Nat) (doms : Array DomC) :
    List.Pairwise (fun x y => x.hi ≤ y.hi) (allDiffHallItems is doms) := by
  unfold allDiffHallItems
  have h := List.pairwise_mergeSort
    (le := fun x y => decide (x.hi ≤ y.hi))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (by
      intro a b
      rw [Bool.or_eq_true_iff]
      by_cases h : a.hi ≤ b.hi
      · exact Or.inl (decide_eq_true_eq.mpr h)
      · exact Or.inr (decide_eq_true_eq.mpr (by omega)))
    (List.filterMap (allDiffItemOfDom? doms) is)
  simpa only [decide_eq_true_eq] using h

theorem hallItems_bound (initView : Array DomC) (is : List Nat) :
    ∀ x ∈ allDiffHallItems is initView,
      (initView.getD x.slot DomC.empty).lo? = some x.lo ∧
        (initView.getD x.slot DomC.empty).hi? = some x.hi := by
  intro x hx
  unfold allDiffHallItems at hx
  obtain ⟨s, hs, hf⟩ := List.mem_filterMap.mp (List.mem_mergeSort.mp hx)
  have hb := allDiffItemOfDom?_bounds hf
  have hsl : x.slot = s := allDiffItemOfDom?_slot hf
  simpa [hsl] using hb

/-- The outer Hall sweep: membership in the accumulated array of a
`goA` run. -/
theorem sweepGoA_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (hndItems : (items.map AllDiffItem.slot).Nodup)
    (hsorted : List.Pairwise (fun x y => x.hi ≤ y.hi) items)
    (view : EngineView)
    (hItemsBound : ∀ x ∈ items,
      (view.doms.getD x.slot DomC.empty).lo? = some x.lo ∧
        (view.doms.getD x.slot DomC.empty).hi? = some x.hi)
    (a : Int) :
    ∀ (lowers : List Int) (acc : Array (PLit × EClause p T)) {q},
      (allDiffHallSweep.goA p T init is hinit hmem hint items hitems hndItems
        lowers none acc).1 = none →
      q ∈ (allDiffHallSweep.goA p T init is hinit hmem hint items hitems hndItems
        lowers none acc).2.toList →
      q ∈ acc.toList ∨
        ∃ (S : List Nat) (a b : Int) (hSsub : ∀ s ∈ S, s ∈ is) (hSnd : S.Nodup),
          (∀ s ∈ S, ∃ lo hi,
            (view.doms.getD s DomC.empty).lo? = some lo ∧
              (view.doms.getD s DomC.empty).hi? = some hi ∧ a ≤ lo ∧ hi ≤ b) ∧
          ∃ hlen : S.length = (b - a + 1).toNat,
            q ∈ (allDiffHallPrunesFor p T init is hinit hmem hint items hitems
              S a b hSsub hSnd hlen).toList := by
  intro lowers
  induction lowers with
  | nil =>
      intro acc q hconf hq
      rw [allDiffHallSweep.goA.eq_1] at hq
      exact Or.inl hq
  | cons a' as' ih =>
      intro acc q hconf hq
      rw [allDiffHallSweep.goA.eq_3] at hconf hq
      cases hgo : allDiffHallSweep.goA.go p T init is hinit hmem hint items hitems
          hndItems a' (items.filter (fun x => decide (a' ≤ x.lo))) (fun _ h => h)
          0 (by simp) none acc with
      | mk c acc' =>
          rw [hgo] at hconf hq
          cases c with
          | some ec => simp at hconf
          | none =>
              have hres := ih acc' (q := q) hconf hq
              rcases hres with hacc' | hblk
              · have hacc'' : q ∈ (allDiffHallSweep.goA.go p T init is hinit hmem hint items hitems
                    hndItems a' (items.filter (fun x => decide (a' ≤ x.lo))) (fun _ h => h)
                    0 (by simp) none acc).2.toList := by
                  simpa [hgo] using hacc'
                rcases sweepGo_block p T init is hinit hmem hint items hitems hndItems
                    hsorted view hItemsBound a' (items.filter (fun x => decide (a' ≤ x.lo)))
                    (fun _ h => h) 0 (by simp) acc rfl (q := q) (by rw [hgo]) hacc'' with
                  hleft | ⟨S, b0, b, hSsub, hSnd, hbound, hlen, hmem⟩
                · exact Or.inl hleft
                · exact Or.inr ⟨S, b0, b, hSsub, hSnd, hbound, hlen, hmem⟩
              · exact Or.inr hblk

/-- Every prune of the full Hall sweep is a block prune. -/
theorem allDiffHallSweep_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (hndItems : (items.map AllDiffItem.slot).Nodup)
    (hsorted : List.Pairwise (fun x y => x.hi ≤ y.hi) items)
    (view : EngineView)
    (hItemsBound : ∀ x ∈ items,
      (view.doms.getD x.slot DomC.empty).lo? = some x.lo ∧
        (view.doms.getD x.slot DomC.empty).hi? = some x.hi)
    {q : PLit × EClause p T}
    (hconf : (allDiffHallSweep p T init is hinit hmem hint items hitems hndItems).1 = none)
    (hq : q ∈ (allDiffHallSweep p T init is hinit hmem hint items hitems hndItems).2.toList) :
    ∃ (S : List Nat) (a b : Int) (hSsub : ∀ s ∈ S, s ∈ is) (hSnd : S.Nodup),
      (∀ s ∈ S, ∃ lo hi,
        (view.doms.getD s DomC.empty).lo? = some lo ∧
          (view.doms.getD s DomC.empty).hi? = some hi ∧ a ≤ lo ∧ hi ≤ b) ∧
      ∃ hlen : S.length = (b - a + 1).toNat,
        q ∈ (allDiffHallPrunesFor p T init is hinit hmem hint items hitems
          S a b hSsub hSnd hlen).toList := by
  unfold allDiffHallSweep at hconf hq
  rcases sweepGoA_mem p T init is hinit hmem hint items hitems hndItems hsorted
      view hItemsBound 0 (allDiffHallLowers items) #[] (q := q) hconf hq with
    h0 | ⟨S, a, b, hSsub, hSnd, hbound, hlen, hmem⟩
  · simp at h0
  · exact ⟨S, a, b, hSsub, hSnd, hbound, hlen, hmem⟩


/-! ## Dedup-fold membership -/

theorem mem_dedupFold {α : Type} (eq : α → α → Bool) :
    ∀ (l : List α) (acc : Array α) {q},
      q ∈ (l.foldl (fun acc pe =>
        if acc.any (fun x => eq x pe) then acc else acc.push pe) acc).toList →
      q ∈ acc.toList ∨ q ∈ l := by
  intro l
  induction l with
  | nil =>
      intro acc q h
      exact Or.inl (by simpa using h)
  | cons a as ih =>
      intro acc q h
      rw [List.foldl_cons] at h
      by_cases hany : acc.any (fun x => eq x a) = true
      · simp only [if_pos hany] at h
        rcases ih acc h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem a h1)
      · simp only [if_neg hany] at h
        rcases ih (acc.push a) h with h1 | h1
        · rw [Array.mem_toList_iff, Array.mem_push] at h1
          rcases h1 with h1 | h1
          · exact Or.inl (Array.mem_toList_iff.mpr h1)
          · exact Or.inr (by rw [h1]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem a h1)

/-- The `all_different` propagator's pruning contract. -/
theorem allDiffPropWith_pruneSound (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints) :
    (allDiffPropWith p T init is hinit hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWF' : ViewWF view is.toArray := by
    simpa [allDiffPropWith] using hWF
  unfold allDiffPropWith at hrun
  by_cases hdup : is.Nodup
  · simp only [dif_pos hdup] at hrun
    split at hrun
    · cases hrun
    · rename_i hfind
      by_cases hkind : is.all (fun s => (init.getD s DomC.empty).intKindB) = true
      · simp only [dif_pos hkind] at hrun
        split at hrun
        · cases hrun
        · rename_i hhall
          split at hrun
          · cases hrun
          · cases hrun
            rw [← Array.foldl_toList] at hq
            have hmemdedup := mem_dedupFold
              (fun a b : PLit × EClause p T => a.1 == b.1) _ #[] (q := q) hq
            rcases hmemdedup with h0 | hrest
            · simp at h0
            · rw [mem_toList_append_iff] at hrest
              rcases hrest with hfix | hhallq
              · obtain ⟨a, ha, hgi, hqa⟩ :=
                  allDiffCollectPrunes_mem p T is init hinit hmem
                    (doms := view.doms) (fs := allDiffFixedSlots is view.doms) hfix
                exact allDiffPrunesFor_sound p T is init hinit hmem view hWF' ha hqa
              · obtain ⟨S, a, b, hSsub, hSnd, hbound, hlen, hqa⟩ :=
                  allDiffHallSweep_mem p T init is hinit hmem
                    (fun s hs => List.all_eq_true.mp hkind s hs)
                    (allDiffHallItems is view.doms)
                    (fun _ hx => allDiffItem_slot_mem hx)
                    (allDiffHallItems_slots_nodup hdup)
                    (hallItems_sorted is view.doms) view (hallItems_bound view.doms is)
                    hhall hhallq
                exact allDiffHallPrunesFor_sound p T init is hinit hmem
                  (fun s hs => List.all_eq_true.mp hkind s hs)
                  (items := allDiffHallItems is view.doms)
                  (hitems := fun _ hx => allDiffItem_slot_mem hx)
                  (S := S) (a := a) (b := b) (hSsub := hSsub) (hSnd := hSnd)
                  (hlen := hlen)
                  view hWF' (hallItems_bound view.doms is) hbound hqa
      · simp only [dif_neg hkind] at hrun
        split at hrun
        · cases hrun
        · cases hrun
          obtain ⟨a, ha, hgi, hqa⟩ :=
            allDiffCollectPrunes_mem p T is init hinit hmem
              (doms := view.doms) (fs := allDiffFixedSlots is view.doms) hq
          exact allDiffPrunesFor_sound p T is init hinit hmem view hWF' ha hqa
  · simp only [dif_neg hdup] at hrun
    cases hrun

/-! ## The generic fallback checker -/

/-- The generic checker (`propsOf`'s fallback for unmodelled constraints)
never prunes, hence satisfies the pruning contract. -/
theorem propCheckV2With_pruneSound
    (p : CompiledProblem DomConstraint) (T : LitTable) (dc : DomConstraint)
    (init : Array DomC)
    (hinit : ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : dc ∈ p.constraints) :
    (propCheckV2With p T dc init hinit hmem).PruneSound :=
  PropV2.pruneSound_of_never_prunes (propCheckV2With_never_prunes p T dc init hinit hmem)

end Wrappers

end LeanFzn.Engine

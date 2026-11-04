/-
File: LeanFzn/Engine/Prop.lean

The propagator interface for the array-based engine: the safe `EClause`
constructor for denotation-level clauses, the forced assignment and its
singleton-negation conflict clause, the generic checking propagator
(`propCheckV2With`, used by `propsOf`), and a sound no-op checker kept for
its audited theorems.

The generic checker reads a `DomConstraint`, waits until every slot it
reads is fixed, and reports the clause of singleton negations when the
constraint is false on the forced assignment.  Entailment needs the
kind-homogeneity guard described in the N6 brief: the emitted literals
express *value disequality within a kind*, so a checked slot's forced
value must be a member of the initial converted domain (`init`).  The
runtime gate checks exactly that membership and returns `.fix` when it
fails.

Dependencies:
  - LeanFzn.Engine.Types: `EClause`, `PropV2`, `PropOut`, `Entailed`.
  - LeanFzn.Engine.Lit: `EClause.ofLits`, `pLit`, `decode_pLit`.
  - LeanFzn.Engine.Dom: `DomC.mem_iff`, `allAssigns_fits_dom`.
  - LeanFzn.Engine.DomOps: `DomC.fixedValue_sound`.
  - LeanFzn.Solver.Propagation.Proofs.PropCheck: `dcSlotsFull`,
    `satisfiedB_dcSlotsFull_congr`.

DAG:
  LeanFzn.Engine.{Types,Lit,Dom,DomOps} -> LeanFzn.Engine.Prop
-/
import LeanFzn.Engine.Types
import LeanFzn.Engine.Lit
import LeanFzn.Engine.Dom
import LeanFzn.Engine.Proofs.Dom
import LeanFzn.Solver.Propagation.Proofs.PropCheck

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Literal-denotation clauses -/

/-- Decoding a list of placeholder literals returns the original list. -/
theorem LitTable.decodeClause_map_pLit (T : LitTable) (ls : List Literal) :
    T.decodeClause (ls.toArray.map pLit) = ls := by
  unfold LitTable.decodeClause
  simp only [LitTable.decode, Array.toList_map]
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [pLit, ih]

/-- Build an `EClause` from a list of literal denotations and an
entailment proof.  The packed array uses the placeholder index; the
engine canonicalizes the indices through the live table before storing
the clause. -/
def EClause.ofLiterals (p : CompiledProblem DomConstraint) (T : LitTable)
    (ls : List Literal) (h : Entailed p ls) : EClause p T :=
  EClause.ofLits p T (ls.toArray.map pLit) (by
    rw [LitTable.decodeClause_map_pLit]
    exact h)

/-! ## Forced assignment and conflict literals -/

/-- A full placeholder assignment from the current compact domains.  The
generic checker only reads the slots in `dcSlotsFull`, all of which are
fixed when the checker runs. -/
def assignmentOfDoms (doms : Array DomC) : List Value :=
  doms.toList.map fun d =>
    match d.fixedValue with
    | some v => v
    | none => Value.int 0

/-- The singleton-negation literals of the fixed slots a constraint reads:
`x ≠ v` for an integer singleton, `x = !b` for a Boolean singleton. -/
def singletonNegLits (dc : DomConstraint) (a : List Value) : Array Literal :=
  (dcSlotsFull dc).toArray.filterMap fun s =>
    match (a[s]? : Option Value) with
    | some (Value.int v) => some (posNe s v)
    | some (Value.bool b) => some (posBool s (!b))
    | _ => none

/-! ## Membership and kind lemmas for `DomC.mem` -/

/-- Membership of an integer in a compact domain forces every other
member to be an integer: `DomC.mem` is kind-homogeneous. -/
theorem DomC.mem_int_kind {d : DomC} {x : Int} (h : d.mem (.int x) = true)
    {w : Value} (hw : d.mem w = true) : ∃ y, w = .int y := by
  cases d <;> cases w <;> simp_all [DomC.mem]

/-- Membership of a Boolean in a compact domain forces every other
member to be a Boolean: `DomC.mem` is kind-homogeneous. -/
theorem DomC.mem_bool_kind {d : DomC} {b : Bool} (h : d.mem (.bool b) = true)
    {w : Value} (hw : d.mem w = true) : ∃ c, w = .bool c := by
  cases d <;> cases w <;> simp_all [DomC.mem]

/-- `memIntView` of an integer member is ordinary integer membership
(the domain cannot be Boolean-valued). -/
theorem DomC.memIntView_eq_mem_int {d : DomC} {x : Int}
    (h : d.mem (.int x) = true) : d.memIntView x = true := by
  cases d <;> simp_all [DomC.memIntView, DomC.mem]

/-- The empty compact domain has no fixed value. -/
theorem DomC.fixedValue_empty : (DomC.empty).fixedValue = none := rfl

/-- `DomC.ofDom?` rejects the empty compiled domain. -/
theorem DomC.ofDom?_empty : DomC.ofDom? (Dom.empty : Dom) = none := rfl

/-- The fixed value at an in-range slot is the value picked by
`assignmentOfDoms`. -/
theorem assignmentOfDoms_getElem? {doms : Array DomC} {s : Nat} {v : Value}
    (h : (doms.getD s DomC.empty).fixedValue = some v) :
    (assignmentOfDoms doms)[s]? = some v := by
  have hgetD : doms.getD s DomC.empty = (doms[s]?).getD DomC.empty := by
    rw [Array.getD_eq_getD_getElem?]
  rw [hgetD] at h
  unfold assignmentOfDoms
  rw [List.getElem?_map, Array.getElem?_toList]
  cases hg : doms[s]? with
  | none =>
      rw [hg] at h
      simp only [Option.getD_none] at h
      rw [DomC.fixedValue_empty] at h
      simp at h
  | some d =>
      rw [hg] at h
      simp only [Option.getD_some] at h
      simp [h]

/-- A literal of `singletonNegLits` arisen from an integer fixed value. -/
theorem posNe_mem_singletonNegLits {dc : DomConstraint} {a : List Value} {s : Nat}
    {x : Int} (hs : s ∈ dcSlotsFull dc) (ha : a[s]? = some (.int x)) :
    posNe s x ∈ (singletonNegLits dc a).toList := by
  unfold singletonNegLits
  rw [Array.mem_toList_iff, Array.mem_filterMap]
  exact ⟨s, by simpa using hs, by simp [ha]⟩

/-- A literal of `singletonNegLits` arisen from a Boolean fixed value. -/
theorem posBool_mem_singletonNegLits {dc : DomConstraint} {a : List Value} {s : Nat}
    {b : Bool} (hs : s ∈ dcSlotsFull dc) (ha : a[s]? = some (.bool b)) :
    posBool s (!b) ∈ (singletonNegLits dc a).toList := by
  unfold singletonNegLits
  rw [Array.mem_toList_iff, Array.mem_filterMap]
  exact ⟨s, by simpa using hs, by simp [ha]⟩

/-- Every literal of `singletonNegLits` is either an integer or a Boolean
singleton negation of a slot the constraint reads. -/
theorem mem_singletonNegLits_cases {dc : DomConstraint} {a : List Value} {q : Literal}
    (hq : q ∈ (singletonNegLits dc a).toList) :
    (∃ s ∈ dcSlotsFull dc, ∃ x, a[s]? = some (.int x) ∧ q = posNe s x) ∨
      (∃ s ∈ dcSlotsFull dc, ∃ b, a[s]? = some (.bool b) ∧ q = posBool s (!b)) := by
  unfold singletonNegLits at hq
  rw [Array.mem_toList_iff, Array.mem_filterMap] at hq
  obtain ⟨s, hs, hf⟩ := hq
  have hs' : s ∈ dcSlotsFull dc := by simpa using hs
  cases ha : a[s]? with
  | none => simp [ha] at hf
  | some v =>
      cases v with
      | int x => exact Or.inl ⟨s, hs', x, ha, by simpa [ha] using hf.symm⟩
      | bool b => exact Or.inr ⟨s, hs', b, ha, by simpa [ha] using hf.symm⟩
      | setOfInt _ => simp [ha] at hf
      | array _ => simp [ha] at hf

/-- `evalLit` of an integer singleton negation is false on a well-formed
domain whose fixed value is that integer. -/
theorem DomC.evalLit_posNe_of_fixed {d : DomC} {s : Nat} {x : Int}
    (hfv : d.fixedValue = some (.int x)) (hmem : d.mem (.int x) = true) :
    d.evalLit (posNe s x) = some false := by
  have hmiv : d.memIntView x = true := DomC.memIntView_eq_mem_int hmem
  simp [DomC.evalLit, posNe, hfv, hmiv]

/-- `evalLit` of a Boolean complement pin is false on a domain fixed to
the complemented value. -/
theorem DomC.evalLit_posBool_of_fixed {d : DomC} {s : Nat} {b : Bool}
    (hfv : d.fixedValue = some (.bool b)) :
    d.evalLit (posBool s (!b)) = some false := by
  simp only [DomC.evalLit, hfv]
  cases b <;> rfl

/-! ## The checker's semantic contract -/

/-- **Conflict entailment.**  When every checked slot has a fixed value
that is a member of the initial converted domain and the constraint is
false on the forced assignment `a`, the emitted singleton-negation
clause is entailed by the problem.  The initial-domain guard is what
makes the integer/Boolean literals exact across kinds. -/
theorem propCheckV2With_conflict_entailed
    (p : CompiledProblem DomConstraint) (dc : DomConstraint) (init : Array DomC)
    (hinit : ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (a : List Value) (view : EngineView) (hmem : dc ∈ p.constraints)
    (_hfixed : ∀ s ∈ dcSlotsFull dc,
      (view.doms.getD s DomC.empty).isFixed = true)
    (hguard : ∀ s ∈ dcSlotsFull dc, ∃ v,
      (view.doms.getD s DomC.empty).fixedValue = some v ∧
        (init.getD s DomC.empty).mem v = true)
    (ha : ∀ s ∈ dcSlotsFull dc,
      a[s]? = (view.doms.getD s DomC.empty).fixedValue)
    (hunsat : dc.satisfiedB a = false) :
    Entailed p (singletonNegLits dc a).toList := by
  intro b hb hacc
  have hfit := allAssigns_fits_dom p.domains b hb
  have hdcb : dc.satisfiedB b = true := List.all_eq_true.mp hacc dc hmem
  refine Classical.byContradiction ?_
  intro hno
  have hagree : ∀ s ∈ dcSlotsFull dc, b[s]? = a[s]? := by
    intro s hs
    obtain ⟨v, hfv, hmv⟩ := hguard s hs
    have haa : a[s]? = some v := by rw [ha s hs, hfv]
    have hlen : s < p.domains.length := by
      rcases Nat.lt_or_ge s p.domains.length with hlt | hge
      · exact hlt
      · exfalso
        have hnone : p.domains.getD s Dom.empty = Dom.empty := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hge]
          rfl
        have hcontra := hinit s hs
        rw [hnone, DomC.ofDom?_empty] at hcontra
        simp at hcontra
    have hblen : s < b.length := by rw [hfit.1]; exact hlen
    have hbget : b[s]? = some b[s] := List.getElem?_eq_getElem hblen
    have hbmem : b[s] ∈ p.domains.getD s Dom.empty := hfit.2 s b[s] hbget
    have hbinit : (init.getD s DomC.empty).mem b[s] = true :=
      (DomC.mem_iff _ _ (hinit s hs) b[s]).mpr hbmem
    cases v with
    | int x =>
        have hlit : posNe s x ∈ (singletonNegLits dc a).toList :=
          posNe_mem_singletonNegLits hs (by rw [haa])
        have hnot : (posNe s x).eval b ≠ some true :=
          fun htrue => hno ⟨posNe s x, hlit, htrue⟩
        obtain ⟨y, hby⟩ := DomC.mem_int_kind (x := x) hmv hbinit
        have hyx : y = x := by
          apply Classical.byContradiction
          intro hyx
          apply hnot
          exact (eval_posNe_iff b s x).mpr
            ⟨y, by simp [slotInt, hbget, hby, Value.intView], hyx⟩
        rw [hbget, hby, hyx, haa]
    | bool bb =>
        have hlit : posBool s (!bb) ∈ (singletonNegLits dc a).toList :=
          posBool_mem_singletonNegLits hs (by rw [haa])
        have hnot : (posBool s (!bb)).eval b ≠ some true :=
          fun htrue => hno ⟨posBool s (!bb), hlit, htrue⟩
        obtain ⟨c, hbc⟩ := DomC.mem_bool_kind (b := bb) hmv hbinit
        have hcb : c = bb := by
          have hne : c ≠ !bb := by
            intro hceq
            apply hnot
            exact (eval_posBool_iff b s (!bb)).mpr (by rw [hbget, hbc, hceq])
          cases c <;> cases bb <;> simp_all
        rw [hbget, hbc, hcb, haa]
    | setOfInt _ => simp [DomC.mem] at hmv
    | array _ => simp [DomC.mem] at hmv
  have hcong := satisfiedB_dcSlotsFull_congr dc hagree
  rw [hdcb, hunsat] at hcong
  simp at hcong

/-- **Conflict literals are false.**  Under the same guard and with
well-formed current domains, every literal of the emitted clause is
falsified by the corresponding current domain.  This is N8's analysis
contract.  (`DomC.WF` is needed: `isFixed` only tests the size, and a
malformed `boundsHoles` can report a fixed value that is not a member.) -/
theorem propCheckV2With_conflict_lits_false
    (p : CompiledProblem DomConstraint) (dc : DomConstraint) (init : Array DomC)
    (_hinit : ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (a : List Value) (view : EngineView)
    (hWF : ∀ s ∈ dcSlotsFull dc, (view.doms.getD s DomC.empty).WF)
    (hguard : ∀ s ∈ dcSlotsFull dc, ∃ v,
      (view.doms.getD s DomC.empty).fixedValue = some v ∧
        (init.getD s DomC.empty).mem v = true)
    (ha : ∀ s ∈ dcSlotsFull dc,
      a[s]? = (view.doms.getD s DomC.empty).fixedValue) :
    ∀ q ∈ (singletonNegLits dc a).toList,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  intro q hq
  rcases mem_singletonNegLits_cases hq with
    ⟨s, hs, x, hax, rfl⟩ | ⟨s, hs, b, hab, rfl⟩
  · obtain ⟨v, hfv, -⟩ := hguard s hs
    have hav : a[s]? = some v := by rw [ha s hs, hfv]
    have hv : v = Value.int x := by
      have hsome : some (Value.int x) = some v := hax.symm.trans hav
      exact (Option.some.inj hsome).symm
    rw [hv] at hfv
    have hmem := (DomC.fixedValue_sound _ (hWF s hs) hfv).1
    exact DomC.evalLit_posNe_of_fixed hfv hmem
  · obtain ⟨v, hfv, -⟩ := hguard s hs
    have hav : a[s]? = some v := by rw [ha s hs, hfv]
    have hv : v = Value.bool b := by
      have hsome : some (Value.bool b) = some v := hab.symm.trans hav
      exact (Option.some.inj hsome).symm
    rw [hv] at hfv
    exact DomC.evalLit_posBool_of_fixed hfv

/-! ## The generic checker -/

/-- The generic checker `PropV2` for one `DomConstraint`, with the
initial converted domains supplied for the kind-homogeneity guard.

`run` first requires every checked slot to be fixed; it then requires
each checked slot's fixed value to be a member of `init` (the guard
discharging the entailment argument of
`propCheckV2With_conflict_entailed`); finally it tests `satisfiedB` on
the forced assignment and reports the singleton-negation conflict clause
when it is false.  If the constraint is not a member of the problem, the
checker performs no propagation (this is unreachable for the propagators
`propsOf` registers, and keeps the function sound for an arbitrary input). -/
def propCheckV2With (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (init : Array DomC)
    (hinit : ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : dc ∈ p.constraints) :
    PropV2 p T :=
  let slots := (dcSlotsFull dc).toArray
  { vars := slots
    events := slots.map fun s => (s, .fix)
    run := fun view =>
      if hfixed : slots.all (fun s => (view.doms.getD s DomC.empty).isFixed) then
        let a := assignmentOfDoms view.doms
        if hguard : slots.all (fun s =>
            match (view.doms.getD s DomC.empty).fixedValue with
            | some v => (init.getD s DomC.empty).mem v
            | none => false) then
          if hsat : dc.satisfiedB a = true then .fix
          else
            let ls := singletonNegLits dc a
            .conflict (EClause.ofLiterals p T ls.toList (by
              apply propCheckV2With_conflict_entailed p dc init hinit a view hmem
              · intro s hs
                exact Array.all_eq_true'.mp hfixed s (List.mem_toArray.mpr hs)
              · intro s hs
                have hg := Array.all_eq_true'.mp hguard s (List.mem_toArray.mpr hs)
                split at hg
                · rename_i v hv
                  exact ⟨v, hv, hg⟩
                · simp at hg
              · intro s hs
                have hg := Array.all_eq_true'.mp hguard s (List.mem_toArray.mpr hs)
                split at hg
                · rename_i v hv
                  rw [hv]
                  exact assignmentOfDoms_getElem? hv
                · simp at hg
              · cases hb : dc.satisfiedB a <;> simp_all))
        else .fix
      else .fix }

/-- A sound `.fix` no-op checker (`propCheckV2_noop` is audited);
`propsOf` uses `propCheckV2With`. -/
def propCheckV2 (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) : PropV2 p T :=
  let slots := (dcSlotsFull dc).toArray
  { vars := slots
    events := slots.map fun s => (s, .fix)
    run := fun _ => .fix }

/-- The generic checker never prunes. -/
theorem propCheckV2With_never_prunes
    (p : CompiledProblem DomConstraint) (T : LitTable) (dc : DomConstraint)
    (init : Array DomC)
    (hinit : ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : dc ∈ p.constraints)
    (view : EngineView) (ps : Array (PLit × EClause p T)) :
    (propCheckV2With p T dc init hinit hmem).run view ≠ .prune ps := by
  unfold propCheckV2With
  dsimp only
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- The transitional checker always returns `.fix`. -/
theorem propCheckV2_noop (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (view : EngineView) :
    (propCheckV2 p T dc).run view = .fix := rfl

end LeanFzn.Engine

/-
File: LeanFzn.Engine.Proofs.Queue.Root

R1: root-entailment invariants.

Every trail entry pushed at decision level zero is a unit consequence of the
compiled problem.  Together with the slot-history replay, this gives domain
containment at the root (`RootDomInv`): every accepted assignment's value is
still present in every live root domain.  A literal that is definitely false
on a root domain is therefore never true on an accepted assignment, and (in
range) its negation is entailed.  R2 consumes the latter fact to delete
level-zero items from a learned clause.

The invariants are proof-only; no runtime field or counter is touched.

Dependencies: `Engine.Analyze` (items and the initial-domain bridge),
`Engine.Proofs.PruneSound` (propagator contracts) and the queue history
lemmas (`domAfter`).
DAG: Engine.Analyze + Engine.Proofs.PruneSound
     + Engine.Proofs.Queue.Bookkeeping -> Engine.Proofs.Queue.Root -> Engine.Search
-/
import LeanFzn.Engine.Analyze
import LeanFzn.Engine.Proofs.PruneSound
import LeanFzn.Engine.Proofs.Queue.Bookkeeping

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

set_option maxHeartbeats 4000000

/-! ## Root-domain replay -/

/-- Replaying the full change list at the root never loses the value of an
accepted root assignment.  At level zero `TrailInv` bounds every entry's
level by zero, so the prefix hypothesis of `domAfter_mem_of_prefix` holds. -/
theorem domAfter_mem_of_root {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T}
    (hTI : TrailInv st) (hlev : st.level = 0)
    (hroot : RootTrail p T st) (hconv : InitConv p init)
    {b : Assignment} (hb : b ∈ allAssigns p.domains) (hacc : accepts p b = true)
    {s : Nat} (hsl : s < p.domains.length) :
    ∀ {m : Nat}, m ≤ (st.changeList s).size → ∀ {v : Value},
      b[s]? = some v → (domAfter init st s m).mem v = true := by
  intro m hm v hbv
  exact domAfter_mem_of_prefix hTI hroot hconv hb hacc hsl hm
    (fun _ _ e he => by
      have hle := hTI.entry_level_le he
      omega) hbv

/-- Domain containment at the root follows from the replay at the full
change-list length. -/
theorem rootDomInv_of_level0 {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T}
    (hhist : SlotHistory init st) (hTI : TrailInv st) (hlev : st.level = 0)
    (hroot : RootTrail p T st) (hconv : InitConv p init) :
    RootDomInv p init st := by
  intro _ b hb hacc s hsl v hbv
  rw [hhist.doms_eq s]
  exact domAfter_mem_of_root hTI hlev hroot hconv hb hacc hsl
    (Nat.le_refl _) hbv

/-- Transport `LevelMono` along an unchanged trail. -/
theorem levelMono_of_trail {st st' : EngineState p T} (h : LevelMono st)
    (htr : st'.trail = st.trail) : LevelMono st' := by
  intro i j e1 e2 hi hj hij
  rw [htr] at hi hj
  exact h i j e1 e2 hi hj hij

/-- A trail prefix keeps level monotonicity. -/
theorem levelMono_extract (st : EngineState p T) (h : LevelMono st) (lim : Nat) :
    LevelMono { st with trail := st.trail.extract 0 lim } := by
  intro i j e1 e2 hi hj hij
  rw [Array.getElem?_extract] at hi hj
  split at hi
  · rename_i hi'
    split at hj
    · rename_i hj'
      exact h i j e1 e2 (by simpa using hi) (by simpa using hj) hij
    · cases hj
  · cases hi

/-- Pushing an entry whose level is at least every existing level keeps the
trail level-monotone. -/
theorem levelMono_trailPush {st : EngineState p T} {e : Entry} (h : LevelMono st)
    (helev : e.level = st.level)
    (hle : ∀ (i : Nat) (e' : Entry), st.trail[i]? = some e' → e'.level ≤ st.level) :
    LevelMono (trailPush st e) := by
  intro i j e1 e2 hi hj hij
  by_cases hjsz : j < st.trail.size
  · have hisz : i < st.trail.size := by omega
    rw [trailPush_trail_old st e hisz] at hi
    rw [trailPush_trail_old st e hjsz] at hj
    exact h i j e1 e2 hi hj hij
  · have hjeq : j = st.trail.size := by
      have hlt := (Array.getElem?_eq_some_iff.mp hj).1
      rw [trailPush_trail_size] at hlt
      omega
    have hnewj := hj
    rw [hjeq, trailPush_trail_new] at hnewj
    have he2 : e2 = e := (Option.some.inj hnewj).symm
    have hlev : e1.level ≤ e.level := by
      by_cases hisz : i < st.trail.size
      · have ho := trailPush_trail_old st e hisz
        rw [ho] at hi
        have h1 := hle i e1 hi
        omega
      · have hilt := (Array.getElem?_eq_some_iff.mp hi).1
        rw [trailPush_trail_size] at hilt
        have hieq : i = st.trail.size := by omega
        have hnewi := hi
        rw [hieq, trailPush_trail_new] at hnewi
        have he1 : e1 = e := (Option.some.inj hnewi).symm
        rw [he1]
        exact Nat.le_refl _
    rw [he2]
    exact hlev

/-- A backjump keeps level monotonicity: it only truncates the trail. -/
theorem levelMono_backjump {st : EngineState p T} (h : LevelMono st) (k : Nat) :
    LevelMono (backjump st k) := by
  have := levelMono_extract st h (st.backjumpLimit (min k st.level))
  refine levelMono_of_trail this ?_
  exact backjump_trail st k

/-- `undoFuel` touches the domains and change lists, never the trail. -/
theorem levelMono_undoFuel {st : EngineState p T} (h : LevelMono st) (limit f : Nat) :
    LevelMono (undoFuel st limit f) :=
  levelMono_of_trail h (undoFuel_trail st limit f)

/-! ## False root literals -/

/-- A literal that is definitely false on the live root domains is never
true on an accepted assignment.  Out-of-range slots have no value in any
accepted assignment, so they are vacuous here. -/
theorem evalLit_false_notTrue {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {l : Literal}
    (hdom : RootDomInv p init st) (hlev : st.level = 0) (hWF : DomsWF st)
    (hfalse : (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) :
    NotTrueEntailed p l := by
  intro b hb hacc hev
  by_cases hsl : atomSlot l.atom < p.domains.length
  · obtain ⟨v, hbv, _⟩ := mem_allAssigns_getElem_mem hb hsl
    have hmem : (st.doms.getD (atomSlot l.atom) DomC.empty).mem v = true :=
      hdom hlev b hb hacc (atomSlot l.atom) hsl v hbv
    have hdWF : (st.doms.getD (atomSlot l.atom) DomC.empty).WF :=
      dom_WF_of_mem hWF hmem
    have hval : l.valueHolds v = false :=
      DomC.evalLit_false_sound _ l hdWF hfalse v hmem
    rw [Literal.eval_eq_valueHolds l b hbv] at hev
    rw [hev] at hval
    exact Bool.noConfusion hval
  · have hlen : b.length = p.domains.length :=
      allAssigns_length_eq hb
    have hnone : b[atomSlot l.atom]? = none :=
      List.getElem?_eq_none (by omega)
    have hnone_eval : l.eval b = none := by
      cases l with
      | mk atom pos =>
        cases atom with
        | boolEq s expected =>
            have hs : b[s]? = none := by simpa [atomSlot] using hnone
            simp [Literal.eval, Atom.eval, hs]
        | intLe s upper =>
            have hs : b[s]? = none := by simpa [atomSlot] using hnone
            simp [Literal.eval, Atom.eval, slotInt, hs]
        | intNe s value =>
            have hs : b[s]? = none := by simpa [atomSlot] using hnone
            simp [Literal.eval, Atom.eval, slotInt, hs]
    rw [hnone_eval] at hev
    cases hev


/-! ## Derived `RootInv` facts -/

/-- The trail-validity component. -/
theorem RootInv.trail_inv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    TrailInv st :=
  h.hist.2

/-- The table's lookup-cache invariant. -/
theorem RootInv.table_wf {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    st.table.TableWF :=
  h.table_inv.table_wf

/-- The slot-history component. -/
theorem RootInv.slotHistory {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    SlotHistory init st :=
  h.hist.1

/-- Every live domain is well formed. -/
theorem RootInv.domsWF {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    DomsWF st :=
  slotHistory_domsWF h.init_inv h.hist.1

/-- The combined history invariant. -/
theorem RootInv.good {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    Good init st :=
  ⟨h.hist.1, h.hist.2, h.domsWF⟩

/-- Root-domain containment at level zero. -/
theorem RootInv.rootDomInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (hlev : st.level = 0) : RootDomInv p init st :=
  rootDomInv_of_level0 h.hist.1 h.hist.2 hlev h.root h.conv

/-- Transport a root invariant along an unchanged logical state. -/
theorem RootInv.congr {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st st' : EngineState p T} (h : RootInv p T init st)
    (hd : st'.doms = st.doms) (htr : st'.trail = st.trail)
    (hcl : ∀ s, st'.changeList s = st.changeList s)
    (hci : st'.changeIndex = st.changeIndex)
    (hls : st'.levelStart = st.levelStart) (hl : st'.level = st.level)
    (hrc : st'.reasonCap = st.reasonCap) (htab : st'.table = st.table)
    (hdb : st'.db = st.db) : RootInv p T init st' := by
  refine ⟨HistInv.congr h.hist hd htr hcl hci hls hl hrc, h.init_inv, ?_,
    ?_, ?_, ?_, h.conv, ?_⟩
  · rw [htab]; exact h.table_inv
  · rw [htab, hdb]; exact h.lits_wf
  · exact levelMono_of_trail h.level_mono htr
  · intro i e hi h0
    rw [htr] at hi
    exact h.root i e hi h0
  · rw [hdb]; exact h.db_inv

/-! ## False literals in the live domains -/

/-- A packed literal whose `litValueC` is false is not true on any accepted
assignment of a level-zero root state. -/
theorem litValueC_false_notTrue {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (hdom : RootDomInv p init st) (hlev : st.level = 0) (hWF : DomsWF st)
    {r : PLit} (h : litValueC st.doms r = some false) :
    NotTrueEntailed p r.lit := by
  unfold litValueC at h
  cases hd : st.doms[r.slot]? with
  | none => rw [hd] at h; simp at h
  | some d =>
      rw [hd] at h
      have hd' : st.doms[atomSlot r.lit.atom]? = some d := by
        simpa [PLit.slot] using hd
      exact evalLit_false_notTrue hdom hlev hWF (by
        rw [Array.getD_eq_getElem?_getD, hd']
        exact h)

/-- The target of an all-but prune is entailed, given that the propagated
literal is not true and every false literal is not true. -/
theorem ClauseDB.PrunesAllBut.entailed_target
    {p : CompiledProblem DomConstraint} {T : LitTable} {db : ClauseDB p T}
    {doms : Array DomC} {l q : PLit} {id : Nat} {ps : Array (PLit × Nat)}
    (h : db.PrunesAllBut doms l ps) (hmem : (q, id) ∈ ps.toList)
    (hnl : NotTrueEntailed p l.lit)
    (hfalse : ∀ r : PLit,
      (doms.getD r.slot DomC.empty).evalLit r.lit = some false →
      NotTrueEntailed p r.lit) :
    Entailed p [q.lit] := by
  obtain ⟨sc, hget, hdel, hmemlit, hother⟩ := h q id hmem
  refine entailed_unit_of_notTrue sc.e.ent ?_
  intro m hm hmne
  have hm' : ∃ r, r ∈ sc.e.lits ∧ m = r.lit := by
    simpa [LitTable.decodeClause, LitTable.decode, eq_comm] using hm
  obtain ⟨r, hr, rfl⟩ := hm'
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hr
  rcases hother k r hk hmne with heq | hf
  · rw [heq]; exact hnl
  · exact hfalse r hf

/-! ## Generic bridges -/

/-- `atomSlot` and `Atom.slot` are the same function. -/
theorem atomSlot_eq_atom_slot (a : Atom) : atomSlot a = a.slot := by
  cases a <;> rfl

/-- Every well-formed domain array yields a well-formed propagator view on
any list of slots (out-of-range slots read the empty domain). -/
theorem viewWF_of_domsWF {st : EngineState p T} (h : DomsWF st)
    (slots : Array Nat) :
    ViewWF { doms := st.doms, level := st.level } slots := by
  intro i hi
  by_cases hs : slots[i] < st.doms.size
  · exact h slots[i] hs
  · rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_none (Nat.le_of_not_lt hs)]
    exact DomC.empty_WF

/-! ## Appending entries above an existing trail -/

/-- Appending entries all pushed at the current level keeps the trail
level-monotone. -/
theorem levelMono_append {st st' : EngineState p T} (h : LevelMono st)
    (hTI : TrailInv st)
    (hpre : st.trail.toList <+: st'.trail.toList)
    (hnew : ∀ (i : Nat) (e : Entry), st'.trail[i]? = some e →
      st.trail.size ≤ i → e.level = st.level) :
    LevelMono st' := by
  have hget_old : ∀ {i : Nat}, i < st.trail.size → st'.trail[i]? = st.trail[i]? := by
    intro i hi
    obtain ⟨c, hc⟩ := hpre
    rw [← Array.getElem?_toList, ← Array.getElem?_toList, ← hc]
    rw [List.getElem?_append_left (by simpa using hi)]
  intro i j e1 e2 hi hj hij
  by_cases hiold : i < st.trail.size
  · rw [hget_old hiold] at hi
    by_cases hjold : j < st.trail.size
    · rw [hget_old hjold] at hj
      exact h i j e1 e2 hi hj hij
    · have h1 : e1.level ≤ st.level := TrailInv.entry_level_le hTI hi
      have h2 : e2.level = st.level := hnew j e2 hj (by omega)
      omega
  · have hjold : st.trail.size ≤ j := by omega
    have h1 : e1.level = st.level := hnew i e1 hi (by omega)
    have h2 : e2.level = st.level := hnew j e2 hj hjold
    omega

/-! ## Root pending literals -/

/-- Every literal waiting in the pending array is entailed whenever the
engine sits at decision level zero.  This is the producer side of
`RootTrail`: pending literals become level-zero trail entries. -/
def PendingRoot (p : CompiledProblem DomConstraint) (st : EngineState p T)
    (pending : Array Pending) : Prop :=
  st.level = 0 → ∀ item ∈ pending.toList, Entailed p [item.lit.lit]

/-- `PendingRoot` only reads the decision level. -/
theorem PendingRoot.mono {p : CompiledProblem DomConstraint} {T : LitTable}
    {st st' : EngineState p T} {pending : Array Pending}
    (h : PendingRoot p st pending) (hl : st'.level = st.level) :
    PendingRoot p st' pending := by
  intro h0 item hit
  exact h (by omega) item hit

/-- Popping the pending array preserves root entailment. -/
theorem PendingRoot.pop {p : CompiledProblem DomConstraint} {T : LitTable}
    {st st' : EngineState p T} {pending : Array Pending}
    (h : PendingRoot p st pending) (hl : st'.level = st.level) :
    PendingRoot p st' pending.pop := by
  intro h0 item hit
  exact h (by omega) item (by
    rw [Array.toList_pop] at hit
    exact (List.dropLast_sublist _).subset hit)

/-- The shape of the trail after `insertPending`: unchanged, or one push of
an entry carrying the pending literal at the current level. -/
theorem insertPending_trail_cases (st : EngineState p T) (item : Pending) :
    (insertPending st item).1.trail = st.trail ∨
    ∃ e : Entry, (insertPending st item).1.trail = st.trail.push e ∧
      e.level = st.level ∧ e.lit.lit = item.lit.lit ∧
      e.slot = item.lit.lit.atom.slot := by
  unfold insertPending
  dsimp only
  split
  · left; simp [canonLit_trail]
  · split
    · left; simp [canonLit_trail, canonClause_trail]
    · left; simp [canonLit_trail]
  · split
    · split
      · left; simp [canonLit_trail, canonClause_trail]
      · left; simp [canonLit_trail]
    · rename_i hz
      refine Or.inr ⟨{ lit := (canonLit st item.lit).1,
                       level := (canonLit st item.lit).2.level,
                       reason := item.reason,
                       slot := (canonLit st item.lit).1.slot,
                       prev := ((canonLit st item.lit).2.doms.getD
                         (canonLit st item.lit).1.slot DomC.empty) }, ?_, ?_, ?_, ?_⟩
      · simp [trailPush, emitSlot_trail, canonNegLit_trail, canonLit_trail]
      · simp [canonLit_level]
      · simp [canonLit_lit]
      · simpa [PLit.slot, canonLit_lit] using atomSlot_eq_atom_slot item.lit.lit.atom

/-- `insertPending` preserves the root invariant when the inserted pending
literal is entailed at the root. -/
theorem insertPending_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (item : Pending) (hitem : st.level = 0 → Entailed p [item.lit.lit]) :
    RootInv p T init (insertPending st item).1 := by
  refine ⟨insertPending_histInv h.hist item, h.init_inv,
    insertPending_table_inv h.table_inv item, ?_, ?_, ?_, h.conv, ?_⟩
  · rw [insertPending_db]
    exact ClauseDB.LitsWF.mono_table (insertPending_table_append_only item)
      h.lits_wf
  · rcases insertPending_trail_cases st item with htr | ⟨e, htr, hlev, hlit, hslot⟩
    · exact levelMono_of_trail h.level_mono htr
    · exact levelMono_of_trail
        (levelMono_trailPush h.level_mono hlev
          (fun i e' hi => TrailInv.entry_level_le h.hist.2 hi)) htr
  · rcases insertPending_trail_cases st item with htr | ⟨e, htr, hlev, hlit, hslot⟩
    · intro i e' hi h0
      rw [htr] at hi
      exact h.root i e' hi h0
    · intro i e' hi h0
      by_cases hlt : i < st.trail.size
      · rw [htr, Array.getElem?_push] at hi
        rw [if_neg (by omega)] at hi
        exact h.root i e' hi h0
      · have hieq : i = st.trail.size := by
          have hsz := (Array.getElem?_eq_some_iff.mp hi).1
          rw [htr, Array.size_push] at hsz
          omega
        subst hieq
        rw [htr, Array.getElem?_push] at hi
        rw [if_pos rfl] at hi
        have he' : e' = e := (Option.some.inj hi).symm
        subst he'
        refine ⟨?_, ?_⟩
        · rw [hlit]
          exact hitem (by omega)
        · rw [hlit]
          exact hslot
  · rw [insertPending_db]
    exact h.db_inv



/-! ## Root-invariant transport and producer steps -/

/-- Transport `RootInv` across a step that keeps the logical state (`doms`,
`trail`, level and change structure) and only grows the intern table and
replaces the clause database pointwise. -/
theorem RootInv.of_eq {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st st' : EngineState p T} (h : RootInv p T init st)
    (hd : st'.doms = st.doms) (htr : st'.trail = st.trail)
    (hcl : ∀ s, st'.changeList s = st.changeList s)
    (hci : st'.changeIndex = st.changeIndex)
    (hls : st'.levelStart = st.levelStart) (hl : st'.level = st.level)
    (hrc : st'.reasonCap = st.reasonCap)
    (htab : st'.table.Inv) (hlits : st'.db.LitsWF st'.table)
    (hdb : st'.db.Inv) :
    RootInv p T init st' := by
  refine ⟨HistInv.congr h.hist hd htr hcl hci hls hl hrc, h.init_inv, htab,
    hlits, ?_, ?_, h.conv, hdb⟩
  · exact levelMono_of_trail h.level_mono htr
  · intro i e hi h0
    rw [htr] at hi
    exact h.root i e hi h0

/-- Canonicalising one literal preserves `RootInv`. -/
theorem canonLit_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (l : PLit) : RootInv p T init (canonLit st l).2 := by
  refine h.of_eq (canonLit_doms st l) (canonLit_trail st l)
    (fun s => canonLit_changeList st l s) (canonLit_changeIndex st l)
    (canonLit_levelStart st l) (canonLit_level st l) rfl
    (canonLit_table_inv st l h.table_inv) ?_ ?_
  change ClauseDB.LitsWF (canonLit st l).2.table st.db
  exact ClauseDB.LitsWF.mono_table (canonLit_table_append_only st l) h.lits_wf
  rw [canonLit_db]
  exact h.db_inv

/-- Canonicalising a clause preserves `RootInv`. -/
theorem canonClause_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (c : EClause p T) : RootInv p T init (canonClause st c).2 := by
  refine h.of_eq (canonClause_doms st c) (canonClause_trail st c)
    (fun s => canonClause_changeList st c s) (canonClause_changeIndex st c)
    (canonClause_levelStart st c) (canonClause_level st c) rfl
    (canonClause_table_inv st c h.table_inv) ?_ ?_
  change ClauseDB.LitsWF (canonClause st c).2.table st.db
  exact ClauseDB.LitsWF.mono_table (canonClause_table_append_only st c) h.lits_wf
  rw [canonClause_db]
  exact h.db_inv

/-- Appending a reason preserves `RootInv`. -/
theorem reasonsPush_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (c : EClause p T) :
    RootInv p T init { st with reasons := st.reasons.push c } :=
  h.of_eq rfl rfl (fun _ => rfl) rfl rfl rfl rfl h.table_inv h.lits_wf h.db_inv

/-- One `pushPropStep` preserves `RootInv`. -/
theorem pushPropStep_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} {pending : Array Pending}
    {failed : Bool} (pe : PLit × EClause p T) (h : RootInv p T init st)
    (hf : failed = false) :
    RootInv p T init (pushPropStep (st, pending, failed) pe).1 := by
  unfold pushPropStep
  dsimp only
  simp only [hf, Bool.false_eq_true, if_false]
  exact reasonsPush_rootInv
    (canonClause_rootInv (canonLit_rootInv h pe.1) pe.2) _

/-- `pushPropPrunes` only grows the intern table and the reason store, so it
preserves `RootInv`. -/
theorem pushPropPrunes_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (pending : Array Pending) (ps : Array (PLit × EClause p T)) :
    RootInv p T init (pushPropPrunes st pending ps).1 := by
  rw [pushPropPrunes_eq, ← Array.foldl_toList]
  suffices H : ∀ (l : List (PLit × EClause p T)) (st : EngineState p T)
      (pending : Array Pending), RootInv p T init st →
      RootInv p T init (l.foldl pushPropStep (st, pending, false)).1 from
    H _ st pending h
  intro l
  induction l with
  | nil => intro st pending h; exact h
  | cons pe rest ih =>
      intro st pending h
      rw [List.foldl_cons]
      exact ih _ _ (pushPropStep_rootInv (pending := pending) pe h rfl)

/-- Propagation only replaces the clause database with a pointwise equal one,
so it preserves `RootInv`. -/
theorem propagateLiteral_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (nl : PLit) :
    RootInv p T init { st with db := (st.db.propagateLiteral p T st.doms nl).1 } := by
  refine h.of_eq rfl rfl (fun _ => rfl) rfl rfl rfl rfl h.table_inv ?_ ?_
  · simpa using ClauseDB.LitsWF.of_map_e h.lits_wf
      (fun id => ClauseDB.propagateLiteral_clauses_e st.db st.doms nl id)
  · exact ClauseDB.propagateLiteral_inv st.db st.doms nl h.db_inv


/-- A literal false on the live root domains is not true on any accepted
assignment. -/
theorem evalLit_getD_false_notTrue {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (h : RootInv p T init st) (hlev : st.level = 0) {r : PLit}
    (hf : (st.doms.getD r.slot DomC.empty).evalLit r.lit = some false) :
    NotTrueEntailed p r.lit :=
  evalLit_false_notTrue (h.rootDomInv hlev) hlev h.domsWF (by
    simpa [PLit.slot] using hf)

/-- A step of `pushPropStep` keeps the decision level. -/
theorem pushPropStep_level {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} {pending : Array Pending} {failed : Bool}
    (pe : PLit × EClause p T) :
    (pushPropStep (st, pending, failed) pe).1.level = st.level := by
  unfold pushPropStep
  dsimp only
  split
  · rfl
  · simp [canonClause_level, canonLit_level]

/-- A step of `pushPropStep` keeps the propagator table. -/
theorem pushPropStep_props {p : CompiledProblem DomConstraint} {T : LitTable}
    {st : EngineState p T} {pending : Array Pending} {failed : Bool}
    (pe : PLit × EClause p T) :
    (pushPropStep (st, pending, failed) pe).1.props = st.props := by
  unfold pushPropStep
  dsimp only
  split
  · rfl
  · simp [canonClause_props, canonLit_props]

/-- Clause prunes carry entailed literals at the root. -/
theorem pushClausePrunes_pendingRoot {p : CompiledProblem DomConstraint}
    {T : LitTable} {st : EngineState p T} {pending : Array Pending}
    (h : PendingRoot p st pending) {l : PLit} {ps : Array (PLit × Nat)}
    (hpr : st.db.PrunesAllBut st.doms l ps)
    (hnl : st.level = 0 → NotTrueEntailed p l.lit)
    (hfalse : st.level = 0 → ∀ r : PLit,
      (st.doms.getD r.slot DomC.empty).evalLit r.lit = some false →
      NotTrueEntailed p r.lit) :
    PendingRoot p st (pushClausePrunes pending ps) := by
  intro h0 item hit
  rcases pushClausePrunes_mem pending ps hit with hin | ⟨q, id, hq, rfl⟩
  · exact h h0 item hin
  · exact hpr.entailed_target hq (hnl h0) (hfalse h0)

/-- Unit-clause prunes carry entailed literals at the root. -/
theorem pushClausePrunes_pendingRoot_of_entailed {p : CompiledProblem DomConstraint}
    {T : LitTable} {st : EngineState p T} {pending : Array Pending}
    (h : PendingRoot p st pending) {ps : Array (PLit × Nat)}
    (hent : st.level = 0 → ∀ (q : PLit) (id : Nat),
      (q, id) ∈ ps.toList → Entailed p [q.lit]) :
    PendingRoot p st (pushClausePrunes pending ps) := by
  intro h0 item hit
  rcases pushClausePrunes_mem pending ps hit with hin | ⟨q, id, hq, rfl⟩
  · exact h h0 item hin
  · exact hent h0 q id hq

/-- Developing one propagator prune preserves root entailment of the pending
literals, provided the prune's target is entailed at the root. -/
theorem pushPropStep_pendingRoot {p : CompiledProblem DomConstraint}
    {T : LitTable} {st : EngineState p T} {pending : Array Pending}
    {failed : Bool} (pe : PLit × EClause p T) (h : PendingRoot p st pending)
    (hf : failed = false) (hent : st.level = 0 → Entailed p [pe.1.lit]) :
    PendingRoot p (pushPropStep (st, pending, failed) pe).1
      (pushPropStep (st, pending, failed) pe).2.1 := by
  unfold pushPropStep
  dsimp only
  simp only [hf, Bool.false_eq_true, if_false]
  intro h0 item hit
  rw [Array.toList_push, List.mem_append] at hit
  rcases hit with hit | hit
  · exact h (by simpa [canonClause_level, canonLit_level] using h0) item hit
  · simp only [List.mem_singleton] at hit
    subst hit
    have h0' : st.level = 0 := by
      simpa [canonClause_level, canonLit_level] using h0
    simpa [canonLit_lit] using hent h0'

/-- A whole batch of propagator prunes preserves root entailment of pending
literals. -/
theorem pushPropPrunes_pendingRoot {p : CompiledProblem DomConstraint}
    {T : LitTable} {st : EngineState p T} {pending : Array Pending}
    (h : PendingRoot p st pending) (ps : Array (PLit × EClause p T))
    (hent : st.level = 0 → ∀ pe ∈ ps.toList, Entailed p [pe.1.lit]) :
    PendingRoot p (pushPropPrunes st pending ps).1
      (pushPropPrunes st pending ps).2.1 := by
  rw [pushPropPrunes_eq, ← Array.foldl_toList]
  suffices H : ∀ (l : List (PLit × EClause p T)) (st : EngineState p T)
      (pending : Array Pending), PendingRoot p st pending →
      (st.level = 0 → ∀ pe ∈ l, Entailed p [pe.1.lit]) →
      PendingRoot p (l.foldl pushPropStep (st, pending, false)).1
        (l.foldl pushPropStep (st, pending, false)).2.1 from
    H ps.toList st pending h hent
  intro l
  induction l with
  | nil => intro st pending hp he; simpa using hp
  | cons pe rest ih =>
      intro st pending hp he
      rw [List.foldl_cons]
      have hstep : PendingRoot p (pushPropStep (st, pending, false) pe).1
          (pushPropStep (st, pending, false) pe).2.1 :=
        pushPropStep_pendingRoot (pending := pending) pe hp rfl
          (fun h0 => he h0 pe List.mem_cons_self)
      have hlev : (pushPropStep (st, pending, false) pe).1.level = st.level :=
        pushPropStep_level (pending := pending) pe
      have he' : (pushPropStep (st, pending, false) pe).1.level = 0 →
          ∀ pe' ∈ rest, Entailed p [pe'.1.lit] := by
        intro h0 pe' hmem
        exact he (by rwa [hlev] at h0) pe' (List.mem_cons_of_mem _ hmem)
      exact ih _ _ hstep he'


/-! ## Transport helpers for the drain induction -/

/-- An entailed unit makes its negation not true. -/
theorem notTrueEntailed_neg_of_entailed {p : CompiledProblem DomConstraint}
    {l : Literal} (h : Entailed p [l]) : NotTrueEntailed p l.negate := by
  intro b hb hacc hev
  obtain ⟨x, hx, hxv⟩ := h b hb hacc
  simp only [List.mem_singleton] at hx
  subst hx
  rw [Literal.eval_negate] at hev
  rw [hxv] at hev
  simp at hev

/-- Transport `PropsSound` across an equality of the propagation tables. -/
theorem PropsSound.congr {p : CompiledProblem DomConstraint} {T : LitTable}
    {props props' : Array (PropV2 p T)} (h : PropsSound p T props)
    (he : props' = props) : PropsSound p T props' := by
  intro id pr hid
  exact h id pr (by rwa [he] at hid)

/-- A literal false on the live root domains is not true on any accepted
assignment. -/
theorem RootInv.evalLit_false_notTrue_lit {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    (h : RootInv p T init st) (hlev : st.level = 0) {l : Literal}
    (hf : (st.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) :
    NotTrueEntailed p l :=
  evalLit_false_notTrue (h.rootDomInv hlev) hlev h.domsWF hf

/-- A propagator prune names an entailed literal at the root. -/
theorem PropV2.PruneSound.entailed_target {p : CompiledProblem DomConstraint}
    {T : LitTable} {init : Array DomC} {st : EngineState p T}
    {pr : PropV2 p T} (hsound : pr.PruneSound)
    (hWF : ViewWF { doms := st.doms, level := st.level } pr.vars)
    (hinv : RootInv p T init st) (hlev : st.level = 0)
    {ps : Array (PLit × EClause p T)}
    (hrun : pr.run { doms := st.doms, level := st.level } = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p [q.1.lit] := by
  obtain ⟨-, hfalse⟩ := hsound _ ps hWF hrun q hq
  refine entailed_unit_of_notTrue q.2.ent ?_
  intro m hm hmne
  exact hinv.evalLit_false_notTrue_lit hlev (hfalse m hm hmne)

/-- A queue-pop step keeps the root invariant. -/
theorem RootInv.queueHighPop {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init { st with queueHigh := st.queueHigh.pop } :=
  h.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl

/-- A low-queue-pop step keeps the root invariant. -/
theorem RootInv.queueLowPop {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init { st with queueLow := st.queueLow.pop } :=
  h.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl

/-- Clearing a worklist flag keeps the root invariant. -/
theorem RootInv.setInQueue {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    (id : Nat) (v : UInt8) :
    RootInv p T init (setInQueue st id v) := by
  refine h.congr (setInQueue_doms st id v) (setInQueue_trail st id v) ?_
    (setInQueue_changeIndex st id v) (setInQueue_levelStart st id v)
    (setInQueue_level st id v) (setInQueue_reasonCap st id v)
    (setInQueue_table st id v) (setInQueue_db st id v)
  intro s
  simp [EngineState.changeList, setInQueue_changeIndex]

/-- `drain` preserves the root invariant and every level-zero pending
literal's entailment. -/
theorem drain_rootInv {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} (st0 : EngineState p T) (pending0 : Array Pending)
    (f : Nat) (hinv : RootInv p T init st0)
    (hpending : PendingRoot p st0 pending0)
    (hsound : PropsSound p T st0.props) :
    RootInv p T init (drain p T st0 pending0 f).st := by
  revert hinv hpending hsound
  induction st0, pending0, f using drain.induct with
  | case1 st pending =>
      intro hinv hpending hsound
      simpa [drain] using hinv
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      simpa [drain, hback, hins] using h1
  | case3 st pending f item hback st1 neg hins =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      simpa [drain, hback, hins] using h1
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      have hlev1 : st1.level = st.level := by
        simpa [hins] using insertPending_level (p := p) (T := T) (st := st) item
      have hp1 : PendingRoot p st1 pending1 := by
        simpa [pending1] using hpending.pop (st' := st1) hlev1
      have hs1 : PropsSound p T st1.props :=
        hsound.congr (by simpa [hins] using insertPending_props (st := st) item)
      simpa [drain, hback, hins, hf, pending1] using ih h1 hp1 hs1
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      have hlev1 : st1.level = st.level := by
        simpa [hins] using insertPending_level (p := p) (T := T) (st := st) item
      have hp1 : PendingRoot p st1 pending1 := by
        simpa [pending1] using hpending.pop (st' := st1) hlev1
      have hs1 : PropsSound p T st1.props :=
        hsound.congr (by simpa [hins] using insertPending_props (st := st) item)
      have h2 : RootInv p T init { st1 with db := db } := by
        simpa [hprop] using propagateLiteral_rootInv h1 nl
      have hp2 : PendingRoot p { st1 with db := db } pending1 := hp1.mono rfl
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2 hp2 hs1
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      have h2 : RootInv p T init { st1 with db := db } := by
        simpa [hprop] using propagateLiteral_rootInv h1 nl
      have h3 : RootInv p T init st3 := by
        simpa [hcanon, st2] using canonClause_rootInv h2 ec
      simpa [drain, hback, hins, hprop, hcanon, hf, st2] using h3
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro hinv hpending hsound
      have hmem : item ∈ pending.toList :=
        (Array.mem_toList_iff).mpr (Array.mem_of_back? hback)
      have h1 : RootInv p T init st1 := by
        simpa [hins] using
          insertPending_rootInv hinv item (fun h0 => hpending h0 item hmem)
      have hlev1 : st1.level = st.level := by
        simpa [hins] using insertPending_level (p := p) (T := T) (st := st) item
      have hp1 : PendingRoot p st1 pending1 := by
        simpa [pending1] using hpending.pop (st' := st1) hlev1
      have hs1 : PropsSound p T st1.props :=
        hsound.congr (by simpa [hins] using insertPending_props (st := st) item)
      have h2 : RootInv p T init st2 := by
        simpa [hprop, st2] using propagateLiteral_rootInv h1 nl
      have hwf : st1.table.WF nl := insertPending_neg_wf hinv.table_inv item hins
      have hprop2 : (st1.db.propagateLiteral p T st1.doms nl).2 = .prune ps := by
        rw [hprop]
      have hpr : st1.db.PrunesAllBut st1.doms nl ps :=
        ClauseDB.propagateLiteral_prunesAllBut st1.db st1.doms nl st1.table
          h1.lits_wf hwf h1.db_inv hprop2
      have hnl : st1.level = 0 → NotTrueEntailed p nl.lit := by
        intro h0
        have hst0 : st.level = 0 := by rwa [hlev1] at h0
        have hent : Entailed p [item.lit.lit] := hpending hst0 item hmem
        have hneg : NotTrueEntailed p (item.lit.lit).negate :=
          notTrueEntailed_neg_of_entailed hent
        simpa [insertPending_neg_lit item hins] using hneg
      have hfalse : st1.level = 0 → ∀ r : PLit,
          (st1.doms.getD r.slot DomC.empty).evalLit r.lit = some false →
          NotTrueEntailed p r.lit := by
        intro h0 r hf
        exact h1.evalLit_false_notTrue_lit h0 hf
      have hstep1 : PendingRoot p st1 (pushClausePrunes pending1 ps) :=
        pushClausePrunes_pendingRoot (st := st1) hp1 hpr hnl hfalse
      have hstep : PendingRoot p st2 (pushClausePrunes pending1 ps) :=
        hstep1.mono (by simp [st2])
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2 hstep hs1
  | case8 st pending f hback hq id st1 hprops ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueHighPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hprops, st1, id] using ih h1 hp1 hs1
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueHighPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hprops, hrun, st1, id] using ih h1 hp1 hs1
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueHighPop).setInQueue id 0
      have h2 : RootInv p T init st2 := by
        simpa [hcanon, st1, id] using canonClause_rootInv h1 ec
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hprops, hrun, hcanon, st1, id] using h2
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueHighPop).setInQueue id 0
      have h2 : RootInv p T init st2 := by
        simpa [hpush] using pushPropPrunes_rootInv h1 pending ps
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, st1, id] using h2
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueHighPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      have h2 : RootInv p T init st2 := by
        simpa [hpush] using pushPropPrunes_rootInv h1 pending ps
      have hent : st1.level = 0 → ∀ pe ∈ ps.toList, Entailed p [pe.1.lit] := by
        intro h0 pe hpe
        exact (hs1 id pr (by simpa [st1, id] using hprops))
          |>.entailed_target (viewWF_of_domsWF h1.domsWF pr.vars) h1 h0 hrun hpe
      have hp2 : PendingRoot p st2 pend := by
        simpa [hpush] using pushPropPrunes_pendingRoot (st := st1) hp1 ps hent
      have hs2 : PropsSound p T st2.props :=
        hs1.congr (by simpa [hpush] using (frame_pushPropPrunes st1 pending ps).props.symm)
      simp only [st1, id] at hprops hrun hpush hf ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using ih h2 hp2 hs2
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueLowPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hql, hprops, st1, id] using ih h1 hp1 hs1
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueLowPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using ih h1 hp1 hs1
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueLowPop).setInQueue id 0
      have h2 : RootInv p T init st2 := by
        simpa [hcanon, st1, id] using canonClause_rootInv h1 ec
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] using h2
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueLowPop).setInQueue id 0
      have h2 : RootInv p T init st2 := by
        simpa [hpush] using pushPropPrunes_rootInv h1 pending ps
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] using h2
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro hinv hpending hsound
      have h1 : RootInv p T init st1 := by
        dsimp only [st1]
        exact (hinv.queueLowPop).setInQueue id 0
      have hp1 : PendingRoot p st1 pending := by
        dsimp only [st1]
        exact hpending.mono (by rw [setInQueue_level])
      have hs1 : PropsSound p T st1.props := by
        dsimp only [st1]
        exact hsound.congr (by rw [setInQueue_props])
      have h2 : RootInv p T init st2 := by
        simpa [hpush] using pushPropPrunes_rootInv h1 pending ps
      have hent : st1.level = 0 → ∀ pe ∈ ps.toList, Entailed p [pe.1.lit] := by
        intro h0 pe hpe
        exact (hs1 id pr (by simpa [st1, id] using hprops))
          |>.entailed_target (viewWF_of_domsWF h1.domsWF pr.vars) h1 h0 hrun hpe
      have hp2 : PendingRoot p st2 pend := by
        simpa [hpush] using pushPropPrunes_pendingRoot (st := st1) hp1 ps hent
      have hs2 : PropsSound p T st2.props :=
        hs1.congr (by simpa [hpush] using (frame_pushPropPrunes st1 pending ps).props.symm)
      simp only [st1, id] at hprops hrun hpush hf ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using ih h2 hp2 hs2
  | case18 st pending f hback hq hql =>
      intro hinv hpending hsound
      simpa [drain, hback, hq, hql] using hinv

@[simp] theorem undoStep_props (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).props = st.props := rfl

@[simp] theorem undoFuel_props (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).props = st.props := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem undoStep_table (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).table = st.table := rfl

@[simp] theorem undoStep_db (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).db = st.db := rfl

@[simp] theorem undoFuel_table (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).table = st.table := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem undoFuel_db (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).db = st.db := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem backjump_props (st : EngineState p T) (k : Nat) :
    (backjump st k).props = st.props := by
  simp [backjump]

@[simp] theorem backjump_table (st : EngineState p T) (k : Nat) :
    (backjump st k).table = st.table := by
  simp [backjump]

@[simp] theorem backjump_db (st : EngineState p T) (k : Nat) :
    (backjump st k).db = st.db := by
  simp [backjump]

/-- Backjumping to a strictly lower level keeps the root invariant: the
trail shrinks, so every surviving level-zero entry was already entailed. -/
theorem RootInv.backjump {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st)
    {k : Nat} (hk : k < st.level) : RootInv p T init (backjump st k) := by
  refine ⟨⟨backjump_slotHistory h.hist.1 h.hist.2 hk, backjump_trailInv h.hist.2 k⟩,
    h.init_inv, ?_, ?_, levelMono_backjump h.level_mono k, ?_, h.conv, ?_⟩
  · rw [backjump_table]; exact h.table_inv
  · rw [backjump_table, backjump_db]; exact h.lits_wf
  · intro i e hi h0
    rw [backjump_trail] at hi
    rw [Array.getElem?_extract] at hi
    split at hi
    · rename_i hlt
      exact h.root i e (by simpa using hi) h0
    · cases hi
  · rw [backjump_db]; exact h.db_inv

/-- Entering a new decision level keeps the root invariant: it leaves the
trail unchanged, and every level-zero entry is still entailed. -/
theorem RootInv.newLevel {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init (newLevel st) := by
  refine ⟨⟨SlotHistory.congr h.hist.1 rfl rfl (fun _ => rfl),
    newLevel_trailInv h.hist.2⟩, h.init_inv, h.table_inv, h.lits_wf, ?_, ?_,
    h.conv, h.db_inv⟩
  · exact levelMono_of_trail h.level_mono rfl
  · intro i e hi h0
    rw [newLevel_trail] at hi
    exact h.root i e hi h0

/-- Reclaiming the transient-reason suffix keeps the root invariant. -/
theorem RootInv.trimReasonsStats {p : CompiledProblem DomConstraint} {T : LitTable}
    {init : Array DomC} {st : EngineState p T} (h : RootInv p T init st) :
    RootInv p T init st.trimReasonsStats :=
  h.congr rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl rfl

end LeanFzn.Engine

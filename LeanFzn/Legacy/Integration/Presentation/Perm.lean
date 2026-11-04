/-
File: LeanFzn/Integration/Presentation/Perm.lean

Purpose (PLAN F4): the permutation-transfer facts needed when the seeded
driver runs on a re-ordered presentation of the compiled box
(`annotDomains p orders`, the F2/F3 value orders).  A per-slot permutation of
the domains preserves:

  * the literal pool `litPool` (the threshold/value pools only look at the
    integer view of a domain, and `Dom.Perm` preserves that view);
  * database alignment (`DatabaseAligned`);
  * the finite assignment set `allAssigns`.

These are class-P facts: they say a presentation is a re-ordering, not a
constraint change, so every certified seeded run on the re-ordered box
transfers back to the compiled box without a new search theorem.

DAG: Annot + SupportedDatabaseFacts + FrontierSemantics -> this file
-> LcgSeedConfig.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.Kernel.Annot
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedDatabaseFacts
import LeanFzn.Solver.Propagation.FrontierSemantics

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP

/-! ## §1 A pointwise `Dom.Perm` relation on boxes -/

/-- Pointwise domain permutation of two boxes of equal length.  This is the
relation a value presentation induces (`annotDomains`); it is deliberately an
inductive so every transfer below is a structural induction. -/
inductive DomListPerm : List Domain → List Domain → Prop
  | nil : DomListPerm [] []
  | cons {d e : Domain} {ds es : List Domain} (h : d.Perm e)
      (t : DomListPerm ds es) : DomListPerm (d :: ds) (e :: es)

namespace DomListPerm

theorem refl (ds : List Domain) : DomListPerm ds ds := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons (Dom.Perm.refl d) ih

theorem trans {a b c : List Domain} (h₁ : DomListPerm a b) (h₂ : DomListPerm b c) :
    DomListPerm a c := by
  induction h₁ generalizing c with
  | nil => cases h₂; exact .nil
  | cons hd ht ih =>
      cases h₂ with
      | cons hd₂ ht₂ => exact .cons (hd.trans hd₂) (ih ht₂)

theorem symm {a b : List Domain} (h : DomListPerm a b) : DomListPerm b a := by
  induction h with
  | nil => exact .nil
  | cons hd ht ih => exact .cons hd.symm ih

end DomListPerm

/-! ## §2 The literal pool is presentation-invariant -/

theorem vocabDomInts_perm {d e : Domain} (h : d.Perm e) :
    (vocabDomInts d).Perm (vocabDomInts e) :=
  List.Perm.filterMap Value.intView h

theorem threshPool_perm {d e : Domain} (h : d.Perm e) :
    (threshPool d).Perm (threshPool e) := by
  unfold threshPool
  exact List.Perm.append (vocabDomInts_perm h)
    ((vocabDomInts_perm h).map (fun i => i - 1))

theorem slotAtomPool_perm {s : Nat} {d e : Domain} (h : d.Perm e) :
    (slotAtomPool s d).Perm (slotAtomPool s e) := by
  unfold slotAtomPool
  exact List.Perm.append
    (List.Perm.append (List.Perm.refl _)
      ((threshPool_perm h).map (Atom.intLe s)))
    ((vocabDomInts_perm h).map (Atom.intNe s))

/-- A pointwise permutation of boxes permutes their slot-indexed atom pools. -/
theorem atomPoolBase_domListPerm {ds es : List Domain} (h : DomListPerm ds es)
    (s : Nat) : (atomPoolBase s ds).Perm (atomPoolBase s es) := by
  induction h generalizing s with
  | nil => exact List.Perm.refl _
  | cons hd ht ih =>
      exact List.Perm.append (slotAtomPool_perm hd) (ih (s + 1))

theorem atomPool_domListPerm {ds es : List Domain} (h : DomListPerm ds es) :
    (atomPool ds).Perm (atomPool es) := by
  unfold atomPool
  exact List.Perm.append (atomPoolBase_domListPerm h 0)
    ((atomPoolBase_domListPerm h 0).map Atom.boolFlip)

theorem litPool_domListPerm {ds es : List Domain} (h : DomListPerm ds es) :
    (litPool ds).Perm (litPool es) := by
  unfold litPool
  have hp := atomPool_domListPerm h
  exact List.Perm.append
    (List.Perm.append
      (List.Perm.append (hp.map posLit) (hp.map negLit))
      (hp.map flipPosLit))
    (hp.map flipNegLit)

/-- Database alignment transfers across a presentation permutation. -/
theorem databaseAligned_domListPerm {orig orig' : List Domain}
    (h : DomListPerm orig orig') {db : List Clause}
    (hal : DatabaseAligned orig db) : DatabaseAligned orig' db := by
  intro c hc q hq
  exact (litPool_domListPerm h).mem_iff.mp (hal c hc q hq)

/-! ## §3 The assignment set is presentation-invariant -/

theorem mem_allAssigns_domListPerm {ds es : List Domain} (h : DomListPerm ds es) :
    ∀ a : Assignment, a ∈ allAssigns ds ↔ a ∈ allAssigns es := by
  induction h with
  | nil => intro a; simp [allAssigns]
  | cons hd ht ih =>
      intro a
      rw [mem_allAssigns_cons_iff, mem_allAssigns_cons_iff]
      constructor
      · rintro ⟨v, hv, a', ha', rfl⟩
        exact ⟨v, hd.dom_mem_iff.mp hv, a', (ih a').mp ha', rfl⟩
      · rintro ⟨v, hv, a', ha', rfl⟩
        exact ⟨v, hd.dom_mem_iff.mpr hv, a', (ih a').mpr ha', rfl⟩

/-! ## §4 Presentations built by `reorderAux`/`reorderAuxWith` -/

theorem reorderAuxWith_domListPerm {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) :
    ∀ (s : Nat) (ds : List Domain), DomListPerm (LcgHeur.reorderAuxWith σ s ds) ds := by
  intro s ds
  induction ds generalizing s with
  | nil => exact .nil
  | cons d ds ih => exact .cons (hσ s d) (ih (s + 1))

theorem reorderAux_domListPerm (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (ds : List Domain) :
    DomListPerm (LcgHeur.reorderAux dcs db s ds) ds := by
  induction ds generalizing s with
  | nil => exact .nil
  | cons d ds ih => exact .cons (LcgHeur.sortDom_perm dcs db s d) (ih (s + 1))

theorem heurDomains_domListPerm (p : CompiledProblem DomConstraint) :
    DomListPerm (LcgHeur.heurDomains p) p.domains :=
  reorderAux_domListPerm p.constraints (LcgHeur.actDb p) 0 p.domains

theorem annotDomains_domListPerm (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) :
    DomListPerm (annotDomains p orders) p.domains := by
  have h₁ : DomListPerm (annotDomains p orders) (LcgHeur.heurDomains p) := by
    unfold annotDomains
    exact reorderAuxWith_domListPerm
      (σ := annotOrder orders)
      (fun s d => annotDomains_perm p orders s d) 0 (LcgHeur.heurDomains p)
  exact h₁.trans (heurDomains_domListPerm p)

end LeanFzn.Integration

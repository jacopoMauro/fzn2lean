/-
File: LeanFzn/Engine/Lit.lean

Purpose:
  The literal layer of Core: the append-only intern table, the definitional
  bridge from a packed `PLit` to its `Literal`, the sound `EClause`
  constructors/transports, and the reusable resolution and monotonicity
  lemmas every later engine module uses.

  `PLit` is self-describing (R1): `idx` is the dense watch index, `lit` is
  the denotation carried by the pack.  `LitTable.decode` reads `lit`, so an
  `EClause` keeps its meaning under append-only growth of the table.  The
  table invariant `LitTable.TableWF` ties `lits` to `lookup`; it is a
  runtime/completeness invariant, never a soundness obligation.

  Soundness contract: every
  `EClause` stored or used as a reason is entailed by the compiled
  problem.  This file proves the contract's reusable consequences:
  resolution (`resolve_entailed`), refutation by an entailed empty clause
  (`entailed_nil_unsat`), monotonicity under a stronger problem
  (`Entailed_mono`), and soundness of the syntactic implication test
  (`litImpliesNot_sound`).

Dependencies:
  - LeanFzn.Engine.Types: `PLit`, `LitTable`, `Entailed`, `EClause`.
  - LeanFzn.Solver.Propagation.Encoding: literal evaluation laws and the
    `posLe`/`negLe`/`posNe`/`negNe`/`posBool` evaluation lemmas.
  - Std.Data.HashMap.Lemmas: intern-cache lemmas.

DAG:
  LeanFzn.Engine.Types -> LeanFzn.Engine.Lit -> LeanFzn.Engine.*
-/
import LeanFzn.Engine.Types
import LeanFzn.Solver.Propagation.Encoding
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Packed literals and the intern table -/

/-- The slot read by an atom. -/
def atomSlot : Atom → Nat
  | .boolEq s _ => s
  | .intLe s _ => s
  | .intNe s _ => s

/-- The slot read by a packed literal. -/
def PLit.slot (l : PLit) : Nat := atomSlot l.lit.atom

/-- The negation of a packed literal, with a placeholder index (the engine
canonicalizes it through the live table before use). -/
def PLit.negate (l : PLit) : PLit := { l with lit := l.lit.negate }

/-- A placeholder packed literal.  Prop outputs use these; the engine
re-interns every literal it receives before watching it. -/
def pLit (l : Literal) : PLit := ⟨0, l⟩

/-- Decoding a placeholder literal returns the literal itself. -/
theorem LitTable.decode_pLit (T : LitTable) (l : Literal) :
    T.decode (pLit l) = l := rfl

/-- Decoding commutes with packed negation. -/
theorem LitTable.decode_negate (T : LitTable) (l : PLit) :
    T.decode l.negate = (T.decode l).negate := rfl

/-- Unpacked version of `LitTable.decode_negate`. -/
theorem PLit.decode_negate (l : PLit) :
    PLit.decode l.negate = (PLit.decode l).negate := rfl

/-- Intern a literal in the append-only table. -/
def LitTable.intern (T : LitTable) (l : Literal) : PLit × LitTable :=
  match T.lookup.get? l with
  | some i => (⟨i, l⟩, T)
  | none =>
      let i := T.lits.size
      (⟨i, l⟩, { T with
        lits := T.lits.push l
        lookup := T.lookup.insert l i
        neg := T.neg.push 0 })

/-- Intern the negation of a packed literal, reusing the negation-index
cache when present and recording both directions on a miss.  A cache hit
returns the recorded index without touching the hash map. -/
def LitTable.internNeg (T : LitTable) (l : PLit) : PLit × LitTable :=
  match T.neg[l.idx]? with
  | some (j + 1) => (⟨j, l.lit.negate⟩, T)
  | _ =>
      let (n, T') := T.intern l.lit.negate
      let neg := (T'.neg.set! l.idx (n.idx + 1)).set! n.idx (l.idx + 1)
      (n, { T' with neg })

/-- Intern an array of literals left-to-right. -/
def LitTable.internArray (T : LitTable) (ls : Array Literal) : Array PLit × LitTable :=
  ls.foldl (fun (acc : Array PLit × LitTable) l =>
    let (p, T') := acc.2.intern l
    (acc.1.push p, T')) (#[], T)

/-! ## Sound `EClause` constructors and canonicalisation -/

/-- Build an `EClause` from packed literals, given the entailment proof of
its decoding.  This is the only way to construct an `EClause`; the former
spike constructors with an unproved proof field are gone. -/
def EClause.ofLits (p : CompiledProblem DomConstraint) (T : LitTable)
    (lits : Array PLit) (ent : Entailed p (T.decodeClause lits)) : EClause p T :=
  ⟨lits, ent⟩

/-- Pointwise equality of decoded literals preserves the decoded clause.
This is the R4 transport lemma: canonicalising the `idx` component of a
packed clause (while keeping each carried `lit`) does not change its
denotation. -/
theorem LitTable.decodeClause_canonical (T : LitTable) {lits lits' : Array PLit}
    (h : ∀ i : Nat, lits'[i]?.map PLit.decode = lits[i]?.map PLit.decode) :
    T.decodeClause lits' = T.decodeClause lits := by
  simp only [LitTable.decodeClause, LitTable.decode]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_toList]
  exact h i

/-- Re-index a clause after canonicalisation without changing its
denotation; this is what the engine uses for R4.  The proof field is
transported by `LitTable.decodeClause_canonical`. -/
def EClause.reindex {p : CompiledProblem DomConstraint} {T : LitTable}
    (e : EClause p T) (lits' : Array PLit)
    (h : ∀ i : Nat, lits'[i]?.map PLit.decode = e.lits[i]?.map PLit.decode) :
    EClause p T :=
  ⟨lits', by
    rw [LitTable.decodeClause_canonical T h]
    exact e.ent⟩

/-! ## Entailment lemmas -/

/-- Resolution of two entailed clauses is entailed.  The resolvent removes
`l` from the first clause and `l.negate` from the second, matching the
kernel's `resolve_step` filter shape. -/
theorem resolve_entailed {p : CompiledProblem DomConstraint} {c1 c2 : Clause}
    {l : Literal} (h1 : Entailed p c1) (h2 : Entailed p c2)
    (_hm1 : l ∈ c1) (_hm2 : l.negate ∈ c2) :
    Entailed p ((c1.filter (fun q => !litEqB q l)) ++
                (c2.filter (fun q => !litEqB q l.negate))) := by
  intro b hb hacc
  obtain ⟨lw, hlwm, hevw⟩ := h1 b hb hacc
  by_cases hlwp : litEqB lw l
  · obtain ⟨lr, hlrm, hevr⟩ := h2 b hb hacc
    by_cases hlrp : litEqB lr l.negate
    · have hlw_eq : lw = l := by simpa [litEqB] using hlwp
      have hlr_eq : lr = l.negate := by simpa [litEqB] using hlrp
      have h1' : l.eval b = some true := by
        rw [hlw_eq] at hevw
        exact hevw
      have h2' : l.negate.eval b = some true := by
        rw [hlr_eq] at hevr
        exact hevr
      rw [Literal.eval_negate, h1'] at h2'
      simp at h2'
    · exact ⟨lr, List.mem_append.mpr (Or.inr
        (List.mem_filter.mpr ⟨hlrm, by simpa [litEqB] using hlrp⟩)), hevr⟩
  · exact ⟨lw, List.mem_append.mpr (Or.inl
      (List.mem_filter.mpr ⟨hlwm, by simpa [litEqB] using hlwp⟩)), hevw⟩

/-- An entailed empty clause refutes the problem: every assignment in the
problem's box is rejected. -/
theorem entailed_nil_unsat {p : CompiledProblem DomConstraint}
    (h : Entailed p []) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro b hb
  cases hacc : accepts p b with
  | false => rfl
  | true =>
      obtain ⟨l, hl, _⟩ := h b hb hacc
      simp at hl

/-- Monotonicity under a stronger problem (same box, stronger acceptance).
`p'` is stronger than `p` when every assignment it accepts is also accepted
by `p`, i.e. `accepts p' b = true → accepts p b = true`.  N11 uses this to
keep the learned DB across objective-bound rounds. -/
theorem Entailed_mono {p p' : CompiledProblem DomConstraint} {c : Clause}
    (hdoms : p'.domains = p.domains)
    (hacc : ∀ b, accepts p' b = true → accepts p b = true)
    (h : Entailed p c) : Entailed p' c := by
  intro b hb hbacc
  rw [hdoms] at hb
  exact h b hb (hacc b hbacc)

/-! ## Evaluation helpers for `litImpliesNot_sound` -/

/-- A false positive order literal means the integer view exceeds the
bound. -/
theorem eval_posLe_false_iff (a : Assignment) (s : Nat) (k : Int) :
    (posLe s k).eval a = some false ↔ ∃ i, slotInt a s = some i ∧ ¬ i ≤ k := by
  rw [eval_posLe, Option.map_eq_some_iff]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, of_decide_eq_false h⟩,
    fun ⟨i, hi, h⟩ => ⟨i, hi, decide_eq_false h⟩⟩

/-- A false negative order literal means the integer view is at most the
bound. -/
theorem eval_negLe_false_iff (a : Assignment) (s : Nat) (k : Int) :
    (negLe s k).eval a = some false ↔ ∃ i, slotInt a s = some i ∧ i ≤ k := by
  rw [eval_negLe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_false'] at hdec
    exact of_decide_eq_true hdec
  · rintro ⟨i, hi, hik⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_false']
    exact decide_eq_true hik

/-- A false positive value-removal literal means the integer view equals the
removed value. -/
theorem eval_posNe_false_iff (a : Assignment) (s : Nat) (k : Int) :
    (posNe s k).eval a = some false ↔ ∃ i, slotInt a s = some i ∧ i = k := by
  rw [eval_posNe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    refine ⟨i, hi, ?_⟩
    have hik : ¬ i ≠ k := of_decide_eq_false hdec
    omega
  · rintro ⟨i, hi, hik⟩
    refine ⟨i, hi, ?_⟩
    subst i
    simp

/-- A false negative value-removal literal means the integer view differs
from the removed value. -/
theorem eval_negNe_false_iff (a : Assignment) (s : Nat) (k : Int) :
    (negNe s k).eval a = some false ↔ ∃ i, slotInt a s = some i ∧ i ≠ k := by
  rw [eval_negNe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_false'] at hdec
    exact of_decide_eq_true hdec
  · rintro ⟨i, hi, hik⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_false']
    exact decide_eq_true hik

/-- A false positive Boolean literal means the slot carries the other
Boolean value. -/
theorem eval_posBool_false_iff (a : Assignment) (s : Nat) (b : Bool) :
    (posBool s b).eval a = some false ↔
      ∃ x, a[s]? = some (.bool x) ∧ x ≠ b := by
  simp only [Literal.eval, posBool, Atom.eval]
  cases h : a[s]? with
  | none => simp
  | some val =>
    cases val with
    | bool x => cases x <;> cases b <;> simp
    | int x => simp
    | setOfInt x => simp
    | array x => simp

/-- A false negative Boolean literal means the slot carries the expected
Boolean. -/
theorem eval_negBool_false_iff (a : Assignment) (s : Nat) (b : Bool) :
    (Literal.mk (.boolEq s b) false).eval a = some false ↔
      a[s]? = some (.bool b) := by
  simp only [Literal.eval, Atom.eval]
  cases h : a[s]? with
  | none => simp
  | some val =>
    cases val with
    | bool x => cases x <;> cases b <;> simp
    | int x => simp
    | setOfInt x => simp
    | array x => simp

/-- A true negative Boolean literal means the slot carries the other
Boolean value. -/
theorem eval_negBool_true_iff (a : Assignment) (s : Nat) (b : Bool) :
    (Literal.mk (.boolEq s b) false).eval a = some true ↔
      ∃ x, a[s]? = some (.bool x) ∧ x ≠ b := by
  simp only [Literal.eval, Atom.eval]
  cases h : a[s]? with
  | none => simp
  | some val =>
    cases val with
    | bool x => cases x <;> cases b <;> simp
    | int x => simp
    | setOfInt x => simp
    | array x => simp

/-! ## The syntactic implication test -/

/-- Does the assignment literal `a` imply the negation of `b`?

This is the conservative syntactic test used by the trail scan; soundness
never depends on it (all reasons are entailed `EClause`s), but it must not
report a false implication, or analysis would resolve on a non-entailed
step.  The cases are the universally valid implications between signed
atoms on one slot: bounds are downward closed, integer disequalities are
the complement of a singleton, and Booleans have exactly two values. -/
def litImpliesNot (a b : Literal) : Bool :=
  match a.atom, b.atom with
  | .intLe s ka, .intLe t kb =>
      if s != t then false
      else if a.positive && b.positive then false
      else if a.positive && !b.positive then decide (ka ≤ kb)
      else if !a.positive && b.positive then decide (kb ≤ ka)
      else false
  | .intNe s va, .intNe t vb =>
      if s != t then false
      else if a.positive && b.positive then false
      else if a.positive && !b.positive then decide (va = vb)
      else if !a.positive && b.positive then decide (va = vb)
      else decide (va ≠ vb)
  | .boolEq s ba, .boolEq t bb =>
      if s != t then false
      else if a.positive && b.positive then decide (ba ≠ bb)
      else if a.positive && !b.positive then decide (ba = bb)
      else if !a.positive && b.positive then decide (ba = bb)
      else decide (ba ≠ bb)
  -- Mixed integer cases.  `negLe k` denotes `x ≥ k + 1`, `posLe k`
  -- denotes `x ≤ k`; `negNe v` denotes `x = v`, `posNe v` denotes
  -- `x ≠ v`.  All implications are over the integers, so a disequality
  -- never yields a bound and a bound never yields an equality.
  | .intLe s ka, .intNe t v =>
      if s != t then false
      else if a.positive && b.positive then false
      else if a.positive && !b.positive then decide (ka < v)
      else if !a.positive && b.positive then false
      else decide (v ≤ ka)
  | .intNe s v, .intLe t kb =>
      if s != t then false
      else if a.positive && b.positive then false
      else if a.positive && !b.positive then false
      else if !a.positive && b.positive then decide (kb < v)
      else decide (v ≤ kb)
  | _, _ => false

/-- The syntactic implication test is sound: whenever `litImpliesNot a b`
is true, every assignment that makes `a` true makes `b` false. -/
theorem litImpliesNot_sound {a b : Literal} (h : litImpliesNot a b = true) :
    ∀ assignment : Assignment,
      a.eval assignment = some true → b.eval assignment = some false := by
  obtain ⟨aa, ap⟩ := a
  obtain ⟨ba, bp⟩ := b
  intro asg ha
  cases aa with
  | boolEq s xa =>
      cases ba with
      | boolEq t xb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          · -- false, false: decide (xa ≠ xb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hne : xa ≠ xb := by simpa using h
              change (Literal.mk (.boolEq s xb) false).eval asg = some false
              rw [eval_negBool_false_iff]
              change (Literal.mk (.boolEq s xa) false).eval asg = some true at ha
              rw [eval_negBool_true_iff] at ha
              obtain ⟨x, hx, hxb⟩ := ha
              cases x <;> cases xa <;> cases xb <;> simp_all
          · -- false, true: decide (xa = xb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have heq : xa = xb := by simpa using h
              change (posBool s xb).eval asg = some false
              rw [eval_posBool_false_iff]
              change (Literal.mk (.boolEq s xa) false).eval asg = some true at ha
              rw [eval_negBool_true_iff] at ha
              obtain ⟨x, hx, hxb⟩ := ha
              subst xb
              exact ⟨x, hx, hxb⟩
          · -- true, false: decide (xa = xb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have heq : xa = xb := by simpa using h
              change (Literal.mk (.boolEq s xb) false).eval asg = some false
              rw [eval_negBool_false_iff]
              change (posBool s xa).eval asg = some true at ha
              rw [eval_posBool_iff] at ha
              subst xb
              exact ha
          · -- true, true: decide (xa ≠ xb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hne : xa ≠ xb := by simpa using h
              change (posBool s xb).eval asg = some false
              rw [eval_posBool_false_iff]
              change (posBool s xa).eval asg = some true at ha
              rw [eval_posBool_iff] at ha
              exact ⟨xa, ha, hne⟩
      | intLe t kb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          all_goals simp at h
      | intNe t vb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          all_goals simp at h
  | intLe s ka =>
      cases ba with
      | boolEq t xb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          all_goals simp at h
      | intLe t kb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          · -- false, false: impossible (else false)
            split at h <;> simp at h
          · -- false, true: decide (kb ≤ ka)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hle : kb ≤ ka := by simpa using h
              change (posLe s kb).eval asg = some false
              rw [eval_posLe_false_iff]
              change (negLe s ka).eval asg = some true at ha
              rw [eval_negLe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, false: decide (ka ≤ kb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hle : ka ≤ kb := by simpa using h
              change (negLe s kb).eval asg = some false
              rw [eval_negLe_false_iff]
              change (posLe s ka).eval asg = some true at ha
              rw [eval_posLe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, true: impossible
            split at h <;> simp at h
      | intNe t vb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          · -- false, false: decide (vb ≤ ka)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hle : vb ≤ ka := by simpa using h
              change (negNe s vb).eval asg = some false
              rw [eval_negNe_false_iff]
              change (negLe s ka).eval asg = some true at ha
              rw [eval_negLe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- false, true: impossible
            split at h <;> simp at h
          · -- true, false: decide (ka < vb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hlt : ka < vb := by simpa using h
              change (negNe s vb).eval asg = some false
              rw [eval_negNe_false_iff]
              change (posLe s ka).eval asg = some true at ha
              rw [eval_posLe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, true: impossible
            split at h <;> simp at h
  | intNe s va =>
      cases ba with
      | boolEq t xb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          all_goals simp at h
      | intLe t kb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          · -- false, false: decide (va ≤ kb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hle : va ≤ kb := by simpa using h
              change (negLe s kb).eval asg = some false
              rw [eval_negLe_false_iff]
              change (negNe s va).eval asg = some true at ha
              rw [eval_negNe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- false, true: decide (kb < va)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hlt : kb < va := by simpa using h
              change (posLe s kb).eval asg = some false
              rw [eval_posLe_false_iff]
              change (negNe s va).eval asg = some true at ha
              rw [eval_negNe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, false: impossible
            split at h <;> simp at h
          · -- true, true: impossible
            split at h <;> simp at h
      | intNe t vb =>
          cases ap <;> cases bp <;> simp only [litImpliesNot] at h
          · -- false, false: decide (va ≠ vb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have hne : va ≠ vb := by simpa using h
              change (negNe s vb).eval asg = some false
              rw [eval_negNe_false_iff]
              change (negNe s va).eval asg = some true at ha
              rw [eval_negNe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- false, true: decide (va = vb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have heq : va = vb := by simpa using h
              change (posNe s vb).eval asg = some false
              rw [eval_posNe_false_iff]
              change (negNe s va).eval asg = some true at ha
              rw [eval_negNe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, false: decide (va = vb)
            split at h
            · simp at h
            · rename_i hst
              have hstf : (s != t) = false := by simpa using hst
              have hst_eq : s = t := bne_eq_false_iff_eq.mp hstf
              subst t
              have heq : va = vb := by simpa using h
              change (negNe s vb).eval asg = some false
              rw [eval_negNe_false_iff]
              change (posNe s va).eval asg = some true at ha
              rw [eval_posNe_iff] at ha
              obtain ⟨i, hi, hik⟩ := ha
              exact ⟨i, hi, by omega⟩
          · -- true, true: impossible
            split at h <;> simp at h

/-! ## Intern-table laws -/

/-- The table invariant: every cached index points at its literal.  This is
a runtime/completeness invariant; soundness never depends on it because
`decode` reads the carried literal. -/
def LitTable.TableWF (T : LitTable) : Prop :=
  ∀ (l : Literal) (i : Nat), T.lookup.get? l = some i → T.lits[i]? = some l

/-- Computation rule for `intern` on a cache hit. -/
theorem LitTable.intern_of_get?_some {T : LitTable} {l : Literal} {i : Nat}
    (h : T.lookup.get? l = some i) : T.intern l = (⟨i, l⟩, T) := by
  unfold LitTable.intern
  rw [h]

/-- Computation rule for `intern` on a cache miss. -/
theorem LitTable.intern_of_get?_none {T : LitTable} {l : Literal}
    (h : T.lookup.get? l = none) :
    T.intern l = (⟨T.lits.size, l⟩,
      { lits := T.lits.push l, lookup := T.lookup.insert l T.lits.size
        neg := T.neg.push 0 }) := by
  unfold LitTable.intern
  rw [h]

/-- The literal component of an interned pack is the input literal. -/
theorem LitTable.intern_fst_lit (T : LitTable) (l : Literal) :
    (T.intern l).1.lit = l := by
  unfold LitTable.intern
  split <;> rfl

/-- Interning an existing literal returns its cached index. -/
theorem LitTable.intern_existing {T : LitTable} {l : Literal} {i : Nat}
    (h : T.lookup.get? l = some i) : (T.intern l).1 = ⟨i, l⟩ := by
  rw [intern_of_get?_some h]

/-- Intern extends the table append-only (prefix form). -/
theorem LitTable.intern_append_only (T : LitTable) (l : Literal) :
    T.lits.toList <+: (T.intern l).2.lits.toList := by
  cases hlook : T.lookup.get? l with
  | some i => rw [intern_of_get?_some hlook]; exact ⟨[], by simp⟩
  | none =>
      rw [intern_of_get?_none hlook]
      exact ⟨[l], by simp [Array.toList_push]⟩

/-- Interning grows the table by exactly zero or one entries. -/
theorem LitTable.intern_size (T : LitTable) (l : Literal) :
    (T.intern l).2.lits.size = T.lits.size ∨
      (T.intern l).2.lits.size = T.lits.size + 1 := by
  cases hlook : T.lookup.get? l with
  | some i => rw [intern_of_get?_some hlook]; exact Or.inl rfl
  | none =>
      rw [intern_of_get?_none hlook]
      exact Or.inr (by simp [Array.size_push])

/-- The returned pack is well-formed in the returned table. -/
theorem LitTable.intern_wf {T : LitTable} {l : Literal} (hT : T.TableWF) :
    (T.intern l).2.WF (T.intern l).1 := by
  cases hlook : T.lookup.get? l with
  | some i =>
      rw [intern_of_get?_some hlook]
      exact hT l i hlook
  | none =>
      rw [intern_of_get?_none hlook]
      unfold LitTable.WF
      rw [Array.getElem?_push]
      simp

/-- Interning preserves the table invariant. -/
theorem LitTable.intern_tableWF {T : LitTable} {l : Literal}
    (hT : T.TableWF) : (T.intern l).2.TableWF := by
  intro l' j hj
  cases hlook : T.lookup.get? l with
  | none =>
      rw [intern_of_get?_none hlook] at hj ⊢
      rw [Std.HashMap.get?_insert] at hj
      by_cases heq : l == l'
      · rw [if_pos heq] at hj
        simp only [Option.some.injEq] at hj
        subst j
        rw [Array.getElem?_push]
        have hl' : l = l' := by simpa using heq
        subst l'
        simp
      · rw [if_neg heq] at hj
        have hjne : j ≠ T.lits.size := by
          intro hjeq
          have hsome := hT l' j hj
          rw [hjeq] at hsome
          have hnone : T.lits[T.lits.size]? = none :=
            Array.getElem?_eq_none (Nat.le_refl _)
          rw [hnone] at hsome
          simp at hsome
        rw [Array.getElem?_push]
        rw [if_neg hjne]
        exact hT l' j hj
  | some i =>
      rw [intern_of_get?_some hlook] at hj ⊢
      exact hT l' j hj

/-- The negation cache returns the literal's negation. -/
theorem LitTable.internNeg_fst_lit (T : LitTable) (l : PLit) :
    (T.internNeg l).1.lit = l.lit.negate := by
  unfold LitTable.internNeg
  split
  · rfl
  · exact intern_fst_lit T l.lit.negate

/-- `internNeg` extends the literal table append-only. -/
theorem LitTable.internNeg_append_only (T : LitTable) (l : PLit) :
    T.lits.toList <+: (T.internNeg l).2.lits.toList := by
  unfold LitTable.internNeg
  split
  · exact ⟨[], by simp⟩
  · exact intern_append_only T l.lit.negate

/-- `internNeg` preserves the intern-table invariant. -/
theorem LitTable.internNeg_tableWF {T : LitTable} {l : PLit}
    (hT : T.TableWF) : (T.internNeg l).2.TableWF := by
  unfold LitTable.internNeg
  split
  · exact hT
  · exact intern_tableWF hT

/-- A well-formed pack stays well-formed under an append-only table
extension. -/
theorem LitTable.WF_mono {T T' : LitTable} {p : PLit}
    (hpre : T.lits.toList <+: T'.lits.toList) (h : T.WF p) : T'.WF p := by
  obtain ⟨c, hc⟩ := hpre
  unfold LitTable.WF at h ⊢
  have hlen : p.idx < T.lits.size := by
    by_cases hlt : p.idx < T.lits.size
    · exact hlt
    · exfalso
      have hnone : T.lits[p.idx]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hlt)
      rw [hnone] at h
      simp at h
  have hlen' : p.idx < T.lits.toList.length := by simpa using hlen
  have hidx : T'.lits[p.idx]? = T.lits[p.idx]? := by
    rw [← Array.getElem?_toList, ← Array.getElem?_toList, ← hc,
      List.getElem?_append_left hlen']
  rw [hidx]
  exact h

/-- Two well-formed packed literals with the same intern index denote the
same literal.  This is the bridge the clause-prune contract needs to turn a
watch-index match into literal identity. -/
theorem LitTable.WF_lit_eq {T : LitTable} {q l : PLit}
    (hq : T.WF q) (hl : T.WF l) (hidx : q.idx = l.idx) : q.lit = l.lit := by
  unfold LitTable.WF at hq hl
  rw [hidx] at hq
  rw [hq] at hl
  exact Option.some.inj hl

/-! ### Array interning -/

/-- The list fold underlying `internArray` (proof-only helper). -/
private def LitTable.internFold (T : LitTable) (acc : Array PLit) :
    List Literal → Array PLit × LitTable
  | [] => (acc, T)
  | l :: ls =>
      let q := T.intern l
      internFold q.2 (acc.push q.1) ls

/-- `Array.foldl` form of `internArray` is the list fold above. -/
private theorem LitTable.list_foldl_intern (T : LitTable) (acc : Array PLit)
    (ls : List Literal) :
    List.foldl (fun (acc : Array PLit × LitTable) l =>
      let q := acc.2.intern l
      (acc.1.push q.1, q.2)) (acc, T) ls = internFold T acc ls := by
  induction ls generalizing T acc with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.foldl, internFold]
      cases hq : T.intern l with
      | mk p T' => exact ih T' (acc.push p)

/-- `internArray` is the append-only list fold. -/
private theorem LitTable.internArray_eq_fold (T : LitTable) (ls : Array Literal) :
    T.internArray ls = internFold T #[] ls.toList := by
  unfold LitTable.internArray
  rw [← Array.foldl_toList]
  exact list_foldl_intern T #[] ls.toList

/-- Tail-recursive runtime twin of `internArray`.  The literal array, the
lookup table and the negation cache are carried as separate accumulator
arguments so that appending a fresh literal pushes into an unshared array;
the logical definition `internArray` projects and replaces the table field
on every step, which makes the compiled code copy the whole literal array at
each new literal. -/
def LitTable.internListFast (ls : List Literal) (acc : Array PLit)
    (lits : Array Literal) (lookup : Std.HashMap Literal Nat) (neg : Array Nat) :
    Array PLit × LitTable :=
  match ls with
  | [] => (acc, ⟨lits, lookup, neg⟩)
  | l :: ls =>
      match lookup.get? l with
      | some i => internListFast ls (acc.push ⟨i, l⟩) lits lookup neg
      | none =>
          let i := lits.size
          internListFast ls (acc.push ⟨i, l⟩) (lits.push l) (lookup.insert l i)
            (neg.push 0)

/-- The fast list fold agrees with the reference fold. -/
theorem LitTable.internListFast_eq (ls : List Literal) (acc : Array PLit)
    (lits : Array Literal) (lookup : Std.HashMap Literal Nat) (neg : Array Nat) :
    internListFast ls acc lits lookup neg = internFold ⟨lits, lookup, neg⟩ acc ls := by
  induction ls generalizing acc lits lookup neg with
  | nil => rfl
  | cons l ls ih =>
      rw [internListFast, internFold]
      cases h : lookup.get? l with
      | some i =>
          simp only [h, LitTable.intern]
          exact ih (acc.push ⟨i, l⟩) lits lookup neg
      | none =>
          simp only [h, LitTable.intern]
          exact ih (acc.push ⟨lits.size, l⟩) (lits.push l) (lookup.insert l lits.size)
            (neg.push 0)

/-- Tail-recursive runtime twin of `internArray`. -/
def LitTable.internArrayFast (T : LitTable) (ls : Array Literal) :
    Array PLit × LitTable :=
  internListFast ls.toList #[] T.lits T.lookup T.neg

/-- Single-literal twin of `intern` that keeps the literal array, lookup
table and negation cache as separate arguments, so the append can reuse the
arrays when the caller transfers the fields. -/
def LitTable.internOneFast (lits : Array Literal)
    (lookup : Std.HashMap Literal Nat) (neg : Array Nat) (l : Literal) :
    PLit × LitTable :=
  match lookup.get? l with
  | some i => (⟨i, l⟩, ⟨lits, lookup, neg⟩)
  | none =>
      let i := lits.size
      (⟨i, l⟩, ⟨lits.push l, lookup.insert l i, neg.push 0⟩)

/-- The single-literal twin is the reference `intern`. -/
theorem LitTable.internOneFast_eq (T : LitTable) (l : Literal) :
    internOneFast T.lits T.lookup T.neg l = T.intern l := by
  unfold internOneFast LitTable.intern
  cases h : T.lookup.get? l <;> simp [h]

/-- The fast array fold is the reference `internArray`. -/
theorem LitTable.internArrayFast_eq (T : LitTable) (ls : Array Literal) :
    T.internArrayFast ls = T.internArray ls := by
  rw [internArrayFast, internArray_eq_fold]
  exact internListFast_eq ls.toList #[] T.lits T.lookup T.neg

/-- Compile `internArray` as the tail-recursive twin; proofs keep the
reference fold. -/
@[csimp] theorem LitTable.internArray_eq_fast :
    @LitTable.internArray = @LitTable.internArrayFast := by
  funext T ls
  exact (internArrayFast_eq T ls).symm

/-- The decoded literals of a fold are the accumulated literals followed by
the remaining input. -/
private theorem LitTable.internFold_lits (T : LitTable) (acc : Array PLit)
    (ls : List Literal) :
    (internFold T acc ls).1.toList.map PLit.decode =
      acc.toList.map PLit.decode ++ ls := by
  induction ls generalizing T acc with
  | nil => simp [internFold]
  | cons l ls ih =>
      simp only [internFold]
      cases hq : T.intern l with
      | mk p T' =>
          rw [ih T' (acc.push p)]
          have hp : PLit.decode p = l := by
            have hpf := intern_fst_lit T l
            rw [hq] at hpf
            exact hpf
          simp [Array.toList_push, hp]

/-- The interned array denotes exactly the input literal list. -/
theorem LitTable.internArray_lits (T : LitTable) (ls : Array Literal) :
    (T.internArray ls).1.toList.map PLit.decode = ls.toList := by
  rw [internArray_eq_fold]
  simpa using internFold_lits T #[] ls.toList

/-- Lookup after `Array.set!`. -/
theorem array_set!_getElem? {α : Type} (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]? = if i = j then (if i < a.size then some v else none) else a[j]? := by
  change (a.setIfInBounds i v)[j]? = _
  rw [Array.getElem?_setIfInBounds]

/-- Lookup after two nested `Array.set!`s (the outer write wins on a tie). -/
theorem array_set!_set!_getElem? {α : Type} (a : Array α) (i j k : Nat) (u v : α) :
    ((a.set! i u).set! j v)[k]? =
      if k = j then (if j < a.size then some v else none)
      else if k = i then (if i < a.size then some u else none)
      else a[k]? := by
  rw [array_set!_getElem?]
  by_cases hkj : k = j
  · subst hkj
    simp [Array.size_set!]
  · rw [if_neg hkj]
    rw [array_set!_getElem?]
    by_cases hki : k = i
    · subst hki
      simp [Array.size_set!]
      omega
    · rw [if_neg hki]
      rw [if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ i = k)]

/-- The negation cache is semantically consistent with the literal array:
a cached entry at source index `i` points to an index holding the negation of
the literal stored at `i`. -/
def LitTable.NegWF (T : LitTable) : Prop :=
  ∀ (i j : Nat) (l : Literal), T.neg[i]? = some (j + 1) → T.lits[i]? = some l →
    T.lits[j]? = some l.negate

/-- Bundled intern-table invariant: the lookup cache is sound, the negation
cache has exactly one slot per literal, and its entries are consistent. -/
structure LitTable.Inv (T : LitTable) : Prop where
  table_wf : T.TableWF
  neg_size : T.neg.size = T.lits.size
  neg_wf : T.NegWF

/-- The empty table satisfies the bundled invariant. -/
theorem LitTable.inv_empty : ({} : LitTable).Inv := by
  refine ⟨?_, ?_, ?_⟩
  · intro l i h
    simp [LitTable.TableWF] at h
  · rfl
  · intro i j l hij _
    simp at hij

/-- Interning one literal preserves the bundled table invariant. -/
theorem LitTable.intern_inv {T : LitTable} (h : T.Inv) (l : Literal) :
    (T.intern l).2.Inv := by
  refine ⟨LitTable.intern_tableWF (l := l) h.table_wf, ?_, ?_⟩
  · cases hlook : T.lookup.get? l with
    | some i =>
        rw [LitTable.intern_of_get?_some hlook]
        exact h.neg_size
    | none =>
        rw [LitTable.intern_of_get?_none hlook]
        simp only [Array.size_push]
        have hsz := h.neg_size
        omega
  · intro i j m hij him
    cases hlook : T.lookup.get? l with
    | some i0 =>
        rw [LitTable.intern_of_get?_some hlook] at hij him ⊢
        exact h.neg_wf i j m hij him
    | none =>
        rw [LitTable.intern_of_get?_none hlook] at hij him ⊢
        rw [Array.getElem?_push] at hij
        split at hij
        · simp at hij
        · rename_i hne
          rw [Array.getElem?_push] at him
          split at him
          · rename_i hieq
            have hlt : i < T.neg.size := (Array.getElem?_eq_some_iff.mp hij).1
            have hsz := h.neg_size
            omega
          · rename_i hne2
            have h1 := h.neg_wf i j m hij him
            rw [Array.getElem?_push]
            have hjlt : j < T.lits.size := (Array.getElem?_eq_some_iff.mp h1).1
            rw [if_neg (by omega)]
            exact h1

/-- Interning an array preserves the bundled table invariant. -/
theorem LitTable.internArray_inv {T : LitTable} (h : T.Inv) (ls : Array Literal) :
    (T.internArray ls).2.Inv := by
  rw [LitTable.internArray_eq_fold]
  have hmain : ∀ (T : LitTable) (acc : Array PLit) (ls : List Literal),
      T.Inv → (internFold T acc ls).2.Inv := by
    intro T acc ls
    induction ls generalizing T acc with
    | nil => intro hT; exact hT
    | cons l ls ih =>
        intro hT
        simp only [internFold]
        cases hq : T.intern l with
        | mk p T' =>
            refine ih T' (acc.push p) ?_
            have := LitTable.intern_inv hT l
            rw [hq] at this
            exact this
  exact hmain T #[] ls.toList h

/-- The literal returned by `internNeg` is well formed in the resulting
table, provided the argument is well formed and the table invariant holds. -/
theorem LitTable.internNeg_wf {T : LitTable} (h : T.Inv) {l : PLit}
    (hl : T.WF l) : (T.internNeg l).2.WF (T.internNeg l).1 := by
  unfold LitTable.internNeg
  split
  · rename_i j hij
    exact h.neg_wf l.idx j l.lit hij hl
  · exact LitTable.intern_wf (l := l.lit.negate) h.table_wf

/-- The negation cache is consistent after `internNeg`. -/
theorem LitTable.internNeg_negWF {T : LitTable} (h : T.Inv) {l : PLit}
    (hl : T.WF l) : (T.internNeg l).2.NegWF := by
  unfold LitTable.internNeg
  split
  · rename_i j hij
    exact h.neg_wf
  · rename_i hmiss
    let n := (T.intern l.lit.negate).1
    let T' := (T.intern l.lit.negate).2
    have hT' : T'.Inv := LitTable.intern_inv h l.lit.negate
    have hnlits : T'.lits[l.idx]? = some l.lit := by
      unfold T'
      exact LitTable.WF_mono (LitTable.intern_append_only T l.lit.negate) hl
    have hnn : T'.lits[n.idx]? = some l.lit.negate := by
      unfold n T'
      simpa only [LitTable.WF, LitTable.intern_fst_lit] using
        LitTable.intern_wf (l := l.lit.negate) h.table_wf
    intro i j m hij him
    change (((T'.neg.set! l.idx (n.idx + 1)).set! n.idx (l.idx + 1))[i]?)
      = some (j + 1) at hij
    change T'.lits[i]? = some m at him
    rw [array_set!_set!_getElem?] at hij
    by_cases hin : i = n.idx
    · rw [if_pos hin] at hij
      by_cases hb : n.idx < T'.neg.size
      · rw [if_pos hb] at hij
        have hj : j = l.idx := by
          have := Option.some.inj hij
          omega
        subst j
        have hm : m = l.lit.negate := by
          rw [hin] at him
          rw [hnn] at him
          exact (Option.some.inj him).symm
        subst m
        rw [hnlits, Literal.negate_negate]
      · rw [if_neg hb] at hij
        simp at hij
    · rw [if_neg hin] at hij
      by_cases hil : i = l.idx
      · rw [if_pos hil] at hij
        by_cases hb : l.idx < T'.neg.size
        · rw [if_pos hb] at hij
          have hj : j = n.idx := by
            have := Option.some.inj hij
            omega
          subst j
          have hm : m = l.lit := by
            rw [hil] at him
            rw [hnlits] at him
            exact (Option.some.inj him).symm
          subst m
          rw [hnn]
        · rw [if_neg hb] at hij
          simp at hij
      · rw [if_neg hil] at hij
        exact hT'.neg_wf i j m hij him

/-- The negation cache keeps one slot per literal after `internNeg`. -/
theorem LitTable.internNeg_neg_size {T : LitTable} (h : T.Inv) (l : PLit) :
    (T.internNeg l).2.neg.size = (T.internNeg l).2.lits.size := by
  unfold LitTable.internNeg
  split
  · exact h.neg_size
  · dsimp only
    rw [Array.size_set!, Array.size_set!]
    exact (LitTable.intern_inv h l.lit.negate).neg_size

/-- `internNeg` preserves the bundled table invariant. -/
theorem LitTable.internNeg_inv {T : LitTable} (h : T.Inv) {l : PLit}
    (hl : T.WF l) : (T.internNeg l).2.Inv := by
  refine ⟨?_, LitTable.internNeg_neg_size h l, LitTable.internNeg_negWF h hl⟩
  unfold LitTable.internNeg
  split
  · exact h.table_wf
  · exact (LitTable.intern_inv h l.lit.negate).table_wf

/-- The decoded clause of an interned array is the input literal list.
This is the form N5/N6 use to build an `EClause.ofLits`. -/
theorem LitTable.decodeClause_internArray (T : LitTable) (ls : Array Literal) :
    T.decodeClause (T.internArray ls).1 = ls.toList := by
  unfold LitTable.decodeClause
  change (T.internArray ls).1.toList.map PLit.decode = ls.toList
  exact internArray_lits T ls

/-- Same decoded-clause statement read through the resulting table (the
form used when the `EClause` is stored against `(T.internArray ls).2`). -/
theorem LitTable.decodeClause_internArray_snd (T : LitTable) (ls : Array Literal) :
    (T.internArray ls).2.decodeClause (T.internArray ls).1 = ls.toList := by
  change T.decodeClause (T.internArray ls).1 = ls.toList
  exact decodeClause_internArray T ls

/-- `internArray` extends the table append-only. -/
private theorem LitTable.internFold_append_only (T : LitTable) (acc : Array PLit)
    (ls : List Literal) :
    T.lits.toList <+: (internFold T acc ls).2.lits.toList := by
  induction ls generalizing T acc with
  | nil => exact ⟨[], by simp [internFold]⟩
  | cons l ls ih =>
      simp only [internFold]
      cases hq : T.intern l with
      | mk p T' =>
          have h1 := intern_append_only T l
          rw [hq] at h1
          exact h1.trans (ih T' (acc.push p))

/-- `internArray` extends the table append-only. -/
theorem LitTable.internArray_append_only (T : LitTable) (ls : Array Literal) :
    T.lits.toList <+: (T.internArray ls).2.lits.toList := by
  rw [internArray_eq_fold]
  exact internFold_append_only T #[] ls.toList

/-- Combined fold invariant: the result table is well-formed and every
returned pack is well-formed in it. -/
private theorem LitTable.internFold_tableWF (T : LitTable) (acc : Array PLit)
    (ls : List Literal) (hT : T.TableWF)
    (hacc : ∀ (j : Nat) p, acc[j]? = some p → T.WF p) :
    (internFold T acc ls).2.TableWF ∧
      (∀ (j : Nat) p, (internFold T acc ls).1[j]? = some p →
        (internFold T acc ls).2.WF p) := by
  induction ls generalizing T acc with
  | nil => exact ⟨hT, hacc⟩
  | cons l ls ih =>
      simp only [internFold]
      cases hq : T.intern l with
      | mk p T' =>
          have hT' : T'.TableWF := by
            have := intern_tableWF (T := T) (l := l) hT
            rw [hq] at this
            exact this
          have hp : T'.WF p := by
            have := intern_wf (T := T) (l := l) hT
            rw [hq] at this
            exact this
          have hpre : T.lits.toList <+: T'.lits.toList := by
            have := intern_append_only T l
            rw [hq] at this
            exact this
          have hacc' : ∀ (j : Nat) q, (acc.push p)[j]? = some q → T'.WF q := by
            intro j q hj
            rw [Array.getElem?_push] at hj
            by_cases hjeq : j = acc.size
            · rw [if_pos hjeq] at hj
              simp only [Option.some.injEq] at hj
              subst q
              exact hp
            · rw [if_neg hjeq] at hj
              exact WF_mono hpre (hacc j q hj)
          exact ih T' (acc.push p) hT' hacc'

/-- `internArray` preserves the table invariant. -/
theorem LitTable.internArray_tableWF {T : LitTable} (hT : T.TableWF)
    (ls : Array Literal) : (T.internArray ls).2.TableWF := by
  rw [internArray_eq_fold]
  exact (internFold_tableWF T #[] ls.toList hT
    (by intro j p hj; simp at hj)).1

/-- Every pack returned by `internArray` is well-formed in the returned
table. -/
theorem LitTable.internArray_wf {T : LitTable} (hT : T.TableWF)
    (ls : Array Literal) :
    ∀ (i : Nat) (p : PLit), (T.internArray ls).1[i]? = some p →
      (T.internArray ls).2.WF p := by
  rw [internArray_eq_fold]
  exact (internFold_tableWF T #[] ls.toList hT
    (by intro j p hj; simp at hj)).2

/-! ### Hinted clause interning -/

/-- A pack is already interned when the live table maps its index to its
carried literal. -/
def LitTable.PackOK (T : LitTable) (l : PLit) : Prop :=
  T.lits[l.idx]? = some l.lit

/-- Intern a pack, reusing its index when the table already maps that index
to the carried literal.  The index is only a hint: a stale or placeholder
index falls back to the hash-map `intern`. -/
def LitTable.internPack (T : LitTable) (l : PLit) : PLit × LitTable :=
  if T.lits[l.idx]? == some l.lit then (l, T) else T.intern l.lit

/-- The literal component of a hinted intern is unchanged. -/
theorem LitTable.internPack_fst_lit (T : LitTable) (l : PLit) :
    (T.internPack l).1.lit = l.lit := by
  unfold internPack
  split
  · rfl
  · exact LitTable.intern_fst_lit T l.lit

/-- Hinted interning extends the table append-only. -/
theorem LitTable.internPack_append_only (T : LitTable) (l : PLit) :
    T.lits.toList <+: (T.internPack l).2.lits.toList := by
  unfold internPack
  split
  · exact ⟨[], by simp⟩
  · exact LitTable.intern_append_only T l.lit

/-- Hinted interning preserves the hash-map well-formedness. -/
theorem LitTable.internPack_tableWF {T : LitTable} (hT : T.TableWF)
    (l : PLit) : (T.internPack l).2.TableWF := by
  unfold internPack
  split
  · exact hT
  · exact LitTable.intern_tableWF hT

/-- Hinted interning preserves the bundled table invariant. -/
theorem LitTable.internPack_inv {T : LitTable} (hT : T.Inv)
    (l : PLit) : (T.internPack l).2.Inv := by
  unfold internPack
  split
  · exact hT
  · exact LitTable.intern_inv hT l.lit

/-- The returned pack is well formed in the returned table. -/
theorem LitTable.internPack_wf {T : LitTable} (hT : T.TableWF)
    (l : PLit) : (T.internPack l).2.WF (T.internPack l).1 := by
  unfold internPack
  split
  · rename_i h
    exact beq_iff_eq.mp h
  · exact LitTable.intern_wf hT

/-- The list fold underlying `internPacks` (proof-only helper). -/
private def LitTable.internPackFold (T : LitTable) (acc : Array PLit) :
    List PLit → Array PLit × LitTable
  | [] => (acc, T)
  | l :: ls =>
      let q := T.internPack l
      internPackFold q.2 (acc.push q.1) ls

/-- Intern an array of packed literals left-to-right, reusing indices that
the table already validates. -/
def LitTable.internPacks (T : LitTable) (ls : Array PLit) :
    Array PLit × LitTable :=
  internPackFold T #[] ls.toList

/-- The decoded literals of the hinted fold are the accumulated literals
followed by the remaining input. -/
private theorem LitTable.internPackFold_lits (T : LitTable) (acc : Array PLit)
    (ls : List PLit) :
    (internPackFold T acc ls).1.toList.map PLit.decode =
      acc.toList.map PLit.decode ++ ls.map PLit.decode := by
  induction ls generalizing T acc with
  | nil => simp [internPackFold]
  | cons l ls ih =>
      simp only [internPackFold]
      cases hq : T.internPack l with
      | mk p T' =>
          rw [ih T' (acc.push p)]
          have hp : PLit.decode p = PLit.decode l := by
            have := LitTable.internPack_fst_lit T l
            rw [hq] at this
            exact this
          simp [Array.toList_push, hp]

/-- The hinted fold denotes exactly the input literal list. -/
theorem LitTable.internPacks_lits (T : LitTable) (ls : Array PLit) :
    (T.internPacks ls).1.toList.map PLit.decode = ls.toList.map PLit.decode := by
  unfold internPacks
  simpa using LitTable.internPackFold_lits T #[] ls.toList

/-- The hinted fold extends the table append-only. -/
private theorem LitTable.internPackFold_append_only (T : LitTable)
    (acc : Array PLit) (ls : List PLit) :
    T.lits.toList <+: (internPackFold T acc ls).2.lits.toList := by
  induction ls generalizing T acc with
  | nil => exact ⟨[], by simp [internPackFold]⟩
  | cons l ls ih =>
      simp only [internPackFold]
      cases hq : T.internPack l with
      | mk p T' =>
          have h1 := LitTable.internPack_append_only T l
          rw [hq] at h1
          exact h1.trans (ih T' (acc.push p))

/-- Hinted interning an array extends the table append-only. -/
theorem LitTable.internPacks_append_only (T : LitTable) (ls : Array PLit) :
    T.lits.toList <+: (T.internPacks ls).2.lits.toList := by
  unfold internPacks
  exact LitTable.internPackFold_append_only T #[] ls.toList

/-- Combined fold invariant: the result table is well-formed and every
returned pack is well-formed in it. -/
private theorem LitTable.internPackFold_tableWF (T : LitTable)
    (acc : Array PLit) (ls : List PLit) (hT : T.TableWF)
    (hacc : ∀ (j : Nat) p, acc[j]? = some p → T.WF p) :
    (internPackFold T acc ls).2.TableWF ∧
      (∀ (j : Nat) p, (internPackFold T acc ls).1[j]? = some p →
        (internPackFold T acc ls).2.WF p) := by
  induction ls generalizing T acc with
  | nil => exact ⟨hT, hacc⟩
  | cons l ls ih =>
      simp only [internPackFold]
      cases hq : T.internPack l with
      | mk p T' =>
          have hT' : T'.TableWF := by
            have := LitTable.internPack_tableWF (T := T) hT l
            rw [hq] at this
            exact this
          have hp : T'.WF p := by
            have := LitTable.internPack_wf (T := T) hT l
            rw [hq] at this
            exact this
          have hpre : T.lits.toList <+: T'.lits.toList := by
            have := LitTable.internPack_append_only T l
            rw [hq] at this
            exact this
          have hacc' : ∀ (j : Nat) q, (acc.push p)[j]? = some q → T'.WF q := by
            intro j q hj
            rw [Array.getElem?_push] at hj
            by_cases hjeq : j = acc.size
            · rw [if_pos hjeq] at hj
              simp only [Option.some.injEq] at hj
              subst q
              exact hp
            · rw [if_neg hjeq] at hj
              exact WF_mono hpre (hacc j q hj)
          exact ih T' (acc.push p) hT' hacc'

/-- Hinted interning preserves the hash-map well-formedness. -/
theorem LitTable.internPacks_tableWF {T : LitTable} (hT : T.TableWF)
    (ls : Array PLit) : (T.internPacks ls).2.TableWF := by
  unfold internPacks
  exact (LitTable.internPackFold_tableWF T #[] ls.toList hT
    (by intro j p hj; simp at hj)).1

/-- Every pack returned by hinted interning is well formed in the returned
table. -/
theorem LitTable.internPacks_wf {T : LitTable} (hT : T.TableWF)
    (ls : Array PLit) :
    ∀ (i : Nat) (p : PLit), (T.internPacks ls).1[i]? = some p →
      (T.internPacks ls).2.WF p := by
  unfold internPacks
  exact (LitTable.internPackFold_tableWF T #[] ls.toList hT
    (by intro j p hj; simp at hj)).2

/-- The hinted fold preserves the bundled table invariant. -/
private theorem LitTable.internPackFold_inv (T : LitTable)
    (acc : Array PLit) (ls : List PLit) (hT : T.Inv) :
    (internPackFold T acc ls).2.Inv := by
  induction ls generalizing T acc with
  | nil => exact hT
  | cons l ls ih =>
      simp only [internPackFold]
      cases hq : T.internPack l with
      | mk p T' =>
          have := LitTable.internPack_inv hT l
          rw [hq] at this
          exact ih T' (acc.push p) this

/-- Hinted interning an array preserves the bundled table invariant. -/
theorem LitTable.internPacks_inv {T : LitTable} (hT : T.Inv)
    (ls : Array PLit) : (T.internPacks ls).2.Inv := by
  unfold internPacks
  exact LitTable.internPackFold_inv T #[] ls.toList hT

/-- Tail-recursive runtime twin of `internPacks`.  A valid hint is reused
without touching the hash map; otherwise the literal is interned exactly as
`internPack` does. -/
def LitTable.internPackListFast (ls : List PLit) (acc : Array PLit)
    (lits : Array Literal) (lookup : Std.HashMap Literal Nat) (neg : Array Nat) :
    Array PLit × LitTable :=
  match ls with
  | [] => (acc, ⟨lits, lookup, neg⟩)
  | l :: ls =>
      if lits[l.idx]? == some l.lit then
        internPackListFast ls (acc.push l) lits lookup neg
      else
        match lookup.get? l.lit with
        | some i =>
            internPackListFast ls (acc.push ⟨i, l.lit⟩) lits lookup neg
        | none =>
            let i := lits.size
            internPackListFast ls (acc.push ⟨i, l.lit⟩) (lits.push l.lit)
              (lookup.insert l.lit i) (neg.push 0)

/-- The fast hinted list fold agrees with the reference fold. -/
theorem LitTable.internPackListFast_eq (ls : List PLit) (acc : Array PLit)
    (lits : Array Literal) (lookup : Std.HashMap Literal Nat) (neg : Array Nat) :
    internPackListFast ls acc lits lookup neg =
      internPackFold ⟨lits, lookup, neg⟩ acc ls := by
  induction ls generalizing acc lits lookup neg with
  | nil => rfl
  | cons l ls ih =>
      rw [internPackListFast]
      by_cases h : (lits[l.idx]? == some l.lit) = true
      · rw [if_pos h]
        have hp : LitTable.internPack ⟨lits, lookup, neg⟩ l =
            (l, ⟨lits, lookup, neg⟩) := by
          unfold LitTable.internPack
          rw [if_pos h]
        rw [internPackFold, hp]
        exact ih (acc.push l) lits lookup neg
      · rw [if_neg h]
        cases hl : lookup.get? l.lit with
        | some i =>
            have hp : LitTable.internPack ⟨lits, lookup, neg⟩ l =
                (⟨i, l.lit⟩, ⟨lits, lookup, neg⟩) := by
              unfold LitTable.internPack LitTable.intern
              rw [if_neg h, hl]
            rw [internPackFold, hp]
            exact ih (acc.push ⟨i, l.lit⟩) lits lookup neg
        | none =>
            have hp : LitTable.internPack ⟨lits, lookup, neg⟩ l =
                (⟨lits.size, l.lit⟩,
                  ⟨lits.push l.lit, lookup.insert l.lit lits.size, neg.push 0⟩) := by
              unfold LitTable.internPack LitTable.intern
              rw [if_neg h, hl]
            rw [internPackFold, hp]
            exact ih (acc.push ⟨lits.size, l.lit⟩) (lits.push l.lit)
              (lookup.insert l.lit lits.size) (neg.push 0)

/-- Tail-recursive runtime twin of `internPacks`. -/
def LitTable.internPacksFast (T : LitTable) (ls : Array PLit) :
    Array PLit × LitTable :=
  internPackListFast ls.toList #[] T.lits T.lookup T.neg

/-- The fast hinted array fold is the reference one. -/
theorem LitTable.internPacksFast_eq (T : LitTable) (ls : Array PLit) :
    T.internPacksFast ls = T.internPacks ls := by
  unfold internPacksFast internPacks
  exact LitTable.internPackListFast_eq ls.toList #[] T.lits T.lookup T.neg

/-! ## Evaluation bridge -/

/-- `Clause.SatisfiedBy` unfolds to the existence of a true literal. -/
theorem Clause.satisfiedBy_iff {c : Clause} {a : Assignment} :
    c.SatisfiedBy a ↔ ∃ l, l ∈ c ∧ l.eval a = some true := Iff.rfl

end LeanFzn.Engine

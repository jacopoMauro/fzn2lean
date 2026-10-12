/-
File: LeanFzn/Solver/UIP/Proofs/EmissionVocabulary.lean
emission vocabulary of the retained kit; owner C1)

Purpose: the honest per-family producer of `UnitEmissionVocabulary`
(`Proofs/SupportedDatabaseFacts.lean` §5) for the registered kit
`dcs.filterMap propagatorOfProved` over `unitFamilyB` constraints.

THE HONEST DECOMPOSITION (land-accepted audit, session 11): the pool half
of the emission vocabulary is NOT free. The bound families emit the
constraint's OWN constant (`leConstHi i c` emits `posLe i c`,
`leConstLo i c` emits `negLe i (c-1)`, `ltConstHi i c` emits
`posLe i (c-1)`, `ltConstLo i c` emits `negLe i c`, `constEq i (.int k)`
emits `posLe i k` or `negLe i (k-1)`), so a fixed box's `threshPool`
(`SchedulerVocabulary`) must carry the constraint's threshold. The
constraint-side representative condition is `ThresholdsPooled` below: the
exact conjuncts the registered emission equations require, nothing more.

  * §1 the pool bridges: a threshold representative at a real slot is a
    pooled order atom (`posLe`/`negLe` at `threshPool` membership), and
    the BOOLEAN row is unconditional in the representative sense — a
    Boolean pin atom is pooled at EVERY domain
    (`pooledEmission_constEqBool_slot`, reused from
    `CanonicalTrailVocabulary.boolEq_mem_slotAtomPool`); only the slot
    index must be in range (`pooledEmission_constEqBool`).
  * §2 `ThresholdsPooled` (the residual, named and refutable — §4).
  * §3 `unitEmissionVocabulary_proved_of_thresholds`: the per-family
    dispatch, each family's pool conjunct discharged from its own `run`
    equation plus its `ThresholdsPooled` row.
  * §4 the kernel witness that the residual is REAL:
    `emitted_threshold_not_pooled` — `LeanFzn.Solver.Propagation.propLeConstHi` at the box
    `[[1, 5]]` emits `posLe 0 3`, which is not pooled.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.EmissionVocabulary` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
The C2 residual (site inhabitedness etc.) is stated in
`Proofs/TrailVocabularyProducers.lean` §4.
-/

import LeanFzn.Solver.UIP.Proofs.CanonicalTrailVocabulary
import LeanFzn.Solver.UIP.Proofs.DomExplained
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The pool bridges -/

/-- A nonempty box read names an in-range slot (the box-side form of
`getD_ne_nil_lt` used by the threshold bridges). -/
theorem threshold_slot_lt {orig : List Domain} {i : Nat} {c : Int}
    (h : c ∈ threshPool (orig.getD i [])) : i < orig.length := by
  have hne : orig.getD i [] ≠ [] := by
    intro hnil
    rw [hnil] at h
    simp [threshPool, vocabDomInts] at h
  exact getD_ne_nil_lt hne

/-- **THE POSITIVE-THRESHOLD POOL BRIDGE**: a `threshPool` representative
of a real slot is a pooled positive order literal. -/
theorem posLe_mem_litPool_of_thresh {orig : List Domain} {i : Nat} {c : Int}
    (h : c ∈ threshPool (orig.getD i [])) : posLe i c ∈ litPool orig := by
  have hi : i < orig.length := threshold_slot_lt h
  have ha : Atom.intLe i c ∈ slotAtomPool i (orig.getD i []) :=
    List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨c, h, rfl⟩))
  show posLit (Atom.intLe i c) ∈ litPool orig
  exact posLit_mem (List.mem_append_left _
    (slotAtomPool_mem_atomPoolBase hi ha))

/-- **THE NEGATIVE-THRESHOLD POOL BRIDGE**: the same for the negative
polarity (`negLe` — the `x > k` shape the lo-bound families emit). -/
theorem negLe_mem_litPool_of_thresh {orig : List Domain} {i : Nat} {c : Int}
    (h : c ∈ threshPool (orig.getD i [])) : negLe i c ∈ litPool orig := by
  have hi : i < orig.length := threshold_slot_lt h
  have ha : Atom.intLe i c ∈ slotAtomPool i (orig.getD i []) :=
    List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨c, h, rfl⟩))
  show negLit (Atom.intLe i c) ∈ litPool orig
  exact negLit_mem (List.mem_append_left _
    (slotAtomPool_mem_atomPoolBase hi ha))

/-- THE UNCONDITIONAL BOOLEAN ROW (domain-level form): both polarities of a
Boolean pin atom are pooled at EVERY domain — unlike the order atoms, no
value representative condition arises. This is what makes the `constEq`
Boolean family's pool half free of any threshold obligation; only the slot
index must be a real box slot. -/
theorem pooledEmission_constEqBool_slot (s : Nat) (d : Domain) (b : Bool) :
    Atom.boolEq s b ∈ slotAtomPool s d :=
  boolEq_mem_slotAtomPool s d b

/-- THE UNCONDITIONAL BOOLEAN ROW (literal-level form): at an in-range
slot, the Boolean emission literal `posBool i b` is pooled — for EVERY
domain at that slot (`pooledEmission_constEqBool_slot`). No threshold
representative is consumed; the only obligation is `i < orig.length`. -/
theorem pooledEmission_constEqBool {orig : List Domain} {i : Nat}
    (hi : i < orig.length) (b : Bool) : posBool i b ∈ litPool orig := by
  have ha : Atom.boolEq i b ∈ slotAtomPool i (orig.getD i []) :=
    pooledEmission_constEqBool_slot i (orig.getD i []) b
  show posLit (Atom.boolEq i b) ∈ litPool orig
  exact posLit_mem (List.mem_append_left _
    (slotAtomPool_mem_atomPoolBase hi ha))

/-! ## §2 The threshold-representative condition (the residual) -/

/-- **THE CONSTRAINT-SIDE REPRESENTATIVE CONDITION.** For every supported
constraint, the threshold(s) its registered `run` emits at its slot must
be `threshPool` representatives of that slot's box domain. Rows (all
vacuous unless the constraint has the shape):

  * `leConstHi i c` consumes `c` (emits `posLe i c`, conflict `[posLe i c]`);
  * `leConstLo i c` consumes `c - 1` (emits `negLe i (c - 1)`);
  * `ltConstHi i c` consumes `c - 1` (emits `posLe i (c - 1)`);
  * `ltConstLo i c` consumes `c` (emits `negLe i c`);
  * `constEq i (.int k)` consumes BOTH `k` and `k - 1` (the two bound
    arms of its `firstEvent`);
  * `constEq i (.bool b)` consumes NO threshold — only the slot range
    (`pooledEmission_constEqBool`), which is the unconditional row.

The condition is REFUTABLE (§4) and is exactly the C2 pool residual
(`Proofs/SupportedDatabaseFacts.lean` §7 item 1): a real LeanFzn.Solver's box
usually does NOT carry every constraint constant in its `threshPool`. -/
def ThresholdsPooled (orig : List Domain) (dcs : List DomConstraint) : Prop :=
  ∀ dc ∈ dcs,
    (∀ i c, dc = .leConstHi i c → c ∈ threshPool (orig.getD i [])) ∧
    (∀ i c, dc = .leConstLo i c → (c - 1) ∈ threshPool (orig.getD i [])) ∧
    (∀ i c, dc = .ltConstHi i c → (c - 1) ∈ threshPool (orig.getD i [])) ∧
    (∀ i c, dc = .ltConstLo i c → c ∈ threshPool (orig.getD i [])) ∧
    (∀ i k, dc = .constEq i (.int k) →
      k ∈ threshPool (orig.getD i []) ∧
        (k - 1) ∈ threshPool (orig.getD i [])) ∧
    (∀ i b, dc = .constEq i (.bool b) → i < orig.length)

/-! ## §3 The per-family producers

The conflict halves invert through the landed `narrowHi_conflict_inv` /
`narrowLo_conflict_inv` (`Proofs/Theory.lean`: the only conflict exit is
the nogood itself); the implied halves through `narrowHi_implied_inv` /
`narrowLo_implied_inv` (`Proofs/ConstFamilies.lean`). -/

/-- The `leConstHi` family's emission vocabulary (the pool half from the
threshold row). -/
theorem emissionVocabulary_leConstHi {orig : List Domain} {i : Nat} {c : Int}
    (hthr : c ∈ threshPool (orig.getD i [])) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLeConstHi st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLeConstHi st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c)
      (ng := [posLe i c]) hrun
    subst hl
    exact ⟨posLe i c, by rw [hcl], rfl, posLe_norm i c,
      posLe_mem_litPool_of_thresh hthr⟩
  · intro st c' hrun
    have hrun' : narrowHi st i c [posLe i c] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowHi_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨posLe i c, rfl, posLe_norm i c,
      posLe_mem_litPool_of_thresh hthr⟩

/-- The `leConstLo` family's emission vocabulary. -/
theorem emissionVocabulary_leConstLo {orig : List Domain} {i : Nat} {c : Int}
    (hthr : (c - 1) ∈ threshPool (orig.getD i [])) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLeConstLo st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLeConstLo st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c)
      (ng := [negLe i (c - 1)]) hrun
    subst hl
    exact ⟨negLe i (c - 1), by rw [hcl], rfl, negLe_norm i (c - 1),
      negLe_mem_litPool_of_thresh hthr⟩
  · intro st c' hrun
    have hrun' : narrowLo st i c [negLe i (c - 1)] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowLo_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨negLe i (c - 1), rfl, negLe_norm i (c - 1),
      negLe_mem_litPool_of_thresh hthr⟩

/-- The `ltConstHi` family's emission vocabulary. -/
theorem emissionVocabulary_ltConstHi {orig : List Domain} {i : Nat} {c : Int}
    (hthr : (c - 1) ∈ threshPool (orig.getD i [])) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLtConstHi st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLtConstHi st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c - 1)
      (ng := [posLe i (c - 1)]) hrun
    subst hl
    exact ⟨posLe i (c - 1), by rw [hcl], rfl, posLe_norm i (c - 1),
      posLe_mem_litPool_of_thresh hthr⟩
  · intro st c' hrun
    have hrun' : narrowHi st i (c - 1) [posLe i (c - 1)] = .conflict c' :=
      hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowHi_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨posLe i (c - 1), rfl, posLe_norm i (c - 1),
      posLe_mem_litPool_of_thresh hthr⟩

/-- The `ltConstLo` family's emission vocabulary. -/
theorem emissionVocabulary_ltConstLo {orig : List Domain} {i : Nat} {c : Int}
    (hthr : c ∈ threshPool (orig.getD i [])) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLtConstLo st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLtConstLo st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c + 1)
      (ng := [negLe i c]) hrun
    have hlc : l = negLe i c := by
      simpa only [show c + 1 - 1 = c by omega] using hl
    exact ⟨negLe i c, by rw [hcl], hlc, negLe_norm i c,
      negLe_mem_litPool_of_thresh hthr⟩
  · intro st c' hrun
    have hrun' : narrowLo st i (c + 1) [negLe i c] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowLo_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨negLe i c, rfl, negLe_norm i c,
      negLe_mem_litPool_of_thresh hthr⟩

/-- The `constEq` integer family's emission vocabulary (both bound arms;
both thresholds from the row). -/
theorem emissionVocabulary_constEqInt {orig : List Domain} {i : Nat} {k : Int}
    (hthr₁ : k ∈ threshPool (orig.getD i []))
    (hthr₂ : (k - 1) ∈ threshPool (orig.getD i [])) :
    (∀ st l r, LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    rcases narrowHi_or_narrowLo_of_firstEvent hrun with h | h
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := k)
        (ng := [posLe i k]) h
      subst hl
      exact ⟨posLe i k, by rw [hcl], rfl, posLe_norm i k,
        posLe_mem_litPool_of_thresh hthr₁⟩
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := k)
        (ng := [negLe i (k - 1)]) h
      subst hl
      exact ⟨negLe i (k - 1), by rw [hcl], rfl, negLe_norm i (k - 1),
        negLe_mem_litPool_of_thresh hthr₂⟩
  · intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    have hmem := firstEvent_mem _ _ hrun
    rcases hmem with hstab | hmem
    · cases hstab
    · rcases List.mem_cons.mp hmem with h1 | h2
      · have hc : narrowHi st i k [posLe i k] = .conflict c' := h1.symm
        obtain ⟨-, -, -, -, -, heq⟩ := narrowHi_conflict_inv hc
        subst heq
        exact Or.inr ⟨posLe i k, rfl, posLe_norm i k,
          posLe_mem_litPool_of_thresh hthr₁⟩
      · have hc : narrowLo st i k [negLe i (k - 1)] = .conflict c' :=
          (List.mem_singleton.mp h2).symm
        obtain ⟨-, -, -, -, -, heq⟩ := narrowLo_conflict_inv hc
        subst heq
        exact Or.inr ⟨negLe i (k - 1), rfl, negLe_norm i (k - 1),
          negLe_mem_litPool_of_thresh hthr₂⟩

/-- The `constEq` Boolean family's emission vocabulary — the UNCONDITIONAL
row: the only premise is the slot range, and the pin is pooled at every
domain (`pooledEmission_constEqBool`). -/
theorem emissionVocabulary_constEqBool {orig : List Domain} {i : Nat}
    (hi : i < orig.length) (b : Bool) :
    (∀ st l r, LeanFzn.Solver.Propagation.propConstEq st i (.bool b) = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propConstEq st i (.bool b) = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig) := by
  constructor
  · intro st l r hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun
      · cases hrun
      · injection hrun with hl hr
        refine ⟨posBool i b, ?_, hl.symm, posBool_norm i b,
          pooledEmission_constEqBool hi b⟩
        rw [← hr]
    · cases hrun
  · intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun <;> cases hrun
    · injection hrun with hc
      subst hc
      exact Or.inr ⟨posBool i b, rfl, posBool_norm i b,
        pooledEmission_constEqBool hi b⟩

/-- **THE C1 KIT EMISSION VOCABULARY**: the registered kit over a
`unitFamilyB`-supported constraint base has the pooled emission vocabulary
as soon as the constraint-side threshold rows hold. Every family's pool
conjunct is discharged from its OWN `run` equation (narrowHi/narrowLo
inversions + the constraints of §2); the unit shape reuses the landed
per-family `UnitEvidence`. -/
theorem unitEmissionVocabulary_proved_of_thresholds {orig : List Domain}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hthr : ThresholdsPooled orig dcs) :
    UnitEmissionVocabulary orig (dcs.filterMap propagatorOfProved) := by
  constructor
  · intro p hpm st l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hrows := hthr dc hdc
    have hs := hSupp dc hdc
    cases dc with
    | leConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_leConstHi (hrows.1 i c rfl)).1 st l r hrun
    | leConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_leConstLo (hrows.2.1 i c rfl)).1 st l r hrun
    | ltConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_ltConstHi (hrows.2.2.1 i c rfl)).1 st l r hrun
    | ltConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_ltConstLo (hrows.2.2.2.1 i c rfl)).1 st l r hrun
    | constEq i v =>
        cases v with
        | int k =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            obtain ⟨hk, hk1⟩ := hrows.2.2.2.2.1 i k rfl
            exact (emissionVocabulary_constEqInt hk hk1).1 st l r hrun
        | bool b =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabulary_constEqBool
              (hrows.2.2.2.2.2 i b rfl) b).1 st l r hrun
        | setOfInt x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
        | array x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
    | eqSlot i j => simp [unitFamilyB] at hs
    | neSlot i j => simp [unitFamilyB] at hs
    | leSlot i j => simp [unitFamilyB] at hs
    | plusSlot i j k => simp [unitFamilyB] at hs
    | allDiff is => simp [unitFamilyB] at hs
    | timesSlot i j k => simp [unitFamilyB] at hs
    | minSlot i j k => simp [unitFamilyB] at hs
    | maxSlot i j k => simp [unitFamilyB] at hs
    | absSlot i k => simp [unitFamilyB] at hs
    | linEq coeffs is b => simp [unitFamilyB] at hs
    | linLe coeffs is b => simp [unitFamilyB] at hs
    | ltSlot i j => simp [unitFamilyB] at hs
    | boolNotSlot i j => simp [unitFamilyB] at hs
    | boolAndSlot i j k => simp [unitFamilyB] at hs
    | boolOrSlot i j k => simp [unitFamilyB] at hs
  · intro p hpm st c' hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hrows := hthr dc hdc
    have hs := hSupp dc hdc
    cases dc with
    | leConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_leConstHi (hrows.1 i c rfl)).2 st c' hrun
    | leConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_leConstLo (hrows.2.1 i c rfl)).2 st c' hrun
    | ltConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_ltConstHi (hrows.2.2.1 i c rfl)).2 st c' hrun
    | ltConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabulary_ltConstLo (hrows.2.2.2.1 i c rfl)).2 st c' hrun
    | constEq i v =>
        cases v with
        | int k =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            obtain ⟨hk, hk1⟩ := hrows.2.2.2.2.1 i k rfl
            exact (emissionVocabulary_constEqInt hk hk1).2 st c' hrun
        | bool b =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabulary_constEqBool
              (hrows.2.2.2.2.2 i b rfl) b).2 st c' hrun
        | setOfInt x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
        | array x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
    | eqSlot i j => simp [unitFamilyB] at hs
    | neSlot i j => simp [unitFamilyB] at hs
    | leSlot i j => simp [unitFamilyB] at hs
    | plusSlot i j k => simp [unitFamilyB] at hs
    | allDiff is => simp [unitFamilyB] at hs
    | timesSlot i j k => simp [unitFamilyB] at hs
    | minSlot i j k => simp [unitFamilyB] at hs
    | maxSlot i j k => simp [unitFamilyB] at hs
    | absSlot i k => simp [unitFamilyB] at hs
    | linEq coeffs is b => simp [unitFamilyB] at hs
    | linLe coeffs is b => simp [unitFamilyB] at hs
    | ltSlot i j => simp [unitFamilyB] at hs
    | boolNotSlot i j => simp [unitFamilyB] at hs
    | boolAndSlot i j k => simp [unitFamilyB] at hs
    | boolOrSlot i j k => simp [unitFamilyB] at hs

/-! ## §4 The residual is real (kernel witness)

The audit's counterexample, kernel-checked: `LeanFzn.Solver.Propagation.propLeConstHi` at a slot
whose domain is the sparse two-value set `{1, 5}` emits `posLe 0 3`, and
`3` is NOT a `threshPool` representative of `{1, 5}` (whose pool is
`{1, 5, 0, 4}`), so `posLe 0 3 ∉ litPool [[1, 5]]`. Hence
`ThresholdsPooled` is a genuine constraint-side input, not a consequence
of `unitFamilyB` + `UnitRunProfile`. -/

/-- The witness state: one slot with the sparse domain `{1, 5}`. -/
def witnessSparseState : State where
  domains := [[Value.int 1, Value.int 5]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- **THE C1 RESIDUAL WITNESS**: the retained kit's `leConstHi` emission at
the sparse box `[[1, 5]]` is `posLe 0 3`, not pooled at that box. -/
theorem emitted_threshold_not_pooled :
    (∃ st : State,
        LeanFzn.Solver.Propagation.propLeConstHi st 0 3 = .implied (posLe 0 3) { clause := [posLe 0 3] }) ∧
      posLe 0 3 ∉ litPool [[Value.int 1, Value.int 5]] := by
  constructor
  · refine ⟨witnessSparseState, rfl⟩
  · show posLe 0 3 ∉ litPool [[Value.int 1, Value.int 5]]
    decide

/-- The same witness in `ThresholdsPooled` form: the singleton constraint
base `[.leConstHi 0 3]` at the sparse box violates the residual. -/
theorem thresholdsPooled_false_sparse :
    ¬ ThresholdsPooled [[Value.int 1, Value.int 5]] [.leConstHi 0 3] := by
  intro h
  have hrow : (3 : Int) ∈ threshPool [Value.int 1, Value.int 5] :=
    (h _ (List.mem_singleton_self _)).1 0 3 rfl
  revert hrow
  show ¬ ((3 : Int) ∈ threshPool [Value.int 1, Value.int 5])
  decide

/-! ## §5 The finite pool extension (C1 round 3): `litPoolExt`

THE HONEST ROUTE (route (b) of the C1 task). The §4 witness shows the
registered kit's pool half is NOT free at the fixed `litPool`: `leConstHi
i c` emits `posLe i c` for the constraint's OWN `c`. The fix that keeps
every landed rank/closure statement intact is an APPEND-ONLY extension:
`litPoolExt orig dcs` = `SchedulerVocabulary.litPoolWith` over the atom
pool extended by the constraint-side atoms (`constraintAtoms`), so

  * `litPool ⊆ litPoolExt` (`litPool_mem_litPoolExt`),
  * `litPoolExt` is finite with an explicit bound
    (`litPoolExt_length_le'`), flip/norm/negate-closed (inherited from
    `litPoolWith`), and
  * the pooled-emission discipline holds at `litPoolExt` for the
    registered kit from `hSupp` ALONE — no `ThresholdsPooled`, no assumed
    membership (`emissionVocabularyAt_litPoolExt`), via the pool-parametric
    form `EmissionVocabularyAt` (`SupportedDatabaseFacts` §8) and the §5
    per-family producers below.

`litPool` itself is NOT redefined; the extended pool is a new name whose
consumers (the sorted-shape rank key C2 owes) re-key through the two
bridges. `unitEmissionVocabulary_proved_of_thresholds` (§3) remains the
answer for callers that DO have `ThresholdsPooled`. -/

/-- The constraint-side ATOMS contributed to the extended pool: exactly
the atoms whose literals the registered `run` equations can emit (the
positive/negative order pins of the constraint's own constants and the
Boolean pin of a Boolean `constEq`). All other families contribute
nothing. -/
def valueAtoms (i : Nat) : Value → List Atom
  | .int k => [Atom.intLe i k, Atom.intLe i (k - 1)]
  | .bool b => [Atom.boolEq i b]
  | _ => []

/-- The per-constraint atom contribution (see `valueAtoms`). -/
def constraintAtoms : DomConstraint → List Atom
  | .leConstHi i c => [Atom.intLe i c]
  | .leConstLo i c => [Atom.intLe i (c - 1)]
  | .ltConstHi i c => [Atom.intLe i (c - 1)]
  | .ltConstLo i c => [Atom.intLe i c]
  | .constEq i v => valueAtoms i v
  | _ => []

/-- The constraint atoms of a whole constraint base. -/
def constraintAtomPool : List DomConstraint → List Atom
  | [] => []
  | dc :: dcs => constraintAtoms dc ++ constraintAtomPool dcs

/-- The constraint-side LITERALS contributed to the extended pool (the
emitted-literal dictionary the row condition speaks about): the exact
literal forms the §6 per-family producers consume. -/
def valueLits (i : Nat) : Value → List Literal
  | .int k => [posLe i k, negLe i (k - 1)]
  | .bool b => [posBool i b]
  | _ => []

/-- The per-constraint emitted-literal forms. -/
def emissionLits : DomConstraint → List Literal
  | .leConstHi i c => [posLe i c]
  | .leConstLo i c => [negLe i (c - 1)]
  | .ltConstHi i c => [posLe i (c - 1)]
  | .ltConstLo i c => [negLe i c]
  | .constEq i v => valueLits i v
  | _ => []

/-- **THE EXTENDED LITERAL POOL**: the box pool plus the constraint-side
constant literals. Append-only: `litPool` is untouched. -/
def litPoolExt (orig : List Domain) (dcs : List DomConstraint) : List Literal :=
  litPoolWith (constraintAtomPool dcs) orig

/-- The base pool embeds into the extended pool. -/
theorem litPool_mem_litPoolExt {orig : List Domain} {dcs : List DomConstraint}
    {l : Literal} (h : l ∈ litPool orig) : l ∈ litPoolExt orig dcs :=
  litPool_mem_litPoolWith (extra := constraintAtomPool dcs) h

/-- An atom of a constraint of the base belongs to the constraint atoms. -/
theorem mem_constraintAtomPool {dcs : List DomConstraint} {dc : DomConstraint}
    {a : Atom} (hdc : dc ∈ dcs) (ha : a ∈ constraintAtoms dc) :
    a ∈ constraintAtomPool dcs := by
  induction dcs with
  | nil => cases hdc
  | cons dc' dcs ih =>
      rcases List.mem_cons.mp hdc with rfl | hdc
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (ih hdc)

/-- A supported constraint's atom belongs to the extended extras. -/
theorem constraintAtoms_mem_extras {dcs : List DomConstraint}
    {dc : DomConstraint} (hdc : dc ∈ dcs) {a : Atom}
    (ha : a ∈ constraintAtoms dc) :
    a ∈ atomExtras (constraintAtomPool dcs) :=
  List.mem_append_left _ (mem_constraintAtomPool hdc ha)

/-- Per-constraint atom-count bound (at most the two `constEq` bound
atoms). -/
theorem valueAtoms_length_le (i : Nat) (v : Value) :
    (valueAtoms i v).length ≤ 2 := by
  cases v <;> simp [valueAtoms]

theorem constraintAtoms_length_le (dc : DomConstraint) :
    (constraintAtoms dc).length ≤ 2 := by
  cases dc <;> simp [constraintAtoms, valueAtoms_length_le]

/-- Finiteness of the constraint atoms: at most two per constraint. -/
theorem constraintAtomPool_length_le (dcs : List DomConstraint) :
    (constraintAtomPool dcs).length ≤ 2 * dcs.length := by
  induction dcs with
  | nil => simp [constraintAtomPool]
  | cons dc dcs ih =>
      have h := constraintAtoms_length_le dc
      simp only [constraintAtomPool, List.length_append, List.length_cons]
      omega

/-- Finiteness of the extended pool (the bound the extended rank/closure
key needs), in the `litPoolWith` shape. -/
theorem litPoolExt_length_le (orig : List Domain) (dcs : List DomConstraint) :
    (litPoolExt orig dcs).length
      ≤ 4 * (atomPool orig).length + 8 * (constraintAtomPool dcs).length :=
  litPoolWith_length_le' (constraintAtomPool dcs) orig

/-- **THE FINITENESS FACT** in box/constraint terms: the extended pool has
at most twenty-four literals per stored domain value, sixteen per slot,
and sixteen per constraint. -/
theorem litPoolExt_length_le' (orig : List Domain) (dcs : List DomConstraint) :
    (litPoolExt orig dcs).length
      ≤ 24 * (orig.map (fun d => d.length)).sum + 16 * orig.length
        + 16 * dcs.length := by
  have h := litPoolExt_length_le orig dcs
  have ha := atomPool_length_le orig
  have hcp := constraintAtomPool_length_le dcs
  omega

/-- **THE EMISSION-LITERAL POOL PRODUCER**: every emitted-literal form of
a constraint of the base is an extended-pool literal — from membership
alone, NO threshold condition. This is the per-family dictionary
(positive block for `posLe`/`posBool`, negative block for `negLe`). -/
theorem emissionLits_mem_litPoolExt {orig : List Domain}
    {dcs : List DomConstraint} {dc : DomConstraint} (hdc : dc ∈ dcs)
    {l : Literal} (hl : l ∈ emissionLits dc) :
    l ∈ litPoolExt orig dcs := by
  cases dc with
  | leConstHi i c =>
      simp only [emissionLits, List.mem_singleton] at hl
      subst hl
      show posLit (Atom.intLe i c) ∈ litPoolWith (constraintAtomPool dcs) orig
      exact posLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
        (constraintAtoms_mem_extras hdc (by simp [constraintAtoms])))
  | leConstLo i c =>
      simp only [emissionLits, List.mem_singleton] at hl
      subst hl
      show negLit (Atom.intLe i (c - 1)) ∈ litPoolWith (constraintAtomPool dcs) orig
      exact negLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
        (constraintAtoms_mem_extras hdc (by simp [constraintAtoms])))
  | ltConstHi i c =>
      simp only [emissionLits, List.mem_singleton] at hl
      subst hl
      show posLit (Atom.intLe i (c - 1)) ∈ litPoolWith (constraintAtomPool dcs) orig
      exact posLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
        (constraintAtoms_mem_extras hdc (by simp [constraintAtoms])))
  | ltConstLo i c =>
      simp only [emissionLits, List.mem_singleton] at hl
      subst hl
      show negLit (Atom.intLe i c) ∈ litPoolWith (constraintAtomPool dcs) orig
      exact negLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
        (constraintAtoms_mem_extras hdc (by simp [constraintAtoms])))
  | constEq i v =>
      cases v with
      | int k =>
          simp only [emissionLits, valueLits] at hl
          rcases List.mem_cons.mp hl with hl | hl
          · subst hl
            show posLit (Atom.intLe i k) ∈ litPoolWith (constraintAtomPool dcs) orig
            exact posLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
              (constraintAtoms_mem_extras hdc (by simp [constraintAtoms, valueAtoms])))
          · simp only [List.mem_singleton] at hl
            subst hl
            show negLit (Atom.intLe i (k - 1)) ∈ litPoolWith (constraintAtomPool dcs) orig
            exact negLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
              (constraintAtoms_mem_extras hdc (by simp [constraintAtoms, valueAtoms])))
      | bool b =>
          simp only [emissionLits, valueLits, List.mem_singleton] at hl
          subst hl
          show posLit (Atom.boolEq i b) ∈ litPoolWith (constraintAtomPool dcs) orig
          exact posLit_mem_litPoolWith (atomExtras_mem_atomPoolWith
            (constraintAtoms_mem_extras hdc (by simp [constraintAtoms, valueAtoms])))
      | setOfInt x => simp [emissionLits, valueLits] at hl
      | array x => simp [emissionLits, valueLits] at hl
  | eqSlot i j => simp [emissionLits] at hl
  | neSlot i j => simp [emissionLits] at hl
  | leSlot i j => simp [emissionLits] at hl
  | plusSlot i j k => simp [emissionLits] at hl
  | allDiff is => simp [emissionLits] at hl
  | timesSlot i j k => simp [emissionLits] at hl
  | minSlot i j k => simp [emissionLits] at hl
  | maxSlot i j k => simp [emissionLits] at hl
  | absSlot i k => simp [emissionLits] at hl
  | linEq coeffs is b => simp [emissionLits] at hl
  | linLe coeffs is b => simp [emissionLits] at hl
  | ltSlot i j => simp [emissionLits] at hl
  | boolNotSlot i j => simp [emissionLits] at hl
  | boolAndSlot i j k => simp [emissionLits] at hl
  | boolOrSlot i j k => simp [emissionLits] at hl

/-! ## §6 The pool-parametric per-family producers

The §3 family lemmas with the pool membership taken DIRECTLY (instead of
derived from `ThresholdsPooled`): the same `narrowHi`/`narrowLo`
inversions, the pool fact abstracted. Instantiating `hmem` at
`litPoolExt`'s emitted-literals bridge (§5) or at the §1 threshold
bridges recovers both routes from ONE proof. -/

/-- Pool-parametric `leConstHi` emission vocabulary. -/
theorem emissionVocabularyAt_leConstHi {P : List Literal} {i : Nat} {c : Int}
    (hmem : posLe i c ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLeConstHi st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLeConstHi st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c)
      (ng := [posLe i c]) hrun
    subst hl
    exact ⟨posLe i c, by rw [hcl], rfl, posLe_norm i c, hmem⟩
  · intro st c' hrun
    have hrun' : narrowHi st i c [posLe i c] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowHi_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨posLe i c, rfl, posLe_norm i c, hmem⟩

/-- Pool-parametric `leConstLo` emission vocabulary. -/
theorem emissionVocabularyAt_leConstLo {P : List Literal} {i : Nat} {c : Int}
    (hmem : negLe i (c - 1) ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLeConstLo st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLeConstLo st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c)
      (ng := [negLe i (c - 1)]) hrun
    subst hl
    exact ⟨negLe i (c - 1), by rw [hcl], rfl, negLe_norm i (c - 1), hmem⟩
  · intro st c' hrun
    have hrun' : narrowLo st i c [negLe i (c - 1)] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowLo_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨negLe i (c - 1), rfl, negLe_norm i (c - 1), hmem⟩

/-- Pool-parametric `ltConstHi` emission vocabulary. -/
theorem emissionVocabularyAt_ltConstHi {P : List Literal} {i : Nat} {c : Int}
    (hmem : posLe i (c - 1) ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLtConstHi st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLtConstHi st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c - 1)
      (ng := [posLe i (c - 1)]) hrun
    subst hl
    exact ⟨posLe i (c - 1), by rw [hcl], rfl, posLe_norm i (c - 1), hmem⟩
  · intro st c' hrun
    have hrun' : narrowHi st i (c - 1) [posLe i (c - 1)] = .conflict c' :=
      hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowHi_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨posLe i (c - 1), rfl, posLe_norm i (c - 1), hmem⟩

/-- Pool-parametric `ltConstLo` emission vocabulary. -/
theorem emissionVocabularyAt_ltConstLo {P : List Literal} {i : Nat} {c : Int}
    (hmem : negLe i c ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propLtConstLo st i c = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propLtConstLo st i c = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c + 1)
      (ng := [negLe i c]) hrun
    have hlc : l = negLe i c := by
      simpa only [show c + 1 - 1 = c by omega] using hl
    exact ⟨negLe i c, by rw [hcl], hlc, negLe_norm i c, hmem⟩
  · intro st c' hrun
    have hrun' : narrowLo st i (c + 1) [negLe i c] = .conflict c' := hrun
    obtain ⟨-, -, -, -, -, hc⟩ := narrowLo_conflict_inv hrun'
    subst hc
    exact Or.inr ⟨negLe i c, rfl, negLe_norm i c, hmem⟩

/-- Pool-parametric `constEq` integer emission vocabulary. -/
theorem emissionVocabularyAt_constEqInt {P : List Literal} {i : Nat} {k : Int}
    (hmem₁ : posLe i k ∈ P) (hmem₂ : negLe i (k - 1) ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    rcases narrowHi_or_narrowLo_of_firstEvent hrun with h | h
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := k)
        (ng := [posLe i k]) h
      subst hl
      exact ⟨posLe i k, by rw [hcl], rfl, posLe_norm i k, hmem₁⟩
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := k)
        (ng := [negLe i (k - 1)]) h
      subst hl
      exact ⟨negLe i (k - 1), by rw [hcl], rfl, negLe_norm i (k - 1), hmem₂⟩
  · intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    have hmem := firstEvent_mem _ _ hrun
    rcases hmem with hstab | hmem
    · cases hstab
    · rcases List.mem_cons.mp hmem with h1 | h2
      · have hc : narrowHi st i k [posLe i k] = .conflict c' := h1.symm
        obtain ⟨-, -, -, -, -, heq⟩ := narrowHi_conflict_inv hc
        subst heq
        exact Or.inr ⟨posLe i k, rfl, posLe_norm i k, hmem₁⟩
      · have hc : narrowLo st i k [negLe i (k - 1)] = .conflict c' :=
          (List.mem_singleton.mp h2).symm
        obtain ⟨-, -, -, -, -, heq⟩ := narrowLo_conflict_inv hc
        subst heq
        exact Or.inr ⟨negLe i (k - 1), rfl, negLe_norm i (k - 1), hmem₂⟩

/-- Pool-parametric `constEq` Boolean emission vocabulary. -/
theorem emissionVocabularyAt_constEqBool {P : List Literal} {i : Nat}
    {b : Bool} (hmem : posBool i b ∈ P) :
    (∀ st l r, LeanFzn.Solver.Propagation.propConstEq st i (.bool b) = .implied l r →
      ∃ q : Literal,
        r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ P) ∧
    (∀ st c', LeanFzn.Solver.Propagation.propConstEq st i (.bool b) = .conflict c' →
      c' = [] ∨
        ∃ q : Literal, c' = [q] ∧ q = q.norm ∧ q.norm ∈ P) := by
  constructor
  · intro st l r hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun
      · cases hrun
      · injection hrun with hl hr
        refine ⟨posBool i b, ?_, hl.symm, posBool_norm i b, hmem⟩
        rw [← hr]
    · cases hrun
  · intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun <;> cases hrun
    · injection hrun with hc
      subst hc
      exact Or.inr ⟨posBool i b, rfl, posBool_norm i b, hmem⟩

/-- **THE ROW CONDITION** of the extended route: every constraint of the
base contributes only extended-pool literals. Unlike `ThresholdsPooled`
this is a POOL-side condition — at `P := litPoolExt orig dcs` it holds
UNCONDITIONALLY (§5's dictionary). -/
def EmissionRowsIn (pool : List Literal) (dcs : List DomConstraint) : Prop :=
  ∀ dc ∈ dcs, ∀ l ∈ emissionLits dc, l ∈ pool

/-- The extended pool satisfies the row condition unconditionally. -/
theorem emissionRowsIn_litPoolExt (orig : List Domain) (dcs : List DomConstraint) :
    EmissionRowsIn (litPoolExt orig dcs) dcs :=
  fun _dc hdc _l hl => emissionLits_mem_litPoolExt (orig := orig) hdc hl

/-- **THE GENERIC KIT PRODUCER**: the registered kit over a
`unitFamilyB`-supported base has the pooled emission vocabulary at ANY
pool satisfying the row condition — the §3 dispatch with the pool fact
abstracted (every family's shape is its own `run` equation; the unit
shape is the landed `UnitEvidence` family half re-derived through the
pool-parametric lemmas of §6). -/
theorem emissionVocabularyAt_of_rows {pool : List Literal}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hrows : EmissionRowsIn pool dcs) :
    EmissionVocabularyAt pool (dcs.filterMap propagatorOfProved) := by
  constructor
  · intro p hpm st l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hrow := hrows dc hdc
    have hs := hSupp dc hdc
    cases dc with
    | leConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_leConstHi
          (hrow (posLe i c) (by simp [emissionLits]))).1 st l r hrun
    | leConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_leConstLo
          (hrow (negLe i (c - 1)) (by simp [emissionLits]))).1 st l r hrun
    | ltConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_ltConstHi
          (hrow (posLe i (c - 1)) (by simp [emissionLits]))).1 st l r hrun
    | ltConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_ltConstLo
          (hrow (negLe i c) (by simp [emissionLits]))).1 st l r hrun
    | constEq i v =>
        cases v with
        | int k =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabularyAt_constEqInt
              (hrow (posLe i k) (by simp [emissionLits, valueLits]))
              (hrow (negLe i (k - 1))
                (by simp [emissionLits, valueLits]))).1 st l r hrun
        | bool b =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabularyAt_constEqBool
              (hrow (posBool i b)
                (by simp [emissionLits, valueLits]))).1 st l r hrun
        | setOfInt x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
        | array x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
    | eqSlot i j => simp [unitFamilyB] at hs
    | neSlot i j => simp [unitFamilyB] at hs
    | leSlot i j => simp [unitFamilyB] at hs
    | plusSlot i j k => simp [unitFamilyB] at hs
    | allDiff is => simp [unitFamilyB] at hs
    | timesSlot i j k => simp [unitFamilyB] at hs
    | minSlot i j k => simp [unitFamilyB] at hs
    | maxSlot i j k => simp [unitFamilyB] at hs
    | absSlot i k => simp [unitFamilyB] at hs
    | linEq coeffs is b => simp [unitFamilyB] at hs
    | linLe coeffs is b => simp [unitFamilyB] at hs
    | ltSlot i j => simp [unitFamilyB] at hs
    | boolNotSlot i j => simp [unitFamilyB] at hs
    | boolAndSlot i j k => simp [unitFamilyB] at hs
    | boolOrSlot i j k => simp [unitFamilyB] at hs
  · intro p hpm st c' hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hrow := hrows dc hdc
    have hs := hSupp dc hdc
    cases dc with
    | leConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_leConstHi
          (hrow (posLe i c) (by simp [emissionLits]))).2 st c' hrun
    | leConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_leConstLo
          (hrow (negLe i (c - 1)) (by simp [emissionLits]))).2 st c' hrun
    | ltConstHi i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_ltConstHi
          (hrow (posLe i (c - 1)) (by simp [emissionLits]))).2 st c' hrun
    | ltConstLo i c =>
        simp only [propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact (emissionVocabularyAt_ltConstLo
          (hrow (negLe i c) (by simp [emissionLits]))).2 st c' hrun
    | constEq i v =>
        cases v with
        | int k =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabularyAt_constEqInt
              (hrow (posLe i k) (by simp [emissionLits, valueLits]))
              (hrow (negLe i (k - 1))
                (by simp [emissionLits, valueLits]))).2 st c' hrun
        | bool b =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            exact (emissionVocabularyAt_constEqBool
              (hrow (posBool i b)
                (by simp [emissionLits, valueLits]))).2 st c' hrun
        | setOfInt x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
        | array x =>
            simp only [propagatorOfProved, Option.some.injEq] at hprop
            subst hprop
            simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
            cases hrun
    | eqSlot i j => simp [unitFamilyB] at hs
    | neSlot i j => simp [unitFamilyB] at hs
    | leSlot i j => simp [unitFamilyB] at hs
    | plusSlot i j k => simp [unitFamilyB] at hs
    | allDiff is => simp [unitFamilyB] at hs
    | timesSlot i j k => simp [unitFamilyB] at hs
    | minSlot i j k => simp [unitFamilyB] at hs
    | maxSlot i j k => simp [unitFamilyB] at hs
    | absSlot i k => simp [unitFamilyB] at hs
    | linEq coeffs is b => simp [unitFamilyB] at hs
    | linLe coeffs is b => simp [unitFamilyB] at hs
    | ltSlot i j => simp [unitFamilyB] at hs
    | boolNotSlot i j => simp [unitFamilyB] at hs
    | boolAndSlot i j k => simp [unitFamilyB] at hs
    | boolOrSlot i j k => simp [unitFamilyB] at hs

/-- **THE C1 EXTENDED-POOL EMISSION PRODUCER (route (b))**: the registered
kit over a `unitFamilyB`-supported base has the pooled emission vocabulary
at the EXTENDED pool — from `hSupp` ALONE (no `ThresholdsPooled`, no
assumed emitted-threshold membership). -/
theorem emissionVocabularyAt_litPoolExt {orig : List Domain}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    EmissionVocabularyAt (litPoolExt orig dcs) (dcs.filterMap propagatorOfProved) :=
  emissionVocabularyAt_of_rows hSupp (emissionRowsIn_litPoolExt orig dcs)

/-- The landed `UnitEmissionVocabulary` transports to the extended pool
(`litPool ⊆ litPoolExt`) — so every existing per-family producer keeps
working verbatim at the extended key. -/
theorem emissionVocabularyAt_litPoolExt_of_unit {orig : List Domain}
    {props : List Propagator} {dcs : List DomConstraint}
    (h : UnitEmissionVocabulary orig props) :
    EmissionVocabularyAt (litPoolExt orig dcs) props :=
  emissionVocabularyAt_mono (fun _l hl => litPool_mem_litPoolExt hl)
    (unitEmissionVocabulary_iff_at.mp h)

/-- The extended producer's `UnitEmissionVocabulary`-shaped consumer twin:
the same statement in the landed `halignDB` chain's field shape, at the
extended pool (C2 re-keys `halignDB` through this). -/
theorem unitEmissionVocabulary_proved_litPoolExt {orig : List Domain}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    EmissionVocabularyAt (litPoolExt orig dcs)
      (dcs.filterMap propagatorOfProved) :=
  emissionVocabularyAt_litPoolExt hSupp

end LeanFzn.Solver.UIP

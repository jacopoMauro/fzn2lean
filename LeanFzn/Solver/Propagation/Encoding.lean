/-
File: LeanFzn/Solver/Propagation/Encoding.lean

Purpose:
  L0.1 semantic foundation of the LCG LeanFzn.Solver:

  * literal algebra laws — negation involutivity, negation-evaluation
    duality, and normalization preserving evaluation;
  * the integer order encoding, made precise: the atoms of a slot `s`
    are `s ≤ k` for every integer bound `k` (Boolean slots included via
    the shared 0/1 integer view), positive literals assert the bound and
    negative literals deny it; equality `s = i` reconstructs as the
    adjacent pair `s ≤ i ∧ ¬(s ≤ i−1)`; adjacent bounds relate by the
    monotonicity laws; a switching point exists in every
    false-below/true-above total segment;
  * `Problem.WellFormed` and `Propagators.WellFormedFor`;
  * the two-way correspondence between complete core assignments and
    complete, order- and Boolean-consistent literal valuations over the
    encoding, carved per-slot at domain values.

  Precision note (why domains stay in `LeanFzn.Solver.Propagation.State`): pure order atoms
  cannot carve holes out of non-contiguous domains — over `{1, 5}` the
  literals `¬(s ≤ 2)` and `s ≤ 3` are jointly satisfiable though no
  domain value sits in `(2, 3)`. Hence the backward correspondence
  carves each slot at a domain value (`CarvesAt`), the engine pins
  extrema with root facts (`LeanFzn.Solver.UIP.Engine.rootFacts`), and exact interior
  carving is deferred to value-removal literals (L0.6).

Dependencies:
  - LeanFzn.Solver.Propagation.Operations: literal vocabulary, `Literal.eval`/`Atom.eval`,
    the shared integer view `Value.intView`, and `slotInt`.
  - LeanFzn.Solver.Propagation.Invariants: `Clause.EntailedBy` and `ProblemSolution`,
    used by `Problem.WellFormed`.

DAG:
  LeanFzn.Solver.Propagation.Operations + LeanFzn.Solver.Propagation.Invariants -> LeanFzn.Solver.Propagation.Encoding
  -> LeanFzn.Solver.Proofs.* (future transition obligations)
-/

import LeanFzn.Solver.Propagation.Operations
import LeanFzn.Solver.Propagation.Invariants
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Literal algebra laws -/

/-- Negating a literal twice restores it. -/
theorem Literal.negate_negate (l : Literal) : l.negate.negate = l := by
  cases l
  simp [Literal.negate]

/-- Negating a literal flips evaluation. -/
theorem Literal.eval_negate (l : Literal) (a : Assignment) :
    l.negate.eval a = (l.eval a).map (! ·) := by
  cases l with
  | mk atom positive =>
    cases positive <;>
      simp [Literal.eval, Literal.negate, Function.comp_def]

/-- A literal is true exactly when its negation is false. -/
theorem Literal.eval_negate_false_iff (l : Literal) (a : Assignment) :
    l.negate.eval a = some true ↔ l.eval a = some false := by
  cases l with
  | mk atom positive =>
    cases positive <;>
      simp [Literal.eval, Literal.negate, Function.comp_def]

/-- The engine's canonical Boolean form preserves evaluation. -/
theorem Literal.norm_eval (l : Literal) (a : Assignment) :
    l.norm.eval a = l.eval a := by
  cases l with
  | mk atom positive =>
    cases atom with
    | boolEq s b =>
      cases positive with
      | true => rfl
      | false =>
        simp only [Literal.norm]
        show (Literal.mk (Atom.boolEq s (!b)) true).eval a =
              (Literal.mk (Atom.boolEq s b) false).eval a
        simp only [Literal.eval, Atom.eval]
        cases h : a[s]? with
        | none => rfl
        | some val =>
          cases val with
          | bool x => cases x <;> cases b <;> simp
          | int x => simp only [h]; rfl
          | setOfInt x => simp only [h]; rfl
          | array x => simp only [h]; rfl
    | intLe s k => cases positive <;> rfl
    | intNe s k => cases positive <;> rfl

/-! ## Order-encoding evaluation

The atoms of an integer-like slot `s` are `s ≤ k` for all `k : Int`. On a
complete assignment they evaluate at the slot's integer view. -/

/-- Positive order literals evaluate at the integer view. -/
theorem eval_posLe (a : Assignment) (s : Nat) (k : Int) :
    (posLe s k).eval a = (slotInt a s).map fun i => decide (i ≤ k) := by
  simp [Literal.eval, posLe, Atom.eval, Function.comp_def, slotInt]

/-- Negative order literals evaluate at the negated view. -/
theorem eval_negLe (a : Assignment) (s : Nat) (k : Int) :
    (negLe s k).eval a = (slotInt a s).map fun i => !(decide (i ≤ k)) := by
  simp [Literal.eval, negLe, Atom.eval, Function.comp_def, slotInt]

/-- A positive order literal holds iff the slot's integer view is at most
    the bound. -/
theorem eval_posLe_iff (a : Assignment) (s : Nat) (k : Int) :
    (posLe s k).eval a = some true ↔ ∃ i, slotInt a s = some i ∧ i ≤ k := by
  rw [eval_posLe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    exact ⟨i, hi, of_decide_eq_true hdec⟩
  · rintro ⟨i, hi, hik⟩
    exact ⟨i, hi, decide_eq_true hik⟩

/-- A negative order literal holds iff the slot's integer view exceeds
    the bound. -/
theorem eval_negLe_iff (a : Assignment) (s : Nat) (k : Int) :
    (negLe s k).eval a = some true ↔ ∃ i, slotInt a s = some i ∧ k < i := by
  rw [eval_negLe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    rw [Bool.not_eq_true'] at hdec
    have : ¬ i ≤ k := of_decide_eq_false hdec
    exact ⟨i, hi, by omega⟩
  · rintro ⟨i, hi, hik⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_true']
    exact decide_eq_false (by omega)

/-- Bridge: a positive order literal evaluates like its atom. -/
theorem eval_posLe_eq_atom (a : Assignment) (s : Nat) (k : Int) :
    (posLe s k).eval a = Atom.eval (.intLe s k) a := by
  simp only [Literal.eval, posLe]
  cases Atom.eval (.intLe s k) a <;> rfl

/-- Bridge: a positive Boolean literal evaluates like its atom. -/
theorem eval_posBool_eq_atom (a : Assignment) (s : Nat) (b : Bool) :
    (posBool s b).eval a = Atom.eval (.boolEq s b) a := by
  simp only [Literal.eval, posBool]
  cases Atom.eval (.boolEq s b) a <;> rfl

/-- Positive order literals are monotone in the bound: asserting `k`
    implies asserting every weaker bound `k ≤ k'`. -/
theorem eval_posLe_mono (a : Assignment) (s : Nat) {k k' : Int} (hk : k ≤ k') :
    (posLe s k).eval a = some true → (posLe s k').eval a = some true := by
  rw [eval_posLe_iff, eval_posLe_iff]
  rintro ⟨i, hi, hik⟩
  exact ⟨i, hi, by omega⟩

/-- Negative order literals are antitone in the bound: denial of the
    tighter bound `k` (`s > k`) implies denial of every weaker bound
    `k'` with `k ≤ k'`. -/
theorem eval_negLe_mono (a : Assignment) (s : Nat) {k k' : Int} (hk : k' ≤ k) :
    (negLe s k).eval a = some true → (negLe s k').eval a = some true := by
  rw [eval_negLe_iff, eval_negLe_iff]
  rintro ⟨i, hi, hik⟩
  exact ⟨i, hi, by omega⟩

/-- Positive value-removal literals evaluate at the integer view. -/
theorem eval_posNe (a : Assignment) (s : Nat) (k : Int) :
    (posNe s k).eval a = (slotInt a s).map fun i => decide (i ≠ k) := by
  simp [Literal.eval, posNe, Atom.eval, Function.comp_def, slotInt]

/-- Negative value-removal literals evaluate at the negated view. -/
theorem eval_negNe (a : Assignment) (s : Nat) (k : Int) :
    (negNe s k).eval a = (slotInt a s).map fun i => !(decide (i ≠ k)) := by
  simp [Literal.eval, negNe, Atom.eval, Function.comp_def, slotInt]

/-- A positive value-removal literal holds iff the slot's integer view
    differs from the removed value. -/
theorem eval_posNe_iff (a : Assignment) (s : Nat) (k : Int) :
    (posNe s k).eval a = some true ↔ ∃ i, slotInt a s = some i ∧ i ≠ k := by
  rw [eval_posNe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    exact ⟨i, hi, (of_decide_eq_true hdec)⟩
  · rintro ⟨i, hi, hik⟩
    exact ⟨i, hi, decide_eq_true hik⟩

/-- A negative value-removal literal holds iff the slot's integer view
    equals the removed value. -/
theorem eval_negNe_iff (a : Assignment) (s : Nat) (k : Int) :
    (negNe s k).eval a = some true ↔ ∃ i, slotInt a s = some i ∧ i = k := by
  rw [eval_negNe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, hdec⟩
    refine ⟨i, hi, ?_⟩
    cases hbb : decide (i ≠ k) with
    | true =>
        rw [hbb] at hdec
        simp at hdec
    | false =>
        have hnn : ¬ (i ≠ k) := of_decide_eq_false hbb
        omega
  · rintro ⟨i, hi, hik⟩
    refine ⟨i, hi, ?_⟩
    rw [Bool.not_eq_true']
    exact decide_eq_false (by omega)

/-- Bridge: a positive value-removal literal evaluates like its atom. -/
theorem eval_posNe_eq_atom (a : Assignment) (s : Nat) (k : Int) :
    (posNe s k).eval a = Atom.eval (.intNe s k) a := by
  simp only [Literal.eval, posNe]
  cases Atom.eval (.intNe s k) a <;> rfl

/-- A positive value-removal literal is FALSE at a slot whose integer
    view is exactly the removed value. -/
theorem posNe_eval_false_of_eq {a : Assignment} {s : Nat} {k i : Int}
    (hsi : slotInt a s = some i) (hik : i = k) :
    (posNe s k).eval a = some false := by
  rw [eval_posNe, hsi]
  show some (decide (i ≠ k)) = some false
  have hdi : decide (i ≠ k) = false := decide_eq_false (by omega)
  rw [hdi]

/-- Equality reconstruction: the adjacent pair pins the integer view. -/
theorem slotInt_eq_of_adjacent (a : Assignment) (s : Nat) (i : Int)
    (hlo : (negLe s (i - 1)).eval a = some true)
    (hhi : (posLe s i).eval a = some true) :
    slotInt a s = some i := by
  rw [eval_negLe_iff] at hlo
  rw [eval_posLe_iff] at hhi
  obtain ⟨j, hj, hjlo⟩ := hlo
  obtain ⟨j', hj', hjhi⟩ := hhi
  rw [hj] at hj'
  rw [Option.some.injEq] at hj'
  subst hj'
  rw [hj]
  congr 1
  omega

/-! ## Slot-local atom meaning -/

/-- The slot an atom constrains. -/
def Atom.slot : Atom → Nat
  | .boolEq s _ => s
  | .intLe s _ => s
  | .intNe s _ => s

/-- Evaluate an atom at a single value — the slot-local meaning of the
    atom, before assignment lookup. -/
def Atom.evalAtValue (atom : Atom) (val : Value) : Option Bool :=
  match atom with
  | .boolEq _ b =>
      match val with
      | .bool x => some (x == b)
      | _ => none
  | .intLe _ k => (Value.intView val).map fun i => decide (i ≤ k)
  | .intNe _ k => (Value.intView val).map fun i => decide (i ≠ k)

/-- Boolean atoms hold iff the slot carries the expected Boolean. -/
theorem eval_posBool_iff (a : Assignment) (s : Nat) (b : Bool) :
    (posBool s b).eval a = some true ↔ a[s]? = some (.bool b) := by
  simp only [Literal.eval, posBool, Atom.eval]
  cases h : a[s]? with
  | none => simp
  | some val =>
    cases val with
    | bool x =>
      simp only [h, beq_iff_eq, Option.some.injEq, Value.bool.injEq]
      cases x <;> cases b <;> simp
    | int x => simp [h]
    | setOfInt x => simp [h]
    | array x => simp [h]

/-- On an in-range slot, atom evaluation is the slot-local meaning at the
    slot's value. -/
theorem Atom.eval_eq_evalAtValue (atom : Atom) (a : Assignment)
    (hslot : atom.slot < a.length) :
    atom.eval a = Atom.evalAtValue atom a[atom.slot] := by
  cases atom with
  | boolEq s b =>
    have hs : s < a.length := hslot
    show (match a[s]? with
          | some (.bool actual) => some (actual == b)
          | _ => none)
        = Atom.evalAtValue (Atom.boolEq s b) a[s]
    simp only [Atom.evalAtValue]
    rw [List.getElem?_eq_getElem hs]
    cases a[s]'hs <;> rfl
  | intLe s k =>
    have hs : s < a.length := hslot
    show (slotInt a s).map (fun i => decide (i ≤ k))
        = Atom.evalAtValue (Atom.intLe s k) a[s]
    simp only [Atom.evalAtValue, slotInt]
    rw [List.getElem?_eq_getElem hs]
    rfl
  | intNe s k =>
    have hs : s < a.length := hslot
    show (slotInt a s).map (fun i => decide (i ≠ k))
        = Atom.evalAtValue (Atom.intNe s k) a[s]
    simp only [Atom.evalAtValue, slotInt]
    rw [List.getElem?_eq_getElem hs]
    rfl

/-! ## Well-formedness of encoded problems -/

/-- An atom fits a compiled domain list: its slot is in range and the
    slot's values all have the shape the atom measures — Booleans for
    equality atoms, an integer view for order atoms. -/
def Atom.WellFormedIn (atom : Atom) (domains : List Domain) : Prop :=
  match atom with
  | .boolEq slot _ => slot < domains.length ∧
      ∀ v ∈ domains.getD slot Dom.empty, ∃ b, v = .bool b
  | .intLe slot _ => slot < domains.length ∧
      ∀ v ∈ domains.getD slot Dom.empty, Value.intView v ≠ none
  | .intNe slot _ => slot < domains.length ∧
      ∀ v ∈ domains.getD slot Dom.empty, Value.intView v ≠ none

/-- Every literal of a clause fits the domains. -/
def Clause.WellFormedIn (clause : Clause) (domains : List Domain) : Prop :=
  ∀ literal ∈ clause, literal.atom.WellFormedIn domains

/-- Structural and semantic well-formedness of an encoded problem:
    name/domain count agreement, slot/type agreement of every atom in
    every initial clause, and entailment of every initial clause by the
    internal problem semantics. -/
def Problem.WellFormed (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop) : Prop :=
  problem.names.length = problem.domains.length ∧
    (∀ clause ∈ problem.clauses, clause.WellFormedIn problem.domains) ∧
    (∀ clause ∈ problem.clauses,
      Clause.EntailedBy problem constraintHolds clause)

/-- Registered propagators only watch declared, well-formed atoms. -/
def Propagators.WellFormedFor (props : List Propagator) (domains : List Domain) :
    Prop :=
  ∀ p ∈ props, ∀ atom ∈ p.watches, atom.WellFormedIn domains

/-! ## Valuations over the encoding

A valuation assigns truth values to atoms. Completeness and consistency
make it behave like an assignment: every well-formed atom is decided,
order atoms vary monotonically, and Boolean atoms are unique. -/

/-- Partial truth assignment to atoms. -/
abbrev Valuation := Atom → Option Bool

/-- Every well-formed atom of the domain list receives a truth value. -/
def Valuation.TotalOn (v : Valuation) (domains : List Domain) : Prop :=
  ∀ atom, atom.WellFormedIn domains → v atom ≠ none

/-- Order atoms vary monotonically: truth flows upward in the bound and
    falsity flows downward. -/
def Valuation.OrderConsistent (v : Valuation) : Prop :=
  ∀ s : Nat, ∀ k k' : Int, k ≤ k' →
    (v (.intLe s k) = some true → v (.intLe s k') = some true) ∧
    (v (.intLe s k') = some false → v (.intLe s k) = some false)

/-- At most one Boolean value per slot is asserted true. -/
def Valuation.BoolConsistent (v : Valuation) : Prop :=
  ∀ s : Nat, ∀ b b' : Bool,
    v (.boolEq s b) = some true → v (.boolEq s b') = some true → b = b'

/-- Evaluation is total for every well-formed atom of a fitting
    assignment (PLAN L0.1 totality obligation). -/
theorem Atom.eval_ne_none_of_fits (atom : Atom) (a : Assignment)
    (domains : List Domain) (hfit : a.Fits domains)
    (hwf : atom.WellFormedIn domains) : atom.eval a ≠ none := by
  obtain ⟨hlen, hmem⟩ := hfit
  cases atom with
  | boolEq s b =>
    obtain ⟨hslot, hbools⟩ := hwf
    have hs : s < a.length := by rw [hlen]; omega
    have hq : a[s]? = some a[s] := (List.getElem?_eq_some_iff).mpr ⟨hs, rfl⟩
    have hin : a[s] ∈ domains.getD s Dom.empty := hmem s a[s] hq
    obtain ⟨x, hx⟩ := hbools a[s] hin
    have hx' : a[s]? = some (.bool x) := by rw [hq, hx]
    show (match a[s]? with
          | some (.bool actual) => some (actual == b)
          | _ => none) ≠ none
    rw [hx']
    simp
  | intLe s k =>
    obtain ⟨hslot, hints⟩ := hwf
    have hs : s < a.length := by rw [hlen]; omega
    have hq : a[s]? = some a[s] := (List.getElem?_eq_some_iff).mpr ⟨hs, rfl⟩
    have hin : a[s] ∈ domains.getD s Dom.empty := hmem s a[s] hq
    show (slotInt a s).map (fun i => decide (i ≤ k)) ≠ none
    rw [slotInt, hq]
    cases hv : Value.intView a[s] with
    | none => exact absurd hv (hints a[s] hin)
    | some j => simp [hv]
  | intNe s k =>
    obtain ⟨hslot, hints⟩ := hwf
    have hs : s < a.length := by rw [hlen]; omega
    have hq : a[s]? = some a[s] := (List.getElem?_eq_some_iff).mpr ⟨hs, rfl⟩
    have hin : a[s] ∈ domains.getD s Dom.empty := hmem s a[s] hq
    show (slotInt a s).map (fun i => decide (i ≠ k)) ≠ none
    rw [slotInt, hq]
    cases hv : Value.intView a[s] with
    | none => exact absurd hv (hints a[s] hin)
    | some j => simp [hv]

/-- The valuation induced by a fitting assignment is total. -/
theorem Valuation.totalOn_of_fits (a : Assignment) (domains : List Domain)
    (hfit : a.Fits domains) :
    Valuation.TotalOn (fun atom => atom.eval a) domains :=
  fun atom hwf => Atom.eval_ne_none_of_fits atom a domains hfit hwf

/-- Falsity flows downward: denial of a weaker bound implies denial of
    every tighter bound. -/
theorem eval_posLe_false_of (a : Assignment) (s : Nat) {k k' : Int}
    (hk : k ≤ k') (h : (posLe s k').eval a = some false) :
    (posLe s k).eval a = some false := by
  have h' : (posLe s k').eval a = (slotInt a s).map fun i => decide (i ≤ k') :=
    eval_posLe a s k'
  rw [h'] at h
  rw [eval_posLe]
  cases hv : slotInt a s with
  | none => rw [hv] at h; simp at h
  | some j =>
    rw [Option.map_eq_some_iff] at h
    obtain ⟨j2, hj2, hdecb⟩ := h
    have hnot2 : ¬ j2 ≤ k' := by
      intro hle
      have hd : decide (j2 ≤ k') = true := decide_eq_true hle
      rw [hd] at hdecb
      simp at hdecb
    rw [hv] at hj2
    rw [Option.some.injEq] at hj2
    subst hj2
    rw [Option.map_some]
    congr 1
    exact decide_eq_false (by omega)

/-- The valuation induced by any assignment is order-consistent. -/
theorem Valuation.orderConsistent_of_assignment (a : Assignment) :
    Valuation.OrderConsistent (fun atom => atom.eval a) := by
  intro s k k' hkk'
  constructor
  · intro h
    simp only [] at h ⊢
    rw [← eval_posLe_eq_atom a s k] at h
    rw [← eval_posLe_eq_atom a s k']
    exact eval_posLe_mono a s hkk' h
  · intro h
    simp only [] at h ⊢
    rw [← eval_posLe_eq_atom a s k'] at h
    rw [← eval_posLe_eq_atom a s k]
    exact eval_posLe_false_of a s hkk' h

/-- The valuation induced by any assignment is Boolean-consistent. -/
theorem Valuation.boolConsistent_of_assignment (a : Assignment) :
    Valuation.BoolConsistent (fun atom => atom.eval a) := by
  intro s b b' h h'
  simp only [] at h h' ⊢
  rw [← eval_posBool_eq_atom a s b] at h
  rw [← eval_posBool_eq_atom a s b'] at h'
  rw [eval_posBool_iff] at h
  rw [eval_posBool_iff] at h'
  rw [h] at h'
  simp only [Option.some.injEq, Value.bool.injEq] at h'
  exact h'

/-! ## The switching-point theorem

A valuation that denies the atom below an interval, asserts the top atom,
and is total inside it has a switching point whose adjacent atoms pin an
integer (`slotInt_eq_of_adjacent`). -/

private theorem switchingSearch (v : Valuation) (s : Nat) (lo hi : Int)
    (htrue : v (.intLe s hi) = some true)
    (htotal : ∀ k : Int, lo ≤ k → k ≤ hi → v (.intLe s k) ≠ none) :
    ∀ (fuel : Nat) (l : Int), lo ≤ l → l ≤ hi →
        v (.intLe s (l - 1)) = some false → (hi - l : Int) ≤ ↑fuel →
        ∃ i : Int, lo ≤ i ∧ i ≤ hi ∧
          v (.intLe s i) = some true ∧ v (.intLe s (i - 1)) = some false
  | 0, l, hlo, hhi, hlf, hfuel => by
      have hlh : l = hi := by omega
      subst hlh
      exact ⟨l, hlo, hhi, htrue, hlf⟩
  | fuel + 1, l, hlo, hhi, hlf, hfuel => by
      match hv : v (.intLe s l) with
      | some true => exact ⟨l, hlo, hhi, hv, hlf⟩
      | some false =>
          have hne : l ≠ hi := by
            intro he
            subst he
            rw [hv] at htrue
            simp at htrue
          have hv' : v (.intLe s (l + 1 - 1)) = some false := by
            have hnorm : (l + 1 - 1 : Int) = l := by omega
            rw [hnorm]
            exact hv
          exact switchingSearch v s lo hi htrue htotal fuel (l + 1)
            (by omega) (by omega) hv' (by omega)
      | none => exact absurd hv (htotal l hlo hhi)

/-- The switching-point theorem of the order encoding. -/
theorem exists_switching (v : Valuation) (s : Nat) (lo hi : Int)
    (hlohi : lo ≤ hi)
    (hfalse : v (.intLe s (lo - 1)) = some false)
    (htrue : v (.intLe s hi) = some true)
    (htotal : ∀ k : Int, lo ≤ k → k ≤ hi → v (.intLe s k) ≠ none) :
    ∃ i : Int, lo ≤ i ∧ i ≤ hi ∧
      v (.intLe s i) = some true ∧ v (.intLe s (i - 1)) = some false := by
  have hnng : (0 : Int) ≤ hi - lo := by omega
  have hcast : ((hi - lo).toNat : Int) = hi - lo := Int.toNat_of_nonneg hnng
  have hfuel : (hi - lo : Int) ≤ ((hi - lo).toNat : Int) := by
    omega
  exact switchingSearch v s lo hi htrue htotal (hi - lo).toNat lo
    (by omega : lo ≤ lo) hlohi hfalse hfuel

/-! ## The two-way correspondence -/

/-- A valuation carves slot `s` at value `val` when every atom about `s`
    has exactly its slot-local meaning at that value. -/
def CarvesAt (v : Valuation) (s : Nat) (val : Value) : Prop :=
  ∀ atom, atom.slot = s → v atom = Atom.evalAtValue atom val

/-- Forward correspondence: a fitting assignment carves its induced
    valuation on every in-range slot, carving at the slot's own value. -/
theorem carvesAt_of_fits (a : Assignment) (domains : List Domain)
    (hfit : a.Fits domains) {s : Nat} (hs : s < domains.length)
    {val : Value} (hval : a[s]? = some val) :
    CarvesAt (fun atom => atom.eval a) s val := by
  intro atom hslot
  have hlen : a.length = domains.length := hfit.1
  obtain ⟨he, hv⟩ : ∃ (he : s < a.length), a[s] = val := by
    rw [List.getElem?_eq_some_iff] at hval
    obtain ⟨he, hv⟩ := hval
    exact ⟨by rw [hlen] at *; omega, hv⟩
  subst hslot
  have hs' : atom.slot < a.length := he
  have hmain := Atom.eval_eq_evalAtValue atom a hs'
  show atom.eval a = Atom.evalAtValue atom val
  rw [hv] at hmain
  exact hmain

/-! ## The assignment construction

The backward correspondence builds the realizing assignment by classical
per-slot choice: every in-range slot picks a carving domain value
(`Classical.choose` over the per-slot existential, totalized by returning
any value with vacuous properties out of range, where `getD` is `[]`). -/

/-- Out of range, `getD` returns the empty domain. -/
private theorem getD_eq_empty_of_lt (l : List Domain) (s : Nat)
    (h : ¬ s < l.length) : l.getD s Dom.empty = Dom.empty := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none_iff.mpr (by omega)]
  rfl

/-- Slot-wise choice: the per-slot existential, totalized over all `s` by
        picking a vacuous witness out of range. -/
private noncomputable def slotPick (domains : List Domain) (v : Valuation)
    (hcarv : ∀ s, s < domains.length → ∃ val ∈ domains.getD s Dom.empty,
      CarvesAt v s val) (s : Nat) : Value :=
  (Classical.epsilon (fun val => val ∈ domains.getD s Dom.empty ∧ CarvesAt v s val))

private theorem slotPick_spec (domains : List Domain) (v : Valuation)
    (hcarv : ∀ s, s < domains.length → ∃ val ∈ domains.getD s Dom.empty,
      CarvesAt v s val) (s : Nat) (hs : s < domains.length) :
    slotPick domains v hcarv s ∈ domains.getD s Dom.empty ∧
      CarvesAt v s (slotPick domains v hcarv s) :=
  Classical.epsilon_spec (hcarv s hs)

/-- The realized assignment: one chosen value per slot position. -/
private noncomputable def pickAssignment (domains : List Domain)
    (v : Valuation)
    (hcarv : ∀ s, s < domains.length → ∃ val ∈ domains.getD s Dom.empty,
      CarvesAt v s val) : Assignment :=
  (List.range domains.length).map (slotPick domains v hcarv)

/-- Backward correspondence: a valuation carved on every slot by a
    domain value is realized by a fitting assignment that reproduces it
    on every well-formed atom. -/
theorem exists_fitting_of_carves (domains : List Domain) (v : Valuation)
    (hcarv : ∀ s, s < domains.length → ∃ val ∈ domains.getD s Dom.empty,
      CarvesAt v s val) :
    ∃ a, a.Fits domains ∧
      ∀ atom, atom.WellFormedIn domains → atom.eval a = v atom := by
  classical
  -- the hole is exactly the pick + Fits + reproduction assembly below
  refine ⟨pickAssignment domains v hcarv, ?_, ?_⟩
  · -- Fits: length matches; every value read is the chosen one, in-domain
    constructor
    · show (pickAssignment domains v hcarv).length = domains.length
      simp only [pickAssignment, List.length_map, List.length_range]
    · intro slot value hval
      have hlen : (pickAssignment domains v hcarv).length = domains.length := by
        simp only [pickAssignment, List.length_map, List.length_range]
      have hs : slot < domains.length := by
        rw [List.getElem?_eq_some_iff] at hval
        obtain ⟨he, _⟩ := hval
        rw [hlen] at he
        exact he
      have hmem := (slotPick_spec domains v hcarv slot hs).1
      show value ∈ domains.getD slot Dom.empty
      have hpickAt : (pickAssignment domains v hcarv)[slot]?
          = some (slotPick domains v hcarv slot) := by
        show (((List.range domains.length).map
            (slotPick domains v hcarv))[slot]?) = _
        rw [List.getElem?_map]
        rw [List.getElem?_range (by omega)]
        simp
      rw [hval] at hpickAt
      injection hpickAt with hvinj
      exact hvinj ▸ hmem
  · intro atom hwf
    -- reproduction: eval at the pick is the slot-local meaning, which the
    -- carving hypothesis identifies with the valuation
    have hslot : atom.slot < domains.length := by
      cases atom with
      | boolEq s b => obtain ⟨h1, _⟩ := hwf; exact h1
      | intLe s k => obtain ⟨h1, _⟩ := hwf; exact h1
      | intNe s k => obtain ⟨h1, _⟩ := hwf; exact h1
    have hlen : (pickAssignment domains v hcarv).length = domains.length := by
      simp only [pickAssignment, List.length_map, List.length_range]
    have hs' : atom.slot < (pickAssignment domains v hcarv).length := by
      rw [hlen]; exact hslot
    have hpickAt : (pickAssignment domains v hcarv)[atom.slot]?
        = some (slotPick domains v hcarv atom.slot) := by
      show (((List.range domains.length).map
          (slotPick domains v hcarv))[atom.slot]?) = _
      rw [List.getElem?_map]
      rw [List.getElem?_range (by omega)]
      simp
    obtain ⟨he, hv⟩ := List.getElem_of_getElem? hpickAt
    rw [Atom.eval_eq_evalAtValue atom (pickAssignment domains v hcarv) hs', hv]
    exact ((slotPick_spec domains v hcarv atom.slot hslot).2 atom rfl).symm

end LeanFzn.Solver.Propagation

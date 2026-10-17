/-
File: LeanFzn/Solver/Propagation/LcgAnalyzer.lean

Purpose (PLAN task R1a): the EXECUTABLE LCG first-UIP analyzer the
scheduler runs (`analyzeAtAllowance`, `ConflictResolution.lean`), with the
three R0 analyzer repairs ported from the prototype `Tests/UIP/LcgProto.lean`:

  root   a working-clause literal that is false under the ORIGINAL domains
         (`litFalseAtRoot`) is dropped like a level-0 falsifier;
  sem    the falsifier of a working literal `q` is the EARLIEST trail entry
         whose literal implies `¬q` (`impliesP`: order bounds, `intNe`
         against bounds, Booleans in their 0/1 order form); the learned
         literal is the negation of THAT entry's literal (LCG weakening:
         the learned clause stays entailed and literal-for-literal
         trail-falsified);
  cycle  the falsifier of a REASON literal is searched only among the
         entries strictly before the pivot being expanded (`bound`, a trail
         index); the initial conflict clause may use any entry.

Marks are trail INDICES. The pivot is the highest marked index; expanding it
sets the bound to that index, so the bound strictly decreases at every
expansion. The guard `boundOk` makes this decrease definitional, which is
what gives unconditional termination (`AnalysisCompletion.lean`): no
reachable-state premise is needed.

The historical analyzer of `TrailEval.lean` (`markLit`, `analyzeStep`,
`analyzeTrail`) is unchanged: it is the reference engine's
(`analyzeConflict`, `Reference/Engine.lean`) and is no longer called by the
scheduler.

Soundness of the semantic lookup (`impliesP_sound`) and of the root drop
(`litFalseAtRoot_sound`) are proved here at the literal-evaluation level.
One prototype bridge is deliberately NOT ported: a Boolean trail literal
is never used to falsify an INTEGER working literal (`impliesP`'s kind
guard), because on an assignment that stores an integer in that slot the
Boolean literal is undefined (`Literal.eval = none`), which would break the
entailment of the weakened learned literal.

Dependencies:
  - LeanFzn.Solver.Propagation.Encoding: `Atom.evalAtValue`, the literal
    algebra (`Literal.eval_negate`, `Literal.norm_eval`).
-/

import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Solver.Propagation.BoolImplication
open LeanFzn.Semantics LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## 1. Literal implication (fix `sem`) -/

/-- Booleans in their 0/1 order form: `b = true` is `x > 0`, `b = false` is
`x ≤ 0` (the `Value.intView` of a Boolean). Integer literals are unchanged. -/
def Literal.intForm (l : Literal) : Literal :=
  match l.atom with
  | .boolEq s b =>
      let pos : Literal := if b then negLe s 0 else posLe s 0
      if l.positive then pos else pos.negate
  | _ => l

/-- Is the literal's atom Boolean? -/
def Literal.boolKind (l : Literal) : Bool :=
  match l.atom with
  | .boolEq _ _ => true
  | _ => false

/-- Syntactic bound implication between order/value literals of one slot:
`t` implies `g` (identical to the harness' `impliesLit`). -/
def impliesLit (t g : Literal) : Bool :=
  if litEqB t g then true
  else if t.atom.slot != g.atom.slot then false
  else
    match t.atom, t.positive, g.atom, g.positive with
    | .intLe _ k, true, .intLe _ k', true => decide (k ≤ k')
    | .intLe _ k, true, .intNe _ v, true => decide (k < v)
    | .intLe _ k, false, .intLe _ k', false => decide (k' ≤ k)
    | .intLe _ k, false, .intNe _ v, true => decide (v ≤ k)
    | .intNe _ v, false, .intLe _ k, true => decide (v ≤ k)
    | .intNe _ v, false, .intLe _ k, false => decide (k < v)
    | .intNe _ v, false, .intNe _ w, true => decide (w ≠ v)
    | _, _, _, _ => false

/-- Every original value of the slot is a Boolean (so every fitting assignment
stores a Boolean there). -/
@[irreducible] def slotBoolB (orig : List Domain) (s : Nat) : Bool :=
  (orig.getD s []).all fun v => match v with | .bool _ => true | _ => false

/-- `t` implies `g`: identical literals, or bound implication of their 0/1
order forms — except that a Boolean `t` implies an integer `g` only when the
slot is Boolean in `orig` (R3; see the module header). -/
def impliesBase (orig : List Domain) (t g : Literal) : Bool :=
  litEqB t g || ((!t.boolKind || g.boolKind || slotBoolB orig t.atom.slot) &&
    impliesLit t.intForm g.intForm)

/-- Complete Boolean-slot implication extends the syntactic order relation. -/
def impliesP (orig : List Domain) (t g : Literal) : Bool :=
  impliesBase orig t g || boolSlotImp orig t g

theorem impliesP_cases {orig : List Domain} {t g : Literal}
    (h : impliesP orig t g = true) :
    impliesBase orig t g = true ∨ boolSlotImp orig t g = true :=
  Bool.or_eq_true_iff.mp h

theorem impliesP_of_base {orig : List Domain} {t g : Literal}
    (h : impliesBase orig t g = true) : impliesP orig t g = true := by
  simp [impliesP, h]

theorem impliesP_of_table {orig : List Domain} {t g : Literal}
    (h : boolSlotImp orig t g = true) : impliesP orig t g = true := by
  simp [impliesP, h]

theorem booleanSlotB_eq_slotBoolB (orig : List Domain) (s : Nat) :
    booleanSlotB orig s = slotBoolB orig s := by unfold booleanSlotB slotBoolB; rfl

/-- On a non-Boolean target slot the finite-table extension cannot fire. -/
theorem impliesP_base_of_target_nonBoolean {orig : List Domain} {t g : Literal}
    (hb : slotBoolB orig g.atom.slot = false) (h : impliesP orig t g = true) :
    impliesBase orig t g = true := by
  rcases impliesP_cases h with h | h
  · exact h
  · obtain ⟨hs, ht, _⟩ := boolSlotImp_elim h
    rw [hs, booleanSlotB_eq_slotBoolB, hb] at ht
    cases ht

/-! ## 2. Root facts (fix `root`) -/

/-- The literal is never TRUE at any value of the original domain of its
slot. An undefined evaluation (`none`) is not `some true`, so it counts as
false. -/
def litFalseAtRoot (orig : List Domain) (q : Literal) : Bool :=
  (orig.getD q.atom.slot []).all fun v =>
    match q.atom.evalAtValue v with
    | some b => (if q.positive then b else !b) == false
    | none => true

/-! ## 3. The falsifier search (fixes `sem`, `cycle`) -/

/-- The trail prefix a falsifier may be taken from: everything before the
bound (the whole trail when there is none). -/
def searchSpace (trail : List TrailEntry) : Option Nat → List TrailEntry
  | none => trail
  | some b => trail.take b

/-- The EARLIEST admissible trail index whose literal implies `¬q`. -/
def falsifierIdx (orig : List Domain) (trail : List TrailEntry) (bound : Option Nat)
    (q : Literal) : Option Nat :=
  (searchSpace trail bound).findIdx? fun e => impliesP orig e.literal q.negate.norm

/-- The expansion guard: the pivot lies strictly before the bound. -/
def boundOk : Option Nat → Nat → Bool
  | none, _ => true
  | some b, i => decide (i < b)

/-! ## 4. The analyzer state and its transition -/

/-- The analyzer worklist: clauses still to scan, the pivot literal to skip
in the reason being scanned, the falsifier bound (`none` while the conflict
clause is scanned; the pivot's index afterwards), the marked current-level
trail INDICES, and the below-level learned literals with their levels. -/
structure AnalyzerState where
  /-- clauses still to scan -/
  work : List Clause
  /-- the pivot of the reason currently being scanned (never re-marked) -/
  skip : Option Literal
  /-- falsifiers of the clause being scanned lie strictly before this index -/
  bound : Option Nat
  /-- marked current-level trail indices -/
  marks : List Nat
  /-- below-level learned literals with their levels -/
  learnt : List (Literal × Nat)

/-- The result of one analysis transition. -/
inductive AnalyzerStep where
  /-- the loop stops: `some` result, or `none` for an unsupported input -/
  | done (result : Option (List (Literal × Nat) × Literal))
  /-- the loop continues from the returned state -/
  | next (state : AnalyzerState)

/-- The initial analyzer state for a conflict clause. -/
def initAnalysisState (c : Clause) : AnalyzerState :=
  { work := [c], skip := none, bound := none, marks := [], learnt := [] }

/-- Mark working literal `q0` (normalized first): dropped when false at the
root; otherwise its earliest admissible falsifier entry `e` is dropped (level
0), marked (current level), rejected (above the current level) or recorded as
the learned literal `¬e.literal` (below the current level). -/
def markLitAt (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (bound : Option Nat) (marks : List Nat) (learnt : List (Literal × Nat))
    (q0 : Literal) : Option (List Nat × List (Literal × Nat)) :=
  let q := q0.norm
  if litFalseAtRoot orig q then some (marks, learnt)
  else
    match falsifierIdx orig trail bound q with
    | none => none
    | some i =>
        match trail[i]? with
        | none => none
        | some e =>
            let wl := e.literal.negate.norm
            if e.level == 0 then some (marks, learnt)
            else if e.level == lvl then
              (if marks.contains i then some (marks, learnt) else some (i :: marks, learnt))
            else if lvl < e.level then none
            else if learnt.any (fun p => litEqB p.1 wl) then some (marks, learnt)
            else some (marks, (wl, e.level) :: learnt)

/-- ONE analyzer transition: pivot selection/expansion on an empty worklist,
otherwise one scan (drop an empty clause, skip the pivot, or mark). -/
def analyzeNext (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (st : AnalyzerState) : AnalyzerStep :=
  match st.work with
  | [] =>
      match st.marks.max? with
      | none => .done none
      | some i =>
          match trail[i]? with
          | none => .done none
          | some e =>
              let marks' := st.marks.filter (· != i)
              if marks'.isEmpty then .done (some (st.learnt, e.literal))
              else if boundOk st.bound i then
                match e.reason with
                | none => .done none
                | some r =>
                    .next { work := [r.clause], skip := some e.literal,
                            bound := some i, marks := marks', learnt := st.learnt }
              else .done none
  | [] :: cs =>
      .next { work := cs, skip := st.skip, bound := st.bound, marks := st.marks,
              learnt := st.learnt }
  | (q0 :: qs) :: cs =>
      let q := q0.norm
      if skipEq st.skip q then
        .next { work := qs :: cs, skip := st.skip, bound := st.bound,
                marks := st.marks, learnt := st.learnt }
      else
        match markLitAt orig trail lvl st.bound st.marks st.learnt q with
        | none => .done none
        | some mp =>
            .next { work := qs :: cs, skip := st.skip, bound := st.bound,
                    marks := mp.1, learnt := mp.2 }

/-- The fuel loop over `analyzeNext`. The executable entry point runs it at
`analysisFuel`, which is PROVED sufficient for every input
(`AnalysisCompletion.lean`), so the fuel never cuts a run short. -/
def analyzeLoop (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (List (Literal × Nat) × Literal)
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext orig trail lvl st with
      | .done r => r
      | .next st' => analyzeLoop orig trail lvl fuel st'

/-! ## 5. The termination analyzerPotential -/

/-- The cost of one trail entry once its reason may be expanded. -/
def pivotEntryCost (e : TrailEntry) : Nat :=
  (match e.reason with
   | some r => r.clause.length
   | none => 0) + 2

/-- Worklist cost: one unit per clause plus one per literal. -/
def workCost (cs : List Clause) : Nat := cs.length + (cs.map List.length).sum

/-- The potential of the frontier: the cost of every entry still eligible
as a pivot. -/
def analyzerFrontierCost (trail : List TrailEntry) (bound : Option Nat) : Nat :=
  ((searchSpace trail bound).map pivotEntryCost).sum

/-- The termination potential: worklist plus frontier. -/
def analyzerPotential (trail : List TrailEntry) (st : AnalyzerState) : Nat :=
  workCost st.work + analyzerFrontierCost trail st.bound

/-- The executable allowance: the initial potential plus the terminal step. -/
def analysisFuel (trail : List TrailEntry) (c : Clause) : Nat :=
  analyzerPotential trail (initAnalysisState c) + 1

/-! ## 6. Literal-level soundness -/

theorem litEqB_iff {a b : Literal} : litEqB a b = true ↔ a = b := by
  simp [litEqB]

theorem Literal.intForm_slot (l : Literal) : l.intForm.atom.slot = l.atom.slot := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => cases b <;> cases pos <;> rfl
  | intLe s k => rfl
  | intNe s k => rfl

/-- Integer-atom evaluation, closed form. -/
theorem eval_intLe (s : Nat) (k : Int) (p : Bool) (a : Assignment) :
    (Literal.mk (.intLe s k) p).eval a
      = (slotInt a s).map (fun x => if p then decide (x ≤ k) else !decide (x ≤ k)) := by
  simp only [Literal.eval, Atom.eval, Option.map_map]
  rfl

theorem eval_intNe (s : Nat) (k : Int) (p : Bool) (a : Assignment) :
    (Literal.mk (.intNe s k) p).eval a
      = (slotInt a s).map (fun x => if p then decide (x ≠ k) else !decide (x ≠ k)) := by
  simp only [Literal.eval, Atom.eval, Option.map_map]
  rfl

/-- Bound implication is sound. -/
theorem impliesLit_sound {t g : Literal} (h : impliesLit t g = true)
    {a : Assignment} (ht : t.eval a = some true) : g.eval a = some true := by
  unfold impliesLit at h
  by_cases heq : litEqB t g = true
  · rw [litEqB_iff.mp heq] at ht; exact ht
  · rw [if_neg heq] at h
    by_cases hs : (t.atom.slot != g.atom.slot) = true
    · rw [if_pos hs] at h; cases h
    · rw [if_neg hs] at h
      have hslot : t.atom.slot = g.atom.slot := by simpa using hs
      obtain ⟨ta, tp⟩ := t
      obtain ⟨ga, gp⟩ := g
      cases ta <;> cases ga <;> cases tp <;> cases gp <;>
        simp only [Atom.slot] at hslot <;> simp at h <;> subst hslot <;>
        simp only [eval_intLe, eval_intNe] at ht ⊢ <;>
        (cases hx : slotInt a _ with
          | none => simp [hx] at ht
          | some x => simp [hx] at ht ⊢; omega)

/-- The order form preserves every DEFINED evaluation. -/
theorem Literal.intForm_eval {l : Literal} {a : Assignment} {x : Bool}
    (h : l.eval a = some x) : l.intForm.eval a = some x := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b =>
      simp only [Literal.eval, Atom.eval] at h
      cases hv : a[s]? with
      | none => simp [hv] at h
      | some v =>
          cases v with
          | bool y =>
              simp only [hv, Option.map_some, Option.some.injEq] at h
              subst h
              have hsi : slotInt a s = some (if y then 1 else 0) := by
                simp [slotInt, hv, Value.intView]
              cases b <;> cases pos <;> cases y <;>
                simp [Literal.intForm, negLe, posLe, Literal.negate, Literal.eval,
                  Atom.eval, hsi]
          | _ => simp [hv] at h
  | intLe s k => exact h
  | intNe s k => exact h

/-- A defined order form reads a defined integer view. -/
theorem slotInt_isSome_of_intForm {l : Literal} {a : Assignment} {x : Bool}
    (h : l.intForm.eval a = some x) : (slotInt a l.atom.slot).isSome := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b =>
      cases b <;> cases pos <;>
        simp only [Literal.intForm, negLe, posLe, Literal.negate, if_true,
          if_false, Bool.false_eq_true] at h <;>
        (simp only [Atom.slot]
         simp only [eval_intLe] at h
         cases hx : slotInt a s <;> simp_all)
  | intLe s k =>
      simp only [Literal.intForm, eval_intLe] at h
      simp only [Atom.slot]
      cases hx : slotInt a s <;> simp_all
  | intNe s k =>
      simp only [Literal.intForm, eval_intNe] at h
      simp only [Atom.slot]
      cases hx : slotInt a s <;> simp_all

/-- An integer literal is defined wherever its slot's integer view is. -/
theorem eval_isSome_of_int {l : Literal} {a : Assignment} (hk : l.boolKind = false)
    (h : (slotInt a l.atom.slot).isSome) : ∃ y, l.eval a = some y := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => simp [Literal.boolKind] at hk
  | intLe s k =>
      simp only [Atom.slot] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      exact ⟨_, by rw [eval_intLe, hx]; rfl⟩
  | intNe s k =>
      simp only [Atom.slot] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      exact ⟨_, by rw [eval_intNe, hx]; rfl⟩

/-- Two Boolean literals of one slot are defined together. -/
theorem eval_isSome_of_bool {l m : Literal} {a : Assignment}
    (hl : l.boolKind = true) (hm : m.boolKind = true)
    (hs : l.atom.slot = m.atom.slot) {x : Bool} (h : m.eval a = some x) :
    ∃ y, l.eval a = some y := by
  obtain ⟨la, lp⟩ := l
  obtain ⟨ma, mp⟩ := m
  cases la with
  | boolEq s b =>
      cases ma with
      | boolEq s' b' =>
          simp only [Atom.slot] at hs
          subst hs
          simp only [Literal.eval, Atom.eval] at h ⊢
          cases hv : a[s]? with
          | none => simp [hv] at h
          | some v =>
              cases v with
              | bool y => simp
              | _ => simp [hv] at h
      | _ => simp [Literal.boolKind] at hm
  | _ => simp [Literal.boolKind] at hl

/-- A Boolean literal on a slot Boolean in `orig` is defined wherever the slot's
integer view is. -/
theorem eval_isSome_of_slotBool {orig : List Domain} {t : Literal} {a : Assignment}
    (hk : t.boolKind = true) (hb : slotBoolB orig t.atom.slot = true) (hfit : a.Fits orig)
    (h : (slotInt a t.atom.slot).isSome) : ∃ y, t.eval a = some y := by
  obtain ⟨atom, pos⟩ := t
  cases atom with
  | boolEq s b =>
      simp only [Atom.slot, slotInt] at h hb
      cases hv : a[s]? with
      | none => simp [hv] at h
      | some v =>
          have hmem := hfit.2 s v hv
          unfold slotBoolB at hb
          have := List.all_eq_true.mp hb v hmem
          cases v with
          | bool y => exact ⟨if pos then y == b else !y == b, by simp [Literal.eval, Atom.eval, hv]⟩
          | _ => simp at this
  | _ => simp [Literal.boolKind] at hk

/-- SOUNDNESS OF THE SEMANTIC LOOKUP: if `t` implies `g`, then wherever `g`
is false, `t` is false (and in particular DEFINED). Applied with
`g = q.negate.norm`: wherever the working literal `q` is true, the falsifier
entry's literal `t` is false, so the learned literal `¬t` is true. -/
theorem impliesBase_sound {orig : List Domain} {t g : Literal} (h : impliesBase orig t g = true)
    {a : Assignment} (hfit : a.Fits orig) (hg : g.eval a = some false) : t.eval a = some false := by
  unfold impliesBase at h
  rcases Bool.or_eq_true_iff.mp h with heq | h2
  · rw [litEqB_iff.mp heq]; exact hg
  · obtain ⟨hguard, hil⟩ := Bool.and_eq_true_iff.mp h2
    have hslot : t.intForm.atom.slot = g.intForm.atom.slot := by
      unfold impliesLit at hil
      by_cases heq : litEqB t.intForm g.intForm = true
      · rw [litEqB_iff.mp heq]
      · rw [if_neg heq] at hil
        by_cases hs : (t.intForm.atom.slot != g.intForm.atom.slot) = true
        · rw [if_pos hs] at hil; cases hil
        · simpa using hs
    rw [Literal.intForm_slot, Literal.intForm_slot] at hslot
    have hgI := Literal.intForm_eval hg
    obtain ⟨y, hy⟩ : ∃ y, t.eval a = some y := by
      cases htk : t.boolKind with
      | false =>
          apply eval_isSome_of_int htk
          have hsi := slotInt_isSome_of_intForm hgI
          rwa [← hslot] at hsi
      | true =>
          cases hgk : g.boolKind with
          | true => exact eval_isSome_of_bool htk hgk hslot hg
          | false =>
              have hb : slotBoolB orig t.atom.slot = true := by simpa [htk, hgk] using hguard
              have hsi := slotInt_isSome_of_intForm hgI
              rw [← hslot] at hsi
              exact eval_isSome_of_slotBool htk hb hfit hsi
    cases y with
    | false => exact hy
    | true =>
        have := impliesLit_sound hil (Literal.intForm_eval hy)
        rw [hgI] at this
        cases this

/-- The completed lookup is sound at every assignment fitting the original box. -/
theorem impliesP_sound {orig : List Domain} {t g : Literal}
    (h : impliesP orig t g = true) {a : Assignment} (hfit : a.Fits orig)
    (hg : g.eval a = some false) : t.eval a = some false := by
  rcases impliesP_cases h with h | h
  · exact impliesBase_sound h hfit hg
  · exact boolSlotImp_sound h hfit hg

/-- The working literal `q` true forces the falsifier literal false. -/
theorem impliesP_negate_sound {orig : List Domain} {t q : Literal}
    (h : impliesP orig t q.negate.norm = true) {a : Assignment} (hfit : a.Fits orig)
    (hq : q.eval a = some true) : t.eval a = some false := by
  apply impliesP_sound h hfit
  rw [Literal.norm_eval, Literal.eval_negate, hq]
  rfl

/-- SOUNDNESS OF THE ROOT DROP: a literal false under the original domains is
never true at an assignment fitting those domains. -/
theorem litFalseAtRoot_sound {orig : List Domain} {q : Literal}
    (h : litFalseAtRoot orig q = true) {a : Assignment} (hfit : a.Fits orig) :
    q.eval a ≠ some true := by
  intro hq
  by_cases hs : q.atom.slot < a.length
  · have hmem : a[q.atom.slot] ∈ orig.getD q.atom.slot [] :=
      hfit.2 _ _ (List.getElem?_eq_getElem hs)
    have hall := List.all_eq_true.mp h _ hmem
    simp only [Literal.eval, Atom.eval_eq_evalAtValue q.atom a hs] at hq
    cases hv : q.atom.evalAtValue a[q.atom.slot] with
    | none => rw [hv] at hq; cases hq
    | some b =>
        rw [hv] at hq hall
        simp only [Option.map_some, Option.some.injEq] at hq
        cases hp : q.positive <;> cases b <;> simp_all
  · have hnone : q.atom.eval a = none := by
      obtain ⟨atom, pos⟩ := q
      cases atom with
      | boolEq s b =>
          simp only [Atom.slot] at hs
          simp [Atom.eval, List.getElem?_eq_none (by omega : a.length ≤ s)]
      | intLe s k =>
          simp only [Atom.slot] at hs
          simp [Atom.eval, slotInt, List.getElem?_eq_none (by omega : a.length ≤ s)]
      | intNe s k =>
          simp only [Atom.slot] at hs
          simp [Atom.eval, slotInt, List.getElem?_eq_none (by omega : a.length ≤ s)]
    simp [Literal.eval, hnone] at hq

/-! ## 7. Specification of the search, the mark and the transition -/

theorem searchSpace_getElem? {trail : List TrailEntry} {bound : Option Nat} {i : Nat}
    {e : TrailEntry} (h : (searchSpace trail bound)[i]? = some e) :
    trail[i]? = some e ∧ ∀ b, bound = some b → i < b := by
  cases bound with
  | none => exact ⟨h, fun b hb => by cases hb⟩
  | some b =>
      simp only [searchSpace, List.getElem?_take] at h
      by_cases hi : i < b
      · rw [if_pos hi] at h
        exact ⟨h, fun b' hb' => by cases hb'; exact hi⟩
      · rw [if_neg hi] at h; cases h

/-- The falsifier search returns an admissible implying entry. -/
theorem falsifierIdx_spec {orig : List Domain} {trail : List TrailEntry} {bound : Option Nat} {q : Literal}
    {i : Nat} (h : falsifierIdx orig trail bound q = some i) :
    ∃ e, trail[i]? = some e ∧ impliesP orig e.literal q.negate.norm = true ∧
      ∀ b, bound = some b → i < b := by
  unfold falsifierIdx at h
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨h1, h2⟩ := searchSpace_getElem? (List.getElem?_eq_getElem hlt)
  exact ⟨_, h1, hp, h2⟩

/-- THE MARK OUTCOMES: unchanged (root drop), or an admissible implying
entry `e` at index `i` that is dropped (level 0), marked (current level), or
recorded/deduplicated as the learned literal `¬e.literal` (below). -/
theorem markLitAt_spec {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {bound : Option Nat} {marks m' : List Nat} {learnt l' : List (Literal × Nat)}
    {q0 : Literal} (h : markLitAt orig trail lvl bound marks learnt q0 = some (m', l')) :
    (litFalseAtRoot orig q0.norm = true ∧ m' = marks ∧ l' = learnt) ∨
    ∃ i e, trail[i]? = some e ∧ impliesP orig e.literal q0.norm.negate.norm = true ∧
      (∀ b, bound = some b → i < b) ∧
      ((e.level = 0 ∧ m' = marks ∧ l' = learnt) ∨
       (e.level = lvl ∧ e.level ≠ 0 ∧ (m' = marks ∨ m' = i :: marks) ∧ i ∈ m' ∧
          l' = learnt) ∨
       (0 < e.level ∧ e.level < lvl ∧ m' = marks ∧
          ((l' = learnt ∧ ∃ p ∈ learnt, p.1 = e.literal.negate.norm) ∨
           l' = (e.literal.negate.norm, e.level) :: learnt))) := by
  unfold markLitAt at h
  simp only at h
  by_cases hr : litFalseAtRoot orig q0.norm = true
  · rw [if_pos hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨hr, h.1.symm, h.2.symm⟩
  · rw [if_neg hr] at h
    right
    cases hf : falsifierIdx orig trail bound q0.norm with
    | none => rw [hf] at h; cases h
    | some i =>
        rw [hf] at h
        dsimp only at h
        obtain ⟨e, he, hp, hb⟩ := falsifierIdx_spec hf
        rw [he] at h
        simp only at h
        refine ⟨i, e, he, hp, hb, ?_⟩
        by_cases h0 : (e.level == 0) = true
        · rw [if_pos h0] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inl ⟨beq_iff_eq.mp h0, h.1.symm, h.2.symm⟩
        · rw [if_neg h0] at h
          have h0' : e.level ≠ 0 := fun hc => h0 (beq_iff_eq.mpr hc)
          by_cases hl : (e.level == lvl) = true
          · rw [if_pos hl] at h
            right; left
            by_cases hc : marks.contains i = true
            · rw [if_pos hc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨beq_iff_eq.mp hl, h0', Or.inl rfl, List.contains_iff_mem.mp hc, rfl⟩
            · rw [if_neg hc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨beq_iff_eq.mp hl, h0', Or.inr rfl, List.mem_cons_self .., rfl⟩
          · rw [if_neg hl] at h
            have hl' : e.level ≠ lvl := fun hc => hl (beq_iff_eq.mpr hc)
            by_cases hgt : lvl < e.level
            · rw [if_pos hgt] at h; cases h
            · rw [if_neg hgt] at h
              right; right
              refine ⟨by omega, by omega, ?_⟩
              by_cases hd : (learnt.any fun p => litEqB p.1 e.literal.negate.norm) = true
              · rw [if_pos hd] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hd
                exact ⟨rfl, Or.inl ⟨rfl, p, hp, litEqB_iff.mp hpe⟩⟩
              · rw [if_neg hd] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨rfl, Or.inr rfl⟩

/-- The transition shape of the reason-expansion arm. -/
def IsExpansion (trail : List TrailEntry) (st st' : AnalyzerState) : Prop :=
  ∃ (i : Nat) (e : TrailEntry) (r : Reason),
    st.work = [] ∧ st.marks.max? = some i ∧ trail[i]? = some e ∧
    (st.marks.filter (· != i)).isEmpty = false ∧ boundOk st.bound i = true ∧
    e.reason = some r ∧
    st' = { work := [r.clause], skip := some e.literal, bound := some i,
            marks := st.marks.filter (· != i), learnt := st.learnt }

/-- The transition shapes of the three continuing scan arms. -/
def IsScan (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (st st' : AnalyzerState) : Prop :=
  (∃ cs : List Clause,
      st.work = [] :: cs ∧
      st' = { work := cs, skip := st.skip, bound := st.bound, marks := st.marks,
              learnt := st.learnt }) ∨
  (∃ (q : Literal) (qs : Clause) (cs : List Clause),
      st.work = (q :: qs) :: cs ∧
      skipEq st.skip q.norm = true ∧
      st' = { work := qs :: cs, skip := st.skip, bound := st.bound,
              marks := st.marks, learnt := st.learnt }) ∨
  (∃ (q : Literal) (qs : Clause) (cs : List Clause)
     (marks' : List Nat) (learnt' : List (Literal × Nat)),
      st.work = (q :: qs) :: cs ∧
      skipEq st.skip q.norm = false ∧
      markLitAt orig trail lvl st.bound st.marks st.learnt q.norm = some (marks', learnt') ∧
      st' = { work := qs :: cs, skip := st.skip, bound := st.bound, marks := marks',
              learnt := learnt' })

/-- Every continuing transition is an expansion or a scan. -/
theorem expansion_or_scan_of_next {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st st' : AnalyzerState}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.next st') :
    IsExpansion trail st st' ∨ IsScan orig trail lvl st st' := by
  obtain ⟨work, skip, bound, marks, learnt⟩ := st
  unfold IsExpansion IsScan
  cases work with
  | nil =>
      simp only [analyzeNext] at h
      cases hm : marks.max? with
      | none => rw [hm] at h; cases h
      | some i =>
          rw [hm] at h
          dsimp only at h
          cases he : trail[i]? with
          | none => rw [he] at h; cases h
          | some e =>
              rw [he] at h
              simp only at h
              by_cases hq : (marks.filter (· != i)).isEmpty = true
              · rw [if_pos hq] at h; cases h
              · rw [if_neg hq] at h
                by_cases hb : boundOk bound i = true
                · rw [if_pos hb] at h
                  cases hr : e.reason with
                  | none => rw [hr] at h; cases h
                  | some r =>
                      rw [hr] at h
                      injection h with hst
                      exact Or.inl ⟨i, e, r, rfl, rfl, he, by simpa using hq, hb, hr,
                        hst.symm⟩
                · rw [if_neg hb] at h; cases h
  | cons c cs =>
      cases c with
      | nil =>
          simp only [analyzeNext] at h
          injection h with hst
          exact Or.inr (Or.inl ⟨cs, rfl, hst.symm⟩)
      | cons q qs =>
          by_cases hs : skipEq skip q.norm = true
          · simp only [analyzeNext, hs, if_true] at h
            injection h with hst
            exact Or.inr (Or.inr (Or.inl ⟨q, qs, cs, rfl, hs, hst.symm⟩))
          · have hs' : skipEq skip q.norm = false := by simpa using hs
            simp only [analyzeNext, hs', Bool.false_eq_true, if_false] at h
            cases hmk : markLitAt orig trail lvl bound marks learnt q.norm with
            | none => rw [hmk] at h; cases h
            | some mp =>
                obtain ⟨marks', learnt'⟩ := mp
                rw [hmk] at h
                injection h with hst
                exact Or.inr (Or.inr (Or.inr
                  ⟨q, qs, cs, marks', learnt', rfl, hs', hmk, hst.symm⟩))

/-- Conversely, every expansion or scan shape IS the executed transition. -/
theorem next_of_expansion_or_scan {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st st' : AnalyzerState}
    (h : IsExpansion trail st st' ∨ IsScan orig trail lvl st st') :
    analyzeNext orig trail lvl st = AnalyzerStep.next st' := by
  obtain ⟨work, skip, bound, marks, learnt⟩ := st
  rcases h with ⟨i, e, r, hw, hm, he, hne, hb, hr, hst⟩ | hscan
  · simp only at hw hm hne hb hst
    subst hw hst
    simp [analyzeNext, hm, he, hne, hb, hr]
  · rcases hscan with ⟨cs, hw, hst⟩ | ⟨q, qs, cs, hw, hs, hst⟩
      | ⟨q, qs, cs, marks', learnt', hw, hs, hm, hst⟩
    · simp only at hw hst; subst hw hst; rfl
    · simp only at hw hs hst; subst hw hst
      simp [analyzeNext, hs]
    · simp only at hw hs hm hst; subst hw hst
      simp [analyzeNext, hs, hm]

/-- The terminal SUCCESS transition: empty worklist, the highest mark is the
only one left, and its entry's literal is the UIP. -/
theorem analyzeNext_done_some {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st : AnalyzerState} {r : List (Literal × Nat) × Literal}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.done (some r)) :
    st.work = [] ∧ ∃ i e, st.marks.max? = some i ∧ trail[i]? = some e ∧
      (st.marks.filter (· != i)).isEmpty = true ∧ r = (st.learnt, e.literal) := by
  obtain ⟨work, skip, bound, marks, learnt⟩ := st
  cases work with
  | nil =>
      simp only [analyzeNext] at h
      cases hm : marks.max? with
      | none => rw [hm] at h; cases h
      | some i =>
          rw [hm] at h
          dsimp only at h
          cases he : trail[i]? with
          | none => rw [he] at h; cases h
          | some e =>
              rw [he] at h
              simp only at h
              by_cases hq : (marks.filter (· != i)).isEmpty = true
              · rw [if_pos hq] at h
                injection h with h1
                injection h1 with h2
                exact ⟨rfl, i, e, rfl, he, hq, h2.symm⟩
              · rw [if_neg hq] at h
                by_cases hb : boundOk bound i = true
                · rw [if_pos hb] at h
                  cases hr : e.reason with
                  | none => rw [hr] at h; cases h
                  | some r => rw [hr] at h; cases h
                · rw [if_neg hb] at h; cases h
  | cons c cs =>
      cases c with
      | nil => simp [analyzeNext] at h
      | cons q qs =>
          by_cases hs : skipEq skip q.norm = true
          · simp [analyzeNext, hs] at h
          · have hs' : skipEq skip q.norm = false := by simpa using hs
            simp only [analyzeNext, hs', Bool.false_eq_true, if_false] at h
            cases hmk : markLitAt orig trail lvl bound marks learnt q.norm with
            | none => rw [hmk] at h; cases h
            | some mp => rw [hmk] at h; cases h

/-! ## 8. Structural invariants: marks and learned literals -/

/-- Every mark names a trail entry at the analysis level. -/
def LcgMarksOk (trail : List TrailEntry) (lvl : Nat) (marks : List Nat) : Prop :=
  ∀ m ∈ marks, ∃ e, trail[m]? = some e ∧ e.level = lvl

/-- Every learned literal is the normalized NEGATION of a trail entry whose
level it records, strictly between the root and the analysis level. -/
def LcgLearntOk (trail : List TrailEntry) (lvl : Nat)
    (learnt : List (Literal × Nat)) : Prop :=
  ∀ p ∈ learnt, ∃ e : TrailEntry, e ∈ trail ∧ p.1 = e.literal.negate.norm ∧
    e.level = p.2 ∧ 0 < p.2 ∧ p.2 < lvl

theorem lcgInv_next {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {st st' : AnalyzerState} (h : analyzeNext orig trail lvl st = AnalyzerStep.next st')
    (hm : LcgMarksOk trail lvl st.marks) (hl : LcgLearntOk trail lvl st.learnt) :
    LcgMarksOk trail lvl st'.marks ∧ LcgLearntOk trail lvl st'.learnt := by
  rcases expansion_or_scan_of_next h with
    ⟨i, e, r, -, -, -, -, -, -, hst⟩ | ⟨cs, -, hst⟩ | ⟨q, qs, cs, -, -, hst⟩ |
      ⟨q, qs, cs, m', l', -, -, hmk, hst⟩
  · subst hst
    exact ⟨fun m hmem => hm m (List.mem_filter.mp hmem).1, hl⟩
  · subst hst; exact ⟨hm, hl⟩
  · subst hst; exact ⟨hm, hl⟩
  · subst hst
    rcases markLitAt_spec hmk with ⟨-, rfl, rfl⟩ | ⟨i, e, he, -, -, hcase⟩
    · exact ⟨hm, hl⟩
    · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hlv, -, hm', -, rfl⟩ | ⟨h0, hlt, rfl, hl'⟩
      · exact ⟨hm, hl⟩
      · refine ⟨?_, hl⟩
        rcases hm' with rfl | rfl
        · exact hm
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨e, he, hlv⟩
          · exact hm x hx
      · refine ⟨hm, ?_⟩
        rcases hl' with ⟨rfl, -⟩ | rfl
        · exact hl
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨e, List.mem_of_getElem? he, rfl, rfl, h0, hlt⟩
          · exact hl p hp

/-- THE STRUCTURAL RESULT: a successful run records only trail-negated
learned literals strictly below the analysis level, and its UIP is the
literal of a trail entry AT the analysis level. -/
theorem analyzeLoop_inv {orig : List Domain} {trail : List TrailEntry} {lvl : Nat} :
    ∀ (fuel : Nat) (st : AnalyzerState) (below : List (Literal × Nat)) (uip : Literal),
    LcgMarksOk trail lvl st.marks → LcgLearntOk trail lvl st.learnt →
    analyzeLoop orig trail lvl fuel st = some (below, uip) →
    LcgLearntOk trail lvl below ∧
      ∃ (i : Nat) (e : TrailEntry), trail[i]? = some e ∧ e.literal = uip ∧ e.level = lvl := by
  intro fuel
  induction fuel with
  | zero => intro st below uip _ _ h; simp [analyzeLoop] at h
  | succ fuel ih =>
      intro st below uip hm hl h
      cases hn : analyzeNext orig trail lvl st with
      | done r =>
          simp only [analyzeLoop, hn] at h
          subst h
          obtain ⟨-, i, e, hmax, he, -, hr⟩ := analyzeNext_done_some hn
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨e', he', hlv⟩ := hm i (List.max?_mem hmax)
          rw [he] at he'
          cases he'
          exact ⟨hl, i, e, he, rfl, hlv⟩
      | next st' =>
          simp only [analyzeLoop, hn] at h
          obtain ⟨hm', hl'⟩ := lcgInv_next hn hm hl
          exact ih st' below uip hm' hl' h

theorem lcgInv_init (trail : List TrailEntry) (lvl : Nat) (c : Clause) :
    LcgMarksOk trail lvl (initAnalysisState c).marks ∧
      LcgLearntOk trail lvl (initAnalysisState c).learnt :=
  ⟨fun _ h => by simp [initAnalysisState] at h,
   fun _ h => by simp [initAnalysisState] at h⟩

/-! ## 9. Semantic invariant: the learned clause is entailed

At a fixed assignment `a` fitting the original domains, satisfying every
trail reason clause and every level-0 trail literal, the analyzer state's
"virtual clause" — learned literals, negated marks, unscanned non-pivot
literals — always has a true literal, provided the conflict clause had one.
No exactness, chronology or distinctness of the trail is needed. -/

/-- The virtual clause of an analyzer state holds at `a`. -/
def LcgHolds (trail : List TrailEntry) (st : AnalyzerState) (a : Assignment) : Prop :=
  (∃ p ∈ st.learnt, p.1.eval a = some true) ∨
  (∃ m ∈ st.marks, ∃ e, trail[m]? = some e ∧ e.literal.eval a = some false) ∨
  (∃ c ∈ st.work, ∃ q ∈ c, skipEq st.skip q.norm = false ∧ q.eval a = some true)

theorem lcgHolds_init {trail : List TrailEntry} {c : Clause} {a : Assignment}
    (hc : c.SatisfiedBy a) : LcgHolds trail (initAnalysisState c) a := by
  obtain ⟨q, hq, hqt⟩ := hc
  exact Or.inr (Or.inr ⟨c, List.mem_singleton_self _, q, hq, rfl, hqt⟩)

theorem lcgHolds_next {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {a : Assignment} (hfit : a.Fits orig)
    (hreasons : ∀ e ∈ trail, ∀ r ∈ e.reason, r.clause.SatisfiedBy a)
    (hroot : ∀ e ∈ trail, e.level = 0 → e.literal.eval a = some true)
    {st st' : AnalyzerState} (h : analyzeNext orig trail lvl st = AnalyzerStep.next st')
    (hh : LcgHolds trail st a) : LcgHolds trail st' a := by
  rcases expansion_or_scan_of_next h with
    ⟨i, e, r, hw, -, he, -, -, hr, hst⟩ | ⟨cs, hw, hst⟩ | ⟨q, qs, cs, hw, hs, hst⟩ |
      ⟨q, qs, cs, m', l', hw, hs, hmk, hst⟩
  · subst hst
    rcases hh with hlrn | ⟨m, hmem, em, hem, hfalse⟩ | ⟨c, hc, -⟩
    · exact Or.inl hlrn
    · by_cases hmi : m = i
      · subst hmi
        rw [he] at hem
        cases hem
        obtain ⟨q, hq, hqt⟩ := hreasons e (List.mem_of_getElem? he) r hr
        right; right
        refine ⟨r.clause, List.mem_singleton_self _, q, hq, ?_, hqt⟩
        cases hsk : skipEq (some e.literal) q.norm with
        | false => rfl
        | true =>
            simp only [skipEq] at hsk
            have hqn : q.norm = e.literal := litEqB_iff.mp hsk
            rw [← hqn, Literal.norm_eval, hqt] at hfalse
            cases hfalse
      · exact Or.inr (Or.inl ⟨m, List.mem_filter.mpr ⟨hmem, by simpa using hmi⟩, em, hem,
          hfalse⟩)
    · rw [hw] at hc; cases hc
  · subst hst
    rcases hh with h1 | h2 | ⟨c, hc, q, hq, hsk, hqt⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · rw [hw] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · cases hq
      · exact Or.inr (Or.inr ⟨c, hc, q, hq, hsk, hqt⟩)
  · subst hst
    rcases hh with h1 | h2 | ⟨c, hc, q', hq', hsk, hqt⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · rw [hw] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · rw [hs] at hsk; cases hsk
        · exact Or.inr (Or.inr ⟨qs, List.mem_cons_self .., q', hq', hsk, hqt⟩)
      · exact Or.inr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, q', hq', hsk, hqt⟩)
  · subst hst
    -- the old witnesses survive the mark
    have hkeep : (∀ p ∈ st.learnt, p ∈ l') ∧ (∀ m ∈ st.marks, m ∈ m') := by
      rcases markLitAt_spec hmk with ⟨-, rfl, rfl⟩ | ⟨i, e, -, -, -, hcase⟩
      · exact ⟨fun _ h => h, fun _ h => h⟩
      · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, -, hm', -, rfl⟩ | ⟨-, -, rfl, hl'⟩
        · exact ⟨fun _ h => h, fun _ h => h⟩
        · refine ⟨fun _ h => h, ?_⟩
          rcases hm' with rfl | rfl
          · exact fun _ h => h
          · exact fun _ h => List.mem_cons_of_mem _ h
        · refine ⟨?_, fun _ h => h⟩
          rcases hl' with ⟨rfl, -⟩ | rfl
          · exact fun _ h => h
          · exact fun _ h => List.mem_cons_of_mem _ h
    rcases hh with ⟨p, hp, hpt⟩ | ⟨m, hmem, em, hem, hfalse⟩ | ⟨c, hc, q', hq', hsk, hqt⟩
    · exact Or.inl ⟨p, hkeep.1 p hp, hpt⟩
    · exact Or.inr (Or.inl ⟨m, hkeep.2 m hmem, em, hem, hfalse⟩)
    · rw [hw] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · -- the scanned literal is the witness: its mark outcome carries it
          have hqq : q'.norm.norm.eval a = some true := by
            rw [Literal.norm_eval, Literal.norm_eval]; exact hqt
          rcases markLitAt_spec hmk with ⟨hroot', -, -⟩ | ⟨i, e, he, hp, -, hcase⟩
          · exact absurd hqq (litFalseAtRoot_sound hroot' hfit)
          · have hef : e.literal.eval a = some false := impliesP_negate_sound hp hfit hqq
            rcases hcase with ⟨h0, -, -⟩ | ⟨-, -, -, hi, -⟩ | ⟨-, -, -, hl'⟩
            · have := hroot e (List.mem_of_getElem? he) h0
              rw [hef] at this; cases this
            · exact Or.inr (Or.inl ⟨i, hi, e, he, hef⟩)
            · have hwl : e.literal.negate.norm.eval a = some true := by
                rw [Literal.norm_eval, Literal.eval_negate_false_iff]; exact hef
              rcases hl' with ⟨rfl, p, hp, hpe⟩ | rfl
              · exact Or.inl ⟨p, hp, by rw [hpe]; exact hwl⟩
              · exact Or.inl ⟨_, List.mem_cons_self .., hwl⟩
        · exact Or.inr (Or.inr ⟨qs, List.mem_cons_self .., q', hq', hsk, hqt⟩)
      · exact Or.inr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, q', hq', hsk, hqt⟩)

/-- The terminal step closes the virtual clause into the learned clause
`¬uip ∨ below`. -/
theorem lcgHolds_done {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {a : Assignment} {st : AnalyzerState} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.done (some (below, uip)))
    (hh : LcgHolds trail st a) :
    uip.negate.eval a = some true ∨ ∃ p ∈ below, p.1.eval a = some true := by
  obtain ⟨hw, i, e, -, he, hempty, hr⟩ := analyzeNext_done_some h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  rcases hh with hlrn | ⟨m, hmem, em, hem, hfalse⟩ | ⟨c, hc, -⟩
  · exact Or.inr hlrn
  · have hmi : m = i := by
      refine Classical.byContradiction fun hne => ?_
      have : m ∈ st.marks.filter (· != i) :=
        List.mem_filter.mpr ⟨hmem, by simpa using hne⟩
      rw [List.isEmpty_iff.mp hempty] at this
      cases this
    subst hmi
    rw [he] at hem
    cases hem
    left
    rw [Literal.eval_negate_false_iff]; exact hfalse
  · rw [hw] at hc; cases hc

/-- THE SEMANTIC RESULT at one assignment. -/
theorem analyzeLoop_holds {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {a : Assignment} (hfit : a.Fits orig)
    (hreasons : ∀ e ∈ trail, ∀ r ∈ e.reason, r.clause.SatisfiedBy a)
    (hroot : ∀ e ∈ trail, e.level = 0 → e.literal.eval a = some true) :
    ∀ (fuel : Nat) (st : AnalyzerState) (below : List (Literal × Nat)) (uip : Literal),
    LcgHolds trail st a → analyzeLoop orig trail lvl fuel st = some (below, uip) →
    uip.negate.eval a = some true ∨ ∃ p ∈ below, p.1.eval a = some true := by
  intro fuel
  induction fuel with
  | zero => intro st below uip _ h; simp [analyzeLoop] at h
  | succ fuel ih =>
      intro st below uip hh h
      cases hn : analyzeNext orig trail lvl st with
      | done r =>
          simp only [analyzeLoop, hn] at h
          subst h
          exact lcgHolds_done hn hh
      | next st' =>
          simp only [analyzeLoop, hn] at h
          exact ih st' below uip (lcgHolds_next hfit hreasons hroot hn hh) h

/-! ## 10. Termination: the potential strictly decreases -/

private theorem sum_take_le_sum : ∀ (l : List Nat) (n : Nat), (l.take n).sum ≤ l.sum
  | [], _ => by simp
  | x :: xs, 0 => by simp
  | x :: xs, n + 1 => by
      simp only [List.take_succ_cons, List.sum_cons]
      have := sum_take_le_sum xs n
      omega

private theorem sum_take_succ {l : List Nat} {i x : Nat} (h : l[i]? = some x) :
    (l.take (i + 1)).sum = (l.take i).sum + x := by
  rw [List.take_add_one, h]
  simp

theorem analyzerFrontierCost_expand {trail : List TrailEntry} {bound : Option Nat}
    {i : Nat} {e : TrailEntry} (he : trail[i]? = some e) (hb : boundOk bound i = true) :
    analyzerFrontierCost trail (some i) + pivotEntryCost e
      ≤ analyzerFrontierCost trail bound := by
  have hL : (trail.map pivotEntryCost)[i]? = some (pivotEntryCost e) := by
    rw [List.getElem?_map, he]; rfl
  have hstep := sum_take_succ hL
  have hle : ((trail.map pivotEntryCost).take (i + 1)).sum
      ≤ analyzerFrontierCost trail bound := by
    cases bound with
    | none =>
        simp only [analyzerFrontierCost, searchSpace]
        exact sum_take_le_sum _ _
    | some b =>
        simp only [boundOk, decide_eq_true_eq] at hb
        simp only [analyzerFrontierCost, searchSpace, List.map_take]
        have := sum_take_le_sum ((trail.map pivotEntryCost).take b) (i + 1)
        rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  simp only [analyzerFrontierCost, searchSpace, List.map_take] at hle ⊢
  omega

/-- EVERY continuing transition strictly decreases the potential. No
premise: the expansion guard `boundOk` is part of the transition. -/
theorem analyzerPotential_lt_of_next {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st st' : AnalyzerState}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.next st') :
    analyzerPotential trail st' < analyzerPotential trail st := by
  rcases expansion_or_scan_of_next h with
    ⟨i, e, r, hw, -, he, -, hb, hr, hst⟩ | ⟨cs, hw, hst⟩ | ⟨q, qs, cs, hw, -, hst⟩ |
      ⟨q, qs, cs, m', l', hw, -, -, hst⟩
  · subst hst
    have hx := analyzerFrontierCost_expand he hb
    simp only [analyzerPotential, hw, workCost, pivotEntryCost, hr] at hx ⊢
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hx ⊢
    omega
  · subst hst
    simp only [analyzerPotential, hw, workCost, List.length_cons, List.map_cons,
      List.sum_cons, List.length_nil]
    omega
  · subst hst
    simp only [analyzerPotential, hw, workCost, List.length_cons, List.map_cons,
      List.sum_cons]
    omega
  · subst hst
    simp only [analyzerPotential, hw, workCost, List.length_cons, List.map_cons,
      List.sum_cons]
    omega

/-- TERMINATION: with fuel above the potential, the loop never runs out of
fuel — it stops at a `.done` transition. -/
theorem analyzeLoop_stops {orig : List Domain} {trail : List TrailEntry} {lvl : Nat} :
    ∀ (fuel : Nat) (st : AnalyzerState), analyzerPotential trail st < fuel →
      ∃ (k : Nat) (st₀ : AnalyzerState) (r : Option (List (Literal × Nat) × Literal)),
        k < fuel ∧ analyzeNext orig trail lvl st₀ = AnalyzerStep.done r ∧
        analyzeLoop orig trail lvl fuel st = r := by
  intro fuel
  induction fuel with
  | zero => intro st h; omega
  | succ fuel ih =>
      intro st hpot
      cases hn : analyzeNext orig trail lvl st with
      | done r => exact ⟨0, st, r, by omega, hn, by simp [analyzeLoop, hn]⟩
      | next st' =>
          have hlt := analyzerPotential_lt_of_next hn
          obtain ⟨k, st₀, r, hk, hd, hl⟩ := ih st' (by omega)
          exact ⟨k + 1, st₀, r, by omega, hd, by simp only [analyzeLoop, hn]; exact hl⟩

end LeanFzn.Solver.Propagation

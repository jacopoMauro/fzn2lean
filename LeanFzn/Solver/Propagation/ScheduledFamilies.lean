/-
File: LeanFzn/Solver/Propagation/ScheduledFamilies.lean

Purpose (PLAN task P1): the CONCRETE locality discharges for the scheduled
scan. For every registered family whose propagator DECLARES a watch
footprint (`propagatorOfProved`'s nonempty `watches` lists), the run reads
only the current domains of the watched slots — so the memorized watch
projection determines the result, which is exactly the premiss
`PropLocalOne` of the equivalence theorems in `ScheduledPropagation`.

Families with an empty declared footprint (`linLe`, `linEq`, `linNe`,
`timesSlot`, `minSlot`, `maxSlot`, `absSlot`, `allDiff`, and every
unregistered family) are NEVER scheduled: the scheduled scan refuses to
reuse a table entry of a footprint-less propagator, so no locality claim is
made for them and the scan simply re-runs them (the full scan's behaviour).

The result `clampProps_local` is the premiss the certified LCG route
discharges for its actual propagator list,
`clampProps orig (dcs.filterMap propagatorOfProved)`.

DAG: ScheduledPropagation + Proofs/Propagators -> ScheduledFamilies.
-/
import LeanFzn.Solver.Propagation.ScheduledPropagation
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Solver.Propagation.LiteralClamp
open LeanFzn.Semantics LeanFzn.Solver.Core


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The watch projection reads the watched slots -/

/-- A watched atom's entry of the projection is the current domain of its
slot. -/
theorem watchStamp_getD {f g : BranchFrame} {ws : List Atom}
    (h : watchStamp f ws = watchStamp g ws) (a : Atom) (ha : a ∈ ws) :
    (Frame.domains f).getD a.slot [] = (Frame.domains g).getD a.slot [] := by
  induction ws with
  | nil => simp at ha
  | cons b ws ih =>
      simp only [watchStamp, List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact ih h.2 ha

/-! ## Primitive locality -/

/-- `narrowHi` reads only the domain of its slot. -/
theorem narrowHi_local {s : Nat} {hi : Int} {ng : Clause} {st1 st2 : State}
    (h : st1.domains.getD s [] = st2.domains.getD s []) :
    narrowHi st1 s hi ng = narrowHi st2 s hi ng := by
  simp only [narrowHi, h]

/-- `narrowLo` reads only the domain of its slot. -/
theorem narrowLo_local {s : Nat} {lo : Int} {ng : Clause} {st1 st2 : State}
    (h : st1.domains.getD s [] = st2.domains.getD s []) :
    narrowLo st1 s lo ng = narrowLo st2 s lo ng := by
  simp only [narrowLo, h]

/-- `domBoolPin` reads only the domain of its slot. -/
theorem domBoolPin_local {doms1 doms2 : List Domain} {s : Nat} {b : Bool}
    (h : doms1.getD s [] = doms2.getD s []) :
    domBoolPin doms1 s b = domBoolPin doms2 s b := by
  simp only [domBoolPin, h]

/-- `implyBool` reads only the domain of its slot. -/
theorem implyBool_local {st1 st2 : State} {s : Nat} {b : Bool} {ng : Clause}
    (h : st1.domains.getD s [] = st2.domains.getD s []) :
    implyBool st1 s b ng = implyBool st2 s b ng := by
  simp only [implyBool, h]

/-! ## Per-family locality of the run functions -/

theorem propLe_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j []) :
    propLe st1 i j = propLe st2 i j := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  simp only [propLe, hi, hj, A, B]

theorem propLt_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j []) :
    propLt st1 i j = propLt st2 i j := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  simp only [propLt, hi, hj, A, B]

theorem propEq_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j []) :
    propEq st1 i j = propEq st2 i j := by
  have A : ∀ k c, narrowLo st1 i k c = narrowLo st2 i k c := fun k c => narrowLo_local hi
  have B : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have C : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  have D : ∀ k c, narrowHi st1 j k c = narrowHi st2 j k c := fun k c => narrowHi_local hj
  simp only [propEq, hi, hj, A, B, C, D]

theorem propNe_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j []) :
    propNe st1 i j = propNe st2 i j := by
  simp only [propNe, hi, hj]

theorem propPlus_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j [])
    (hk : st1.domains.getD k [] = st2.domains.getD k []) :
    propPlus st1 i j k = propPlus st2 i j k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Aj : ∀ t c, narrowLo st1 j t c = narrowLo st2 j t c := fun t c => narrowLo_local hj
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bj : ∀ t c, narrowHi st1 j t c = narrowHi st2 j t c := fun t c => narrowHi_local hj
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propPlus, hi, hj, hk, Ai, Aj, Ak, Bi, Bj, Bk]

theorem propLeConstHi_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i []) :
    propLeConstHi st1 i c = propLeConstHi st2 i c := by
  simp only [propLeConstHi, narrowHi_local hi]

theorem propLeConstLo_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i []) :
    propLeConstLo st1 i c = propLeConstLo st2 i c := by
  simp only [propLeConstLo, narrowLo_local hi]

theorem propLtConstHi_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i []) :
    propLtConstHi st1 i c = propLtConstHi st2 i c := by
  simp only [propLtConstHi, narrowHi_local hi]

theorem propLtConstLo_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i []) :
    propLtConstLo st1 i c = propLtConstLo st2 i c := by
  simp only [propLtConstLo, narrowLo_local hi]

theorem propConstEq_local {i : Nat} {v : Value} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i []) :
    propConstEq st1 i v = propConstEq st2 i v := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 i k c = narrowLo st2 i k c := fun k c => narrowLo_local hi
  simp only [propConstEq, hi, A, B]

theorem propBoolNot_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j []) :
    propBoolNot st1 i j = propBoolNot st2 i j := by
  have Ai : ∀ b, domBoolPin st1.domains i b = domBoolPin st2.domains i b :=
    fun b => domBoolPin_local hi
  have Aj : ∀ b, domBoolPin st1.domains j b = domBoolPin st2.domains j b :=
    fun b => domBoolPin_local hj
  have Bi : ∀ b c, implyBool st1 i b c = implyBool st2 i b c := fun b c => implyBool_local hi
  have Bj : ∀ b c, implyBool st1 j b c = implyBool st2 j b c := fun b c => implyBool_local hj
  simp only [propBoolNot, Ai, Aj, Bi, Bj]

theorem propBoolAnd_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j [])
    (hk : st1.domains.getD k [] = st2.domains.getD k []) :
    propBoolAnd st1 i j k = propBoolAnd st2 i j k := by
  have Ai : ∀ b, domBoolPin st1.domains i b = domBoolPin st2.domains i b :=
    fun b => domBoolPin_local hi
  have Aj : ∀ b, domBoolPin st1.domains j b = domBoolPin st2.domains j b :=
    fun b => domBoolPin_local hj
  have Ak : ∀ b, domBoolPin st1.domains k b = domBoolPin st2.domains k b :=
    fun b => domBoolPin_local hk
  have Bi : ∀ b c, implyBool st1 i b c = implyBool st2 i b c := fun b c => implyBool_local hi
  have Bj : ∀ b c, implyBool st1 j b c = implyBool st2 j b c := fun b c => implyBool_local hj
  have Bk : ∀ b c, implyBool st1 k b c = implyBool st2 k b c := fun b c => implyBool_local hk
  simp only [propBoolAnd, Ai, Aj, Ak, Bi, Bj, Bk]

theorem propBoolOr_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i [] = st2.domains.getD i [])
    (hj : st1.domains.getD j [] = st2.domains.getD j [])
    (hk : st1.domains.getD k [] = st2.domains.getD k []) :
    propBoolOr st1 i j k = propBoolOr st2 i j k := by
  have Ai : ∀ b, domBoolPin st1.domains i b = domBoolPin st2.domains i b :=
    fun b => domBoolPin_local hi
  have Aj : ∀ b, domBoolPin st1.domains j b = domBoolPin st2.domains j b :=
    fun b => domBoolPin_local hj
  have Ak : ∀ b, domBoolPin st1.domains k b = domBoolPin st2.domains k b :=
    fun b => domBoolPin_local hk
  have Bi : ∀ b c, implyBool st1 i b c = implyBool st2 i b c := fun b c => implyBool_local hi
  have Bj : ∀ b c, implyBool st1 j b c = implyBool st2 j b c := fun b c => implyBool_local hj
  have Bk : ∀ b c, implyBool st1 k b c = implyBool st2 k b c := fun b c => implyBool_local hk
  simp only [propBoolOr, Ai, Aj, Ak, Bi, Bj, Bk]

/-! ## Propagator-level locality of the registered families -/

/-- The clamp preserves `PropLocalOne` (same watches, clamped emissions). -/
theorem PropLocalOne.clamp {orig : List Domain} {p : Propagator}
    (h : PropLocalOne p) : PropLocalOne (p.clamp orig) := by
  intro f g hstamp
  simp only [Propagator.clamp]
  rw [h f g hstamp]

/-- The watched-slot hypotheses from one watch-stamp equality. -/
theorem watchStamp_getD_of_mem {f g : BranchFrame} {ws : List Atom}
    (h : watchStamp f ws = watchStamp g ws) {a : Atom} (ha : a ∈ ws) :
    (frameState f).domains.getD a.slot [] = (frameState g).domains.getD a.slot [] :=
  watchStamp_getD h a ha

theorem propLe_propLocal (i j : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0], run := fun st => propLe st i j } := by
  intro f g hstamp
  exact propLe_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))

theorem propLt_propLocal (i j : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0], run := fun st => propLt st i j } := by
  intro f g hstamp
  exact propLt_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))

theorem propEq_propLocal (i j : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0], run := fun st => propEq st i j } := by
  intro f g hstamp
  exact propEq_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))

theorem propNe_propLocal (i j : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0], run := fun st => propNe st i j } := by
  intro f g hstamp
  exact propNe_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))

theorem propPlus_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propPlus st i j k } := by
  intro f g hstamp
  exact propPlus_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

theorem propLeConstHi_propLocal (i : Nat) (c : Int) :
    PropLocalOne { watches := [.intLe i 0], run := fun st => propLeConstHi st i c } := by
  intro f g hstamp
  exact propLeConstHi_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))

theorem propLeConstLo_propLocal (i : Nat) (c : Int) :
    PropLocalOne { watches := [.intLe i 0], run := fun st => propLeConstLo st i c } := by
  intro f g hstamp
  exact propLeConstLo_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))

theorem propLtConstHi_propLocal (i : Nat) (c : Int) :
    PropLocalOne { watches := [.intLe i 0], run := fun st => propLtConstHi st i c } := by
  intro f g hstamp
  exact propLtConstHi_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))

theorem propLtConstLo_propLocal (i : Nat) (c : Int) :
    PropLocalOne { watches := [.intLe i 0], run := fun st => propLtConstLo st i c } := by
  intro f g hstamp
  exact propLtConstLo_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))

theorem propConstEq_propLocal (i : Nat) (v : Value) :
    PropLocalOne { watches := [.intLe i 0], run := fun st => propConstEq st i v } := by
  intro f g hstamp
  exact propConstEq_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))

theorem propBoolNot_propLocal (i j : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0], run := fun st => propBoolNot st i j } := by
  intro f g hstamp
  exact propBoolNot_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))

theorem propBoolAnd_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propBoolAnd st i j k } := by
  intro f g hstamp
  exact propBoolAnd_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

theorem propBoolOr_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propBoolOr st i j k } := by
  intro f g hstamp
  exact propBoolOr_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-! ## The concrete registration -/

/-- Every registered propagator with a nonempty declared footprint is
locally sound; footprint-less registrations (and unregistered families) are
excluded (they are never scheduled). -/
theorem propagatorOfProved_local {dc : DomConstraint} {p : Propagator}
    (hp : propagatorOfProved dc = some p) (hne : p.watches ≠ []) : PropLocalOne p := by
  cases dc with
  | eqSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propEq_propLocal _ _
  | neSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propNe_propLocal _ _
  | leSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLe_propLocal _ _
  | constEq a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propConstEq_propLocal _ _
  | plusSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propPlus_propLocal _ _ _
  | leConstHi a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLeConstHi_propLocal _ _
  | leConstLo a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLeConstLo_propLocal _ _
  | allDiff a =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | timesSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | minSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | maxSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | absSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linEq a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linLe a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linNe a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | ltSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLt_propLocal _ _
  | ltConstHi a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLtConstHi_propLocal _ _
  | ltConstLo a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLtConstLo_propLocal _ _
  | boolNotSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propBoolNot_propLocal _ _
  | boolAndSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propBoolAnd_propLocal _ _ _
  | boolOrSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propBoolOr_propLocal _ _ _
  | boolClauseSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | arrayBoolAndSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | bool2intSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | boolEqSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | arrayIntElementSlot a b c =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | arrayVarIntElementSlot a b c =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | arrayVarBoolElementSlot a b c =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | eqReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | leReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | neReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linEqReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linLeReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | linNeReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | maxGen a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | minGen a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | divGen a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | modGen a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact absurd rfl hne
  | minPair a b c =>
      cases a <;> cases b <;> cases c <;>
        (simp only [propagatorOfProved, Option.some.injEq] at hp
         subst hp
         exact absurd rfl hne)
  | maxPair a b c =>
      cases a <;> cases b <;> cases c <;>
        (simp only [propagatorOfProved, Option.some.injEq] at hp
         subst hp
         exact absurd rfl hne)

/-- **THE CONCRETE LOCALITY DISCHARGE**: the certified LCG route's actual
propagator list is locally sound on its schedulable members. -/
theorem clampProps_local (orig : List Domain) (dcs : List DomConstraint) :
    PropLocal (clampProps orig (dcs.filterMap propagatorOfProved)) := by
  intro p hp hne
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  have hne' : p0.watches ≠ [] := by
    intro hnil
    exact hne (by simp [Propagator.clamp, hnil])
  obtain ⟨dc, _, hprop⟩ := propagatorsOfProved_mem hp0
  exact PropLocalOne.clamp (propagatorOfProved_local hprop hne')

end LeanFzn.Solver.Propagation

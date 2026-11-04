/-
File: LeanFzn/Solver/Propagation/ScheduledFamilies.lean

Purpose (PLAN task P1): the CONCRETE locality discharges for the scheduled
scan. For every registered family whose propagator DECLARES a watch
footprint (`propagatorOfProved`'s nonempty `watches` lists), the run reads
only the current domains of the watched slots — so the memorized watch
projection determines the result, which is exactly the premiss
`PropLocalOne` of the equivalence theorems in `ScheduledPropagation`.

Unregistered families have no `propagatorOfProved` arm and hence no
footprint; a footprint-less propagator's table entry is never reused, so the
scan simply re-runs it (the full scan's behaviour). Every registered family,
including `allDiff` (S3a), now has a proved footprint.

The result `clampProps_local` is the premiss the certified LCG route
discharges for its actual propagator list,
`clampProps orig (dcs.filterMap propagatorOfProved)`.

DAG: ScheduledPropagation + Proofs/Propagators -> ScheduledFamilies.
-/
import LeanFzn.Legacy.Solver.Propagation.ScheduledPropagation
import LeanFzn.Legacy.Solver.Propagation.Proofs.Propagators
import LeanFzn.Legacy.Solver.Propagation.Proofs.Fam.AllDiffLocal
import LeanFzn.Legacy.Solver.Propagation.LiteralClamp
open LeanFzn.Semantics LeanFzn.Solver.Core


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The watch projection reads the watched slots -/

/-- A watched atom's entry of the projection is the current domain of its
slot. -/
theorem watchStamp_getD {f g : BranchFrame} {ws : List Atom}
    (h : watchStamp f ws = watchStamp g ws) (a : Atom) (ha : a ∈ ws) :
    (Frame.domains f).getD a.slot Dom.empty = (Frame.domains g).getD a.slot Dom.empty := by
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
    (h : st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    narrowHi st1 s hi ng = narrowHi st2 s hi ng := by
  simp only [narrowHi, h]

/-- `narrowLo` reads only the domain of its slot. -/
theorem narrowLo_local {s : Nat} {lo : Int} {ng : Clause} {st1 st2 : State}
    (h : st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    narrowLo st1 s lo ng = narrowLo st2 s lo ng := by
  simp only [narrowLo, h]

/-- A list-wide `flatMap` is determined by its pointwise values. -/
theorem list_flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.flatMap_cons, h a (by simp),
        list_flatMap_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A list-wide Boolean conjunction is determined by its pointwise values. -/
theorem list_all_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
      show (p a && l.all p) = (q a && l.all q)
      rw [h a (by simp),
        list_all_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A list-wide Boolean disjunction is determined by its pointwise values. -/
theorem list_any_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
      show (p a || l.any p) = (q a || l.any q)
      rw [h a (by simp),
        list_any_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A list-wide `find?` is determined by its pointwise values. -/
theorem list_find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?_cons, h a (by simp)]
      cases q a <;>
        simp [list_find?_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A list-wide `filterMap` is determined by its pointwise values. -/
theorem list_filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.filterMap_cons, h a (by simp),
        list_filterMap_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `domBoolPin` reads only the domain of its slot. -/
theorem domBoolPin_local {doms1 doms2 : List Domain} {s : Nat} {b : Bool}
    (h : doms1.getD s Dom.empty = doms2.getD s Dom.empty) :
    domBoolPin doms1 s b = domBoolPin doms2 s b := by
  simp only [domBoolPin, slotEnum, h]

/-- `implyBool` reads only the domain of its slot. -/
theorem implyBool_local {st1 st2 : State} {s : Nat} {b : Bool} {ng : Clause}
    (h : st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    implyBool st1 s b ng = implyBool st2 s b ng := by
  simp only [implyBool, slotEnum, h]
  rfl

/-! ## Per-family locality of the run functions -/

theorem propLe_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propLe st1 i j = propLe st2 i j := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  simp only [propLe, hi, hj, A, B]

theorem propLt_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propLt st1 i j = propLt st2 i j := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  simp only [propLt, hi, hj, A, B]

theorem propEq_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propEq st1 i j = propEq st2 i j := by
  have A : ∀ k c, narrowLo st1 i k c = narrowLo st2 i k c := fun k c => narrowLo_local hi
  have B : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have C : ∀ k c, narrowLo st1 j k c = narrowLo st2 j k c := fun k c => narrowLo_local hj
  have D : ∀ k c, narrowHi st1 j k c = narrowHi st2 j k c := fun k c => narrowHi_local hj
  simp only [propEq, hi, hj, A, B, C, D]

theorem propNe_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propNe st1 i j = propNe st2 i j := by
  simp only [propNe, hi, hj]

theorem propPlus_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propPlus st1 i j k = propPlus st2 i j k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Aj : ∀ t c, narrowLo st1 j t c = narrowLo st2 j t c := fun t c => narrowLo_local hj
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bj : ∀ t c, narrowHi st1 j t c = narrowHi st2 j t c := fun t c => narrowHi_local hj
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propPlus, hi, hj, hk, Ai, Aj, Ak, Bi, Bj, Bk]

/-- `propMin` reads only the three operand/result domains (their extrema). -/
theorem propMin_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propMin st1 i j k = propMin st2 i j k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Aj : ∀ t c, narrowLo st1 j t c = narrowLo st2 j t c := fun t c => narrowLo_local hj
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bj : ∀ t c, narrowHi st1 j t c = narrowHi st2 j t c := fun t c => narrowHi_local hj
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propMin, hi, hj, hk, Ai, Aj, Ak, Bk]

/-- `propMax` reads only the three operand/result domains (their extrema). -/
theorem propMax_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propMax st1 i j k = propMax st2 i j k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Aj : ∀ t c, narrowLo st1 j t c = narrowLo st2 j t c := fun t c => narrowLo_local hj
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bj : ∀ t c, narrowHi st1 j t c = narrowHi st2 j t c := fun t c => narrowHi_local hj
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propMax, hi, hj, hk, Ak, Bi, Bj, Bk]

/-- `propTimes` reads only the three operand/result domains (their extrema
    and the target membership of each bound update). -/
theorem propTimes_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propTimes st1 i j k = propTimes st2 i j k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Aj : ∀ t c, narrowLo st1 j t c = narrowLo st2 j t c := fun t c => narrowLo_local hj
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bj : ∀ t c, narrowHi st1 j t c = narrowHi st2 j t c := fun t c => narrowHi_local hj
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propTimes, hi, hj, hk, Ai, Aj, Ak, Bi, Bj, Bk]

/-- `divPin` reads only the slot named by its operand (a literal reads no
    domain). -/
theorem divPin_local {st1 st2 : State} {o : DomIntArg}
    (h : ∀ j ∈ o.slots, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    divPin st1 o = divPin st2 o := by
  cases o with
  | lit d => rfl
  | slot j =>
      simp only [divPin, h j (by simp [DomIntArg.slots])]

/-- `propAbs` reads only the two operand/result domains (their extrema). -/
theorem propAbs_local {i k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propAbs st1 i k = propAbs st2 i k := by
  have Ai : ∀ t c, narrowLo st1 i t c = narrowLo st2 i t c := fun t c => narrowLo_local hi
  have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c := fun t c => narrowLo_local hk
  have Bi : ∀ t c, narrowHi st1 i t c = narrowHi st2 i t c := fun t c => narrowHi_local hi
  have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c := fun t c => narrowHi_local hk
  simp only [propAbs, hi, hk, Ai, Ak, Bi, Bk]

/-- `propDiv` reads only the divisor slot's pin and, when both the dividend
    and the result are slots, the dividend/result extrema. -/
theorem propDiv_local {o₁ o₂ r : DomIntArg} {st1 st2 : State}
    (h : ∀ j ∈ o₁.slots ++ o₂.slots ++ r.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propDiv st1 o₁ o₂ r = propDiv st2 o₁ o₂ r := by
  have hpin : divPin st1 o₂ = divPin st2 o₂ :=
    divPin_local (fun j hj =>
      h j (List.mem_append_left _ (List.mem_append_right _ hj)))
  unfold propDiv
  rw [hpin]
  cases hd : divPin st2 o₂ with
  | none => rfl
  | some d =>
      dsimp only
      by_cases hz : d = 0
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz]
        cases o₁ with
        | lit p => cases r <;> rfl
        | slot i =>
            cases r with
            | lit p => rfl
            | slot k =>
                have hi := h i (by simp [DomIntArg.slots])
                have hk := h k (by simp [DomIntArg.slots])
                have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c :=
                  fun t c => narrowLo_local hk
                have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c :=
                  fun t c => narrowHi_local hk
                simp only [hi, hk, Ak, Bk]

/-- `propMod` reads only the divisor slot's pin and, when both the dividend
    and the result are slots, the dividend/result extrema. -/
theorem propMod_local {o₁ o₂ r : DomIntArg} {st1 st2 : State}
    (h : ∀ j ∈ o₁.slots ++ o₂.slots ++ r.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propMod st1 o₁ o₂ r = propMod st2 o₁ o₂ r := by
  have hpin : divPin st1 o₂ = divPin st2 o₂ :=
    divPin_local (fun j hj =>
      h j (List.mem_append_left _ (List.mem_append_right _ hj)))
  unfold propMod
  rw [hpin]
  cases hd : divPin st2 o₂ with
  | none => rfl
  | some d =>
      dsimp only
      by_cases hz : d = 0
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz]
        cases o₁ with
        | lit p => cases r <;> rfl
        | slot i =>
            cases r with
            | lit p => rfl
            | slot k =>
                have hi := h i (by simp [DomIntArg.slots])
                have hk := h k (by simp [DomIntArg.slots])
                have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c :=
                  fun t c => narrowLo_local hk
                have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c :=
                  fun t c => narrowHi_local hk
                simp only [hi, hk, Ak, Bk]

/-- `argLoB` reads only the named slot's integer minimum (a literal reads
    no domain). -/
theorem argLoB_local {st1 st2 : State} {o : DomIntArg}
    (h : ∀ j ∈ o.slots, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    argLoB st1 o = argLoB st2 o := by
  cases o with
  | lit k => rfl
  | slot i => simp only [argLoB, h i (by simp [DomIntArg.slots])]

/-- `argHiB` reads only the named slot's integer maximum. -/
theorem argHiB_local {st1 st2 : State} {o : DomIntArg}
    (h : ∀ j ∈ o.slots, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    argHiB st1 o = argHiB st2 o := by
  cases o with
  | lit k => rfl
  | slot i => simp only [argHiB, h i (by simp [DomIntArg.slots])]

/-- `minArgLo` reads only the operands' named slots. -/
theorem minArgLo_local {st1 st2 : State} {os : List DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    minArgLo st1 os = minArgLo st2 os := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
      cases rest with
      | nil =>
          exact argLoB_local (fun j hj =>
            h j (List.mem_flatMap.mpr ⟨o, by simp, hj⟩))
      | cons o' rest' =>
          simp only [minArgLo]
          rw [argLoB_local (fun j hj =>
                h j (List.mem_flatMap.mpr ⟨o, by simp, hj⟩)),
              ih (fun j hj =>
                h j (by
                  rw [List.flatMap_cons]
                  exact List.mem_append_right _ hj))]

/-- `maxArgHi` reads only the operands' named slots. -/
theorem maxArgHi_local {st1 st2 : State} {os : List DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    maxArgHi st1 os = maxArgHi st2 os := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
      cases rest with
      | nil =>
          exact argHiB_local (fun j hj =>
            h j (List.mem_flatMap.mpr ⟨o, by simp, hj⟩))
      | cons o' rest' =>
          simp only [maxArgHi]
          rw [argHiB_local (fun j hj =>
                h j (List.mem_flatMap.mpr ⟨o, by simp, hj⟩)),
              ih (fun j hj =>
                h j (by
                  rw [List.flatMap_cons]
                  exact List.mem_append_right _ hj))]

/-- `argLoCause` reads only the named slot's integer minimum. -/
theorem argLoCause_local {st1 st2 : State} {o : DomIntArg}
    (h : ∀ j ∈ o.slots, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    argLoCause st1 o = argLoCause st2 o := by
  cases o with
  | lit k => rfl
  | slot i => simp only [argLoCause, h i (by simp [DomIntArg.slots])]

/-- `argHiCause` reads only the named slot's integer maximum. -/
theorem argHiCause_local {st1 st2 : State} {o : DomIntArg}
    (h : ∀ j ∈ o.slots, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    argHiCause st1 o = argHiCause st2 o := by
  cases o with
  | lit k => rfl
  | slot i => simp only [argHiCause, h i (by simp [DomIntArg.slots])]

/-- The flat-mapped lower causes read only the operands' named slots. -/
theorem argLoCauses_local {st1 st2 : State} {os : List DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    os.flatMap (argLoCause st1) = os.flatMap (argLoCause st2) :=
  list_flatMap_congr_mem (fun o ho =>
    argLoCause_local (fun j hj =>
      h j (List.mem_flatMap.mpr ⟨o, ho, hj⟩)))

/-- The flat-mapped upper causes read only the operands' named slots. -/
theorem argHiCauses_local {st1 st2 : State} {os : List DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    os.flatMap (argHiCause st1) = os.flatMap (argHiCause st2) :=
  list_flatMap_congr_mem (fun o ho =>
    argHiCause_local (fun j hj =>
      h j (List.mem_flatMap.mpr ⟨o, ho, hj⟩)))

/-- `propMinGen` reads only the operands' named slots and the result slot. -/
theorem propMinGen_local {st1 st2 : State} {os : List DomIntArg}
    {r : DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots ++ r.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propMinGen st1 os r = propMinGen st2 os r := by
  have hos : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty :=
    fun j hj => h j (List.mem_append_left _ hj)
  have Hlo := minArgLo_local hos
  have Hhi := maxArgHi_local hos
  have Hclo := argLoCauses_local hos
  have Hchi := argHiCauses_local hos
  cases r with
  | lit k => rfl
  | slot k =>
      have hk := h k (List.mem_append_right _ (by simp [DomIntArg.slots]))
      have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c :=
        fun t c => narrowLo_local hk
      have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c :=
        fun t c => narrowHi_local hk
      simp only [propMinGen, Hlo, Hhi, Hclo, Hchi, Ak, Bk]

/-- `propMaxGen` reads only the operands' named slots and the result slot. -/
theorem propMaxGen_local {st1 st2 : State} {os : List DomIntArg}
    {r : DomIntArg}
    (h : ∀ j ∈ os.flatMap DomIntArg.slots ++ r.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propMaxGen st1 os r = propMaxGen st2 os r := by
  have hos : ∀ j ∈ os.flatMap DomIntArg.slots,
      st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty :=
    fun j hj => h j (List.mem_append_left _ hj)
  have Hlo := minArgLo_local hos
  have Hhi := maxArgHi_local hos
  have Hclo := argLoCauses_local hos
  have Hchi := argHiCauses_local hos
  cases r with
  | lit k => rfl
  | slot k =>
      have hk := h k (List.mem_append_right _ (by simp [DomIntArg.slots]))
      have Ak : ∀ t c, narrowLo st1 k t c = narrowLo st2 k t c :=
        fun t c => narrowLo_local hk
      have Bk : ∀ t c, narrowHi st1 k t c = narrowHi st2 k t c :=
        fun t c => narrowHi_local hk
      simp only [propMaxGen, Hlo, Hhi, Hclo, Hchi, Ak, Bk]

/-- `propCheck` reads only the slots `dcSlotsFull dc` names: its readiness
    gate checks their singleton shape, its forced assignment reads their
    singleton values, and its conflict clause lists their falsified
    literals.  The gate makes the empty-domain/out-of-range ambiguity
    harmless (both sides are then unready and return `.stable`). -/
theorem propCheck_local (dc : DomConstraint) {st1 st2 : State}
    (h : ∀ s ∈ dcSlotsFull dc,
      st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    (propCheck dc).run st1 = (propCheck dc).run st2 := by
  have Hsing : ∀ s ∈ dcSlotsFull dc,
      frameSingleton st1.domains s = frameSingleton st2.domains s :=
    fun s hs => by unfold frameSingleton; rw [h s hs]
  have Hready : propCheckReady dc st1.domains = propCheckReady dc st2.domains := by
    unfold propCheckReady
    exact list_all_congr_mem (fun s hs => by rw [Hsing s hs])
  simp only [propCheck, Hready]
  by_cases hr : propCheckReady dc st2.domains = true
  · rw [if_pos hr, if_pos hr]
    have Hsat : dc.satisfiedB (propCheckAssign st1.domains) =
        dc.satisfiedB (propCheckAssign st2.domains) := by
      apply satisfiedB_dcSlotsFull_congr
      intro s hs
      have h1 : (frameSingleton st1.domains s).isSome = true := by
        rw [Hsing s hs]
        exact List.all_eq_true.mp hr s hs
      have h2 : (frameSingleton st2.domains s).isSome = true :=
        List.all_eq_true.mp hr s hs
      obtain ⟨v1, hv1⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨v2, hv2⟩ := Option.isSome_iff_exists.mp h2
      have hvv : v1 = v2 := by
        have heq := Hsing s hs
        rw [hv1, hv2] at heq
        exact Option.some.inj heq
      subst hvv
      rw [propCheckAssign_getElem? hv1, propCheckAssign_getElem? hv2]
    rw [Hsat]
    by_cases hsat : dc.satisfiedB (propCheckAssign st2.domains) = true
    · rw [if_pos hsat, if_pos hsat]
    · rw [if_neg hsat, if_neg hsat]
      have Hconf : propCheckConflict dc st1.domains =
          propCheckConflict dc st2.domains := by
        unfold propCheckConflict
        exact list_filterMap_congr_mem (fun s hs => by rw [Hsing s hs])
      rw [Hconf]
  · rw [if_neg hr, if_neg hr]

theorem propLeConstHi_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLeConstHi st1 i c = propLeConstHi st2 i c := by
  simp only [propLeConstHi, narrowHi_local hi]

theorem propLeConstLo_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLeConstLo st1 i c = propLeConstLo st2 i c := by
  simp only [propLeConstLo, narrowLo_local hi]

theorem propLtConstHi_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLtConstHi st1 i c = propLtConstHi st2 i c := by
  simp only [propLtConstHi, narrowHi_local hi]

theorem propLtConstLo_local {i : Nat} {c : Int} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLtConstLo st1 i c = propLtConstLo st2 i c := by
  simp only [propLtConstLo, narrowLo_local hi]

theorem propConstEq_local {i : Nat} {v : Value} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propConstEq st1 i v = propConstEq st2 i v := by
  have A : ∀ k c, narrowHi st1 i k c = narrowHi st2 i k c := fun k c => narrowHi_local hi
  have B : ∀ k c, narrowLo st1 i k c = narrowLo st2 i k c := fun k c => narrowLo_local hi
  simp only [propConstEq, hi, A, B]

theorem propBoolNot_local {i j : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propBoolNot st1 i j = propBoolNot st2 i j := by
  have Ai : ∀ b, domBoolPin st1.domains i b = domBoolPin st2.domains i b :=
    fun b => domBoolPin_local hi
  have Aj : ∀ b, domBoolPin st1.domains j b = domBoolPin st2.domains j b :=
    fun b => domBoolPin_local hj
  have Bi : ∀ b c, implyBool st1 i b c = implyBool st2 i b c := fun b c => implyBool_local hi
  have Bj : ∀ b c, implyBool st1 j b c = implyBool st2 j b c := fun b c => implyBool_local hj
  simp only [propBoolNot, Ai, Aj, Bi, Bj]

theorem propBoolAnd_local {i j k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
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
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
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
    (frameState f).domains.getD a.slot Dom.empty = (frameState g).domains.getD a.slot Dom.empty :=
  watchStamp_getD h a ha

/-- A slot list whose `intLe` atoms all lie in the footprint inherits the
    pointwise domain equalities from one watch-stamp equality. -/
theorem watchStamp_getD_forall {f g : BranchFrame} {ws : List Atom} {is : List Nat}
    (h : watchStamp f ws = watchStamp g ws)
    (hmem : ∀ i ∈ is, Atom.intLe i 0 ∈ ws) :
    ∀ i ∈ is, (frameState f).domains.getD i Dom.empty = (frameState g).domains.getD i Dom.empty :=
  fun i hi => watchStamp_getD h (.intLe i 0) (hmem i hi)

/-- The `intLe` atoms of a list are members of its mapped footprint. -/
theorem mem_map_intLe {is : List Nat} {i : Nat} (hi : i ∈ is) :
    Atom.intLe i 0 ∈ is.map (fun j => Atom.intLe j 0) := by
  induction is with
  | nil => cases hi
  | cons j js ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hi)

/-- The pointwise domain equalities of the `intLe`-mapped footprint. -/
theorem watchStamp_getD_map_intLe {f g : BranchFrame} {is : List Nat}
    (h : watchStamp f (is.map fun i => Atom.intLe i 0) =
         watchStamp g (is.map fun i => Atom.intLe i 0)) :
    ∀ i ∈ is, (frameState f).domains.getD i Dom.empty = (frameState g).domains.getD i Dom.empty :=
  watchStamp_getD_forall h (fun _ hi => mem_map_intLe hi)

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

theorem propMin_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propMin st i j k } := by
  intro f g hstamp
  exact propMin_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

theorem propMax_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propMax st i j k } := by
  intro f g hstamp
  exact propMax_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-- `propTimes` watches exactly its three slots. -/
theorem propTimes_propLocal (i j k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe k 0],
                   run := fun st => propTimes st i j k } := by
  intro f g hstamp
  exact propTimes_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe j 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-- `propAbs` watches its two slots. -/
theorem propAbs_propLocal (i k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe k 0],
                   run := fun st => propAbs st i k } := by
  intro f g hstamp
  exact propAbs_local (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-- `propDiv` watches the slots named by its three operands. -/
theorem propDiv_propLocal (o₁ o₂ r : DomIntArg) :
    PropLocalOne { watches := (o₁.slots ++ o₂.slots ++ r.slots).map
                     (fun j => Atom.intLe j 0),
                   run := fun st => propDiv st o₁ o₂ r } := by
  intro f g hstamp
  exact propDiv_local (fun j hj =>
    watchStamp_getD hstamp (.intLe j 0) (mem_map_intLe hj))

/-- `propMod` watches the slots named by its three operands. -/
theorem propMod_propLocal (o₁ o₂ r : DomIntArg) :
    PropLocalOne { watches := (o₁.slots ++ o₂.slots ++ r.slots).map
                     (fun j => Atom.intLe j 0),
                   run := fun st => propMod st o₁ o₂ r } := by
  intro f g hstamp
  exact propMod_local (fun j hj =>
    watchStamp_getD hstamp (.intLe j 0) (mem_map_intLe hj))

/-- `propMinGen` watches the operands' named slots and the result slot. -/
theorem propMinGen_propLocal (os : List DomIntArg) (r : DomIntArg) :
    PropLocalOne { watches := (os.flatMap DomIntArg.slots ++ r.slots).map
                     (fun j => Atom.intLe j 0),
                   run := fun st => propMinGen st os r } := by
  intro f g hstamp
  exact propMinGen_local (fun j hj =>
    watchStamp_getD hstamp (.intLe j 0) (mem_map_intLe hj))

/-- `propMaxGen` watches the operands' named slots and the result slot. -/
theorem propMaxGen_propLocal (os : List DomIntArg) (r : DomIntArg) :
    PropLocalOne { watches := (os.flatMap DomIntArg.slots ++ r.slots).map
                     (fun j => Atom.intLe j 0),
                   run := fun st => propMaxGen st os r } := by
  intro f g hstamp
  exact propMaxGen_local (fun j hj =>
    watchStamp_getD hstamp (.intLe j 0) (mem_map_intLe hj))

/-- `propCheck` watches exactly the slots `dcSlotsFull dc` names. -/
theorem propCheck_propLocal (dc : DomConstraint) :
    PropLocalOne { watches := (dcSlotsFull dc).map (fun s => Atom.intLe s 0),
                   run := (propCheck dc).run } := by
  intro f g hstamp
  exact propCheck_local dc (fun s hs =>
    watchStamp_getD hstamp (.intLe s 0) (mem_map_intLe hs))

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

/-- `propArrayBoolAnd` reads only the target slot and the input slots (the
    alias guard is list-only, and every `find?`/`all` test is a Boolean-pin
    read of those slots). -/
theorem propArrayBoolAnd_local {is : List Nat} {k : Nat} {st1 st2 : State}
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty)
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propArrayBoolAnd st1 is k = propArrayBoolAnd st2 is k := by
  have Hpint : is.all (fun i => domBoolPin st1.domains i true) =
      is.all (fun i => domBoolPin st2.domains i true) :=
    list_all_congr_mem (fun i hi => domBoolPin_local (his i hi))
  have Hpinf : is.find? (fun i => domBoolPin st1.domains i false) =
      is.find? (fun i => domBoolPin st2.domains i false) :=
    list_find?_congr_mem (fun i hi => domBoolPin_local (his i hi))
  have Hpinnt : is.find? (fun i => !domBoolPin st1.domains i true) =
      is.find? (fun i => !domBoolPin st2.domains i true) :=
    list_find?_congr_mem (fun i hi => by rw [domBoolPin_local (his i hi)])
  have Hkt := domBoolPin_local (doms1 := st1.domains) (doms2 := st2.domains)
    (s := k) (b := true) hk
  have Hkf := domBoolPin_local (doms1 := st1.domains) (doms2 := st2.domains)
    (s := k) (b := false) hk
  unfold propArrayBoolAnd
  by_cases hmem : k ∈ is
  · rw [if_pos hmem, if_pos hmem]
  · rw [if_neg hmem, if_neg hmem]
    by_cases hall : is.all (fun i => domBoolPin st1.domains i true) = true
    · have hall2 : is.all (fun i => domBoolPin st2.domains i true) = true := by
        rw [← Hpint]; exact hall
      rw [if_pos hall, if_pos hall2]
      exact implyBool_local hk
    · have hall2 : is.all (fun i => domBoolPin st2.domains i true) ≠ true := by
        rw [← Hpint]; exact hall
      rw [if_neg hall, if_neg hall2]
      cases hfind : is.find? (fun i => domBoolPin st1.domains i false) with
      | some i =>
          have hfind2 : is.find? (fun i => domBoolPin st2.domains i false) = some i := by
            rw [← Hpinf]; exact hfind
          rw [hfind2]
          exact implyBool_local hk
      | none =>
          have hfind2 : is.find? (fun i => domBoolPin st2.domains i false) = none := by
            rw [← Hpinf]; exact hfind
          rw [hfind2]
          by_cases hkt : domBoolPin st1.domains k true = true
          · have hkt2 : domBoolPin st2.domains k true = true := by
              rw [← Hkt]; exact hkt
            rw [if_pos hkt, if_pos hkt2]
            cases hfind3 : is.find? (fun i => !domBoolPin st1.domains i true) with
            | some i =>
                have hfind4 : is.find? (fun i => !domBoolPin st2.domains i true) = some i := by
                  rw [← Hpinnt]; exact hfind3
                have hi : i ∈ is := List.mem_of_find?_eq_some hfind3
                rw [hfind4]
                exact implyBool_local (his i hi)
            | none =>
                have hfind4 : is.find? (fun i => !domBoolPin st2.domains i true) = none := by
                  rw [← Hpinnt]; exact hfind3
                rw [hfind4]
          · have hkt2 : domBoolPin st2.domains k true ≠ true := by
              rw [← Hkt]; exact hkt
            rw [if_neg hkt, if_neg hkt2]
            by_cases hkf : domBoolPin st1.domains k false = true
            · have hkf2 : domBoolPin st2.domains k false = true := by
                rw [← Hkf]; exact hkf
              rw [if_pos hkf, if_pos hkf2]
              cases is with
              | nil => rfl
              | cons a as =>
                  cases as with
                  | nil =>
                      show (if aba_domBoolOnlyB (Dom.enum (st1.domains.getD a Dom.empty)) then
                          implyBool st1 a false [posBool a false, posBool k true]
                        else .stable) =
                        (if aba_domBoolOnlyB (Dom.enum (st2.domains.getD a Dom.empty)) then
                          implyBool st2 a false [posBool a false, posBool k true]
                        else .stable)
                      rw [his a (by simp)]
                      by_cases hb : aba_domBoolOnlyB (Dom.enum (st2.domains.getD a Dom.empty))
                      · rw [if_pos hb, if_pos hb]
                        exact implyBool_local (his a (by simp))
                      · rw [if_neg hb, if_neg hb]
                  | cons b bs => rfl
            · have hkf2 : domBoolPin st2.domains k false ≠ true := by
                rw [← Hkf]; exact hkf
              rw [if_neg hkf, if_neg hkf2]

/-- `propArrayBoolAnd` watches the target slot and the input slots. -/
theorem propArrayBoolAnd_propLocal (is : List Nat) (k : Nat) :
    PropLocalOne { watches := Atom.intLe k 0 :: is.map (fun i => Atom.intLe i 0),
                   run := fun st => propArrayBoolAnd st is k } := by
  intro f g hstamp
  have hk : (frameState f).domains.getD k Dom.empty = (frameState g).domains.getD k Dom.empty :=
    watchStamp_getD hstamp (.intLe k 0) (by simp)
  have his : ∀ i ∈ is, (frameState f).domains.getD i Dom.empty =
      (frameState g).domains.getD i Dom.empty :=
    watchStamp_getD_forall hstamp (fun _ hi => List.mem_cons_of_mem _ (mem_map_intLe hi))
  exact propArrayBoolAnd_local hk his


/-! ## Reified binary comparisons (PLAN P3 batch 2) -/

/-- The integer-only operand guard reads each listed slot's domain only; the
    slot count is absorbed by the empty-domain case of each conjunct. -/
theorem domsIntOnlyB_local {doms1 doms2 : List Domain} {is : List Nat}
    (h : ∀ i ∈ is, doms1.getD i Dom.empty = doms2.getD i Dom.empty) :
    domsIntOnlyB doms1 is = domsIntOnlyB doms2 is := by
  unfold domsIntOnlyB
  refine list_all_congr_mem ?_
  intro i hi
  have hd := h i hi
  by_cases hemp : doms1.getD i Dom.empty = Dom.empty
  · have hemp2 : doms2.getD i Dom.empty = Dom.empty := by rw [← hd, hemp]
    have hz1 : (doms1.getD i Dom.empty).length = 0 := by rw [hemp]; rfl
    have hz2 : (doms2.getD i Dom.empty).length = 0 := by rw [hemp2]; rfl
    rw [hz1, hz2]
    simp
  · have hlt1 : i < doms1.length := by
      by_cases h : i < doms1.length
      · exact h
      · exact absurd (getD_nil_of_length_le h) hemp
    have hlt2 : i < doms2.length := by
      by_cases h : i < doms2.length
      · exact h
      · have e : doms2.getD i Dom.empty = Dom.empty := getD_nil_of_length_le h
        rw [← hd] at e
        exact absurd e hemp
    have e1 : doms1.getD i Dom.empty = doms1[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt1]
      rfl
    have e2 : doms2.getD i Dom.empty = doms2[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]
      rfl
    have hii : doms1[i] = doms2[i] := by rw [← e1, ← e2]; exact hd
    rw [e1, e2, hii]
    simp [hlt1, hlt2]

/-! ### Variable-table element locality (PLAN P3 batch 6) -/

/-- `firstBadView` is determined by its domain and its pointwise keep test. -/
theorem firstBadView_local {d1 d2 : List Value} {k1 k2 : Int → Bool}
    (hd : d1 = d2) (hk : ∀ w, k1 w = k2 w) :
    firstBadView d1 k1 = firstBadView d2 k2 := by
  subst hd
  unfold firstBadView
  have hfun : (fun v => (Value.intView v).bind
        (fun w => if k1 w then none else some w)) =
      (fun v => (Value.intView v).bind
        (fun w => if k2 w then none else some w)) := by
    funext v
    cases h : Value.intView v with
    | none => rfl
    | some w => simp only [Option.bind_some, hk w]
  rw [hfun]

/-- `avieTableMemB` reads only the table slots. -/
theorem avieTableMemB_local {st1 st2 : State} {is : List Nat} {w : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    avieTableMemB st1 is w = avieTableMemB st2 is w := by
  unfold avieTableMemB
  exact list_any_congr_mem (fun j hj => by rw [slotEnum_congr (his j hj)])

/-- `aviePinTargetOkB` reads only the entry slot selected from `is`. -/
theorem aviePinTargetOkB_local {st1 st2 : State} {is : List Nat}
    {idx : Int} {v : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    aviePinTargetOkB st1 is idx v = aviePinTargetOkB st2 is idx v := by
  unfold aviePinTargetOkB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h))]

/-- `aviePinTargetRes` reads only the entry slot selected from `is`. -/
theorem aviePinTargetRes_local {st1 st2 : State} {is : List Nat}
    {i k : Nat} {idx : Int} {v : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    aviePinTargetRes st1 is i k idx v = aviePinTargetRes st2 is i k idx v := by
  unfold aviePinTargetRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h))]

/-- `avieBelowBadB` reads the entry slot and the target slot. -/
theorem avieBelowBadB_local {st1 st2 : State} {is : List Nat} {idx : Int}
    {k : Nat}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieBelowBadB st1 is idx k = avieBelowBadB st2 is idx k := by
  unfold avieBelowBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), hk]

/-- `avieBelowRes` reads the entry slot and the target slot. -/
theorem avieBelowRes_local {st1 st2 : State} {is : List Nat} {i k : Nat}
    {idx : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieBelowRes st1 is i k idx = avieBelowRes st2 is i k idx := by
  unfold avieBelowRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), hk]

/-- `avieAboveBadB` reads the entry slot and the target slot. -/
theorem avieAboveBadB_local {st1 st2 : State} {is : List Nat} {idx : Int}
    {k : Nat}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieAboveBadB st1 is idx k = avieAboveBadB st2 is idx k := by
  unfold avieAboveBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), hk]

/-- `avieAboveRes` reads the entry slot and the target slot. -/
theorem avieAboveRes_local {st1 st2 : State} {is : List Nat} {i k : Nat}
    {idx : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieAboveRes st1 is i k idx = avieAboveRes st2 is i k idx := by
  unfold avieAboveRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), hk]

/-- `avieSingleBadB` reads the entry slot and the target slot. -/
theorem avieSingleBadB_local {st1 st2 : State} {is : List Nat} {idx : Int}
    {k : Nat}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieSingleBadB st1 is idx k = avieSingleBadB st2 is idx k := by
  unfold avieSingleBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), slotEnum_congr hk]

/-- `avieSingleRes` reads the entry slot and the target slot. -/
theorem avieSingleRes_local {st1 st2 : State} {is : List Nat} {i k : Nat}
    {idx : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avieSingleRes st1 is i k idx = avieSingleRes st2 is i k idx := by
  unfold avieSingleRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [his j (avieEntry_mem h), slotEnum_congr hk]

/-- `propArrayVarIntElement` reads only the index slot, the target slot and
    the table slots of `is`: equal domains there give equal runs. -/
theorem propArrayVarIntElement_local {st1 st2 : State} {is : List Nat}
    {i k : Nat}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty)
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propArrayVarIntElement st1 is i k = propArrayVarIntElement st2 is i k := by
  have Hguard : domsIntOnlyB st1.domains (i :: k :: is) =
      domsIntOnlyB st2.domains (i :: k :: is) := by
    refine domsIntOnlyB_local ?_
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hi
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hk
    · exact his s hs
  unfold propArrayVarIntElement
  rw [slotEnum_congr hi, slotEnum_congr hk, Hguard]
  by_cases hik : i = k
  · rw [if_pos hik, if_pos hik]
  · rw [if_neg hik, if_neg hik]
    by_cases helem : is.elem i || is.elem k
    · rw [if_pos helem, if_pos helem]
    · rw [if_neg helem, if_neg helem]
      by_cases hnd : decide is.Nodup = false
      · rw [if_pos hnd, if_pos hnd]
      · rw [if_neg hnd, if_neg hnd]
        by_cases hd : domsIntOnlyB st2.domains (i :: k :: is) = false
        · rw [if_pos hd, if_pos hd]
        · rw [if_neg hd, if_neg hd]
          split
          · -- pinned index: `i`'s domain is the raw singleton `[.int idx]`
            rename_i idx hdi
            cases hent : avieEntry is idx with
            | none => rfl
            | some j =>
                dsimp only
                rw [slotEnum_congr (his j (avieEntry_mem hent))]
          · -- unpinned index
            split
            · -- pinned target: `k`'s domain is the raw singleton `[.int v]`
              rename_i v hdk
              have HfbPin : firstBadView (slotEnum st2.domains i)
                    (fun idx => aviePinTargetOkB st1 is idx v) =
                  firstBadView (slotEnum st2.domains i)
                    (fun idx => aviePinTargetOkB st2 is idx v) := by
                rw [show (fun idx => aviePinTargetOkB st1 is idx v) =
                    (fun idx => aviePinTargetOkB st2 is idx v) from
                  funext (fun idx => aviePinTargetOkB_local his)]
              rw [HfbPin]
              split
              · rename_i idx hfb
                exact aviePinTargetRes_local his
              · rfl
            · -- unpinned target
              split
              · rename_i idx hfb
                rfl
              · have HfbBelow : firstBadView (slotEnum st2.domains i)
                    (fun idx => !avieBelowBadB st1 is idx k) =
                  firstBadView (slotEnum st2.domains i)
                    (fun idx => !avieBelowBadB st2 is idx k) := by
                  rw [show (fun idx => !avieBelowBadB st1 is idx k) =
                      (fun idx => !avieBelowBadB st2 is idx k) from
                    funext (fun idx => by rw [avieBelowBadB_local his hk])]
                rw [HfbBelow]
                split
                · rename_i idx hfb
                  exact avieBelowRes_local his hk
                · have HfbAbove : firstBadView (slotEnum st2.domains i)
                      (fun idx => !avieAboveBadB st1 is idx k) =
                    firstBadView (slotEnum st2.domains i)
                      (fun idx => !avieAboveBadB st2 is idx k) := by
                    rw [show (fun idx => !avieAboveBadB st1 is idx k) =
                        (fun idx => !avieAboveBadB st2 is idx k) from
                      funext (fun idx => by rw [avieAboveBadB_local his hk])]
                  rw [HfbAbove]
                  split
                  · rename_i idx hfb
                    exact avieAboveRes_local his hk
                  · have HfbSingle : firstBadView (slotEnum st2.domains i)
                        (fun idx => !avieSingleBadB st1 is idx k) =
                      firstBadView (slotEnum st2.domains i)
                        (fun idx => !avieSingleBadB st2 is idx k) := by
                      rw [show (fun idx => !avieSingleBadB st1 is idx k) =
                          (fun idx => !avieSingleBadB st2 is idx k) from
                        funext (fun idx => by rw [avieSingleBadB_local his hk])]
                    rw [HfbSingle]
                    split
                    · rename_i idx hfb
                      exact avieSingleRes_local his hk
                    · have HfbTable : firstBadView (slotEnum st2.domains k)
                          (fun w => avieTableMemB st1 is w) =
                        firstBadView (slotEnum st2.domains k)
                          (fun w => avieTableMemB st2 is w) := by
                        rw [show (fun w => avieTableMemB st1 is w) =
                            (fun w => avieTableMemB st2 is w) from
                          funext (fun w => avieTableMemB_local his)]
                      rw [HfbTable]

/-! ### Variable-table Boolean element locality (PLAN P3 batch 7) -/

/-- `avbeTableMemB` reads only the table slots. -/
theorem avbeTableMemB_local {st1 st2 : State} {is : List Nat} {b : Bool}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    avbeTableMemB st1 is b = avbeTableMemB st2 is b := by
  unfold avbeTableMemB
  exact list_any_congr_mem (fun j hj => by rw [slotEnum_congr (his j hj)])

/-- `avbePinTargetOkB` reads only the entry slot selected from `is`. -/
theorem avbePinTargetOkB_local {st1 st2 : State} {is : List Nat}
    {idx : Int} {v : Bool}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    avbePinTargetOkB st1 is idx v = avbePinTargetOkB st2 is idx v := by
  unfold avbePinTargetOkB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h))]

/-- `avbePinTargetRes` reads only the entry slot selected from `is`. -/
theorem avbePinTargetRes_local {st1 st2 : State} {is : List Nat}
    {i k : Nat} {idx : Int} {v : Bool}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    avbePinTargetRes st1 is i k idx v = avbePinTargetRes st2 is i k idx v := by
  unfold avbePinTargetRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h))]

/-- `avbeSingleBadB` reads the entry slot and the target slot. -/
theorem avbeSingleBadB_local {st1 st2 : State} {is : List Nat} {idx : Int}
    {k : Nat}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avbeSingleBadB st1 is idx k = avbeSingleBadB st2 is idx k := by
  unfold avbeSingleBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h)), slotEnum_congr hk]

/-- `avbeSingleRes` reads the entry slot and the target slot. -/
theorem avbeSingleRes_local {st1 st2 : State} {is : List Nat} {i k : Nat}
    {idx : Int}
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    avbeSingleRes st1 is i k idx = avbeSingleRes st2 is i k idx := by
  unfold avbeSingleRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      dsimp only
      rw [slotEnum_congr (his j (avieEntry_mem h)), slotEnum_congr hk]

/-- The family guard reads the index slot, the target slot and every table
    slot. -/
theorem avbeGuardB_local {st1 st2 : State} {is : List Nat} {i k : Nat}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty)
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    avbeGuardB st1 is i k = avbeGuardB st2 is i k := by
  unfold avbeGuardB
  have H1 : domsIntOnlyB st1.domains [i] = domsIntOnlyB st2.domains [i] :=
    domsIntOnlyB_local (fun s hs => by
      rcases List.mem_singleton.mp hs with rfl
      exact hi)
  have H2 : domBoolOnlyB (slotEnum st1.domains k) =
      domBoolOnlyB (slotEnum st2.domains k) := by rw [slotEnum_congr hk]
  have H3 : is.all (fun j => domBoolOnlyB (slotEnum st1.domains j)) =
      is.all (fun j => domBoolOnlyB (slotEnum st2.domains j)) :=
    list_all_congr_mem (fun j hj => by rw [slotEnum_congr (his j hj)])
  rw [H1, H2, H3]

/-- `propArrayVarBoolElement` reads only the index slot, the target slot and
    the table slots of `is`. -/
theorem propArrayVarBoolElement_local {st1 st2 : State} {is : List Nat}
    {i k : Nat}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty)
    (his : ∀ j ∈ is, st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty) :
    propArrayVarBoolElement st1 is i k = propArrayVarBoolElement st2 is i k := by
  have Hguard := avbeGuardB_local hi hk his
  unfold propArrayVarBoolElement
  rw [slotEnum_congr hi, slotEnum_congr hk, Hguard]
  by_cases hik : i = k
  · rw [if_pos hik, if_pos hik]
  · rw [if_neg hik, if_neg hik]
    by_cases helem : is.elem i || is.elem k
    · rw [if_pos helem, if_pos helem]
    · rw [if_neg helem, if_neg helem]
      by_cases hnd : decide is.Nodup = false
      · rw [if_pos hnd, if_pos hnd]
      · rw [if_neg hnd, if_neg hnd]
        by_cases hg : avbeGuardB st2 is i k = false
        · rw [if_pos hg, if_pos hg]
        · rw [if_neg hg, if_neg hg]
          split
          · -- pinned index
            rename_i idx hdi
            cases hent : avieEntry is idx with
            | none => rfl
            | some j =>
                dsimp only
                have hj := his j (avieEntry_mem hent)
                rw [slotEnum_congr hj]
                split
                · rename_i b hfb
                  unfold avbeResTarget
                  rw [implyBool_local hk]
                · split
                  · rename_i b hfb
                    unfold avbeResEntry
                    rw [implyBool_local hj]
                  · rfl
          · -- unpinned index
            split
            · -- pinned target
              rename_i v hdk
              have hfun : (fun idx => avbePinTargetOkB st1 is idx v) =
                  (fun idx => avbePinTargetOkB st2 is idx v) :=
                funext (fun idx => avbePinTargetOkB_local his)
              rw [hfun]
              split
              · rename_i idx hfb
                exact avbePinTargetRes_local his
              · rfl
            · -- unpinned target
              split
              · rename_i idx hfb
                rfl
              · have hfun : (fun idx => !avbeSingleBadB st1 is idx k) =
                    (fun idx => !avbeSingleBadB st2 is idx k) :=
                  funext (fun idx => by rw [avbeSingleBadB_local his hk])
                rw [hfun]
                split
                · rename_i idx hfb
                  exact avbeSingleRes_local his hk
                · have hfun2 : (fun b => avbeTableMemB st1 is b) =
                      (fun b => avbeTableMemB st2 is b) :=
                    funext (fun b => avbeTableMemB_local his)
                  rw [hfun2]
                  split
                  · rename_i b hfb
                    unfold avbeResNoSupp
                    rw [implyBool_local hk]
                  · rfl

/-- `propEqReifSlot` reads the reif slot's pin and the two operand domains. -/
theorem propEqReifSlot_local {i j r : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty) :
    propEqReifSlot st1 i j r = propEqReifSlot st2 i j r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have He := propEq_local hi hj
  have Hn := propNe_local hi hj
  simp only [propEqReifSlot, Ar true, Ar false, He, Hn]

/-- `propNeReifSlot` reads the reif slot's pin and the two operand domains. -/
theorem propNeReifSlot_local {i j r : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty) :
    propNeReifSlot st1 i j r = propNeReifSlot st2 i j r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have He := propEq_local hi hj
  have Hn := propNe_local hi hj
  simp only [propNeReifSlot, Ar true, Ar false, He, Hn]

/-- The unpinned bounds arm `propLeReifB` reads only the reif slot and the
    two operand domains (the `domsIntOnlyB` guard is local by
    `domsIntOnlyB_local`). -/
theorem propLeReifB_local {i j r : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty) :
    propLeReifB st1 i j r = propLeReifB st2 i j r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Hd : domsIntOnlyB st1.domains [i, j] = domsIntOnlyB st2.domains [i, j] := by
    refine domsIntOnlyB_local ?_
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hi
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact hj
      · cases hs
  simp only [propLeReifB, Ar true, Ar false, hr, hi, hj, Hd]

/-- The strengthened `leReifSlot` run reads the reif slot and both operands. -/
theorem propLeReifSlotB_local {i j r : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hj : st1.domains.getD j Dom.empty = st2.domains.getD j Dom.empty)
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty) :
    propLeReifSlotB st1 i j r = propLeReifSlotB st2 i j r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Hl := propLe_local hi hj
  have Ht := propLt_local hj hi
  have Hb := propLeReifB_local hi hj hr
  simp only [propLeReifSlotB, Ar true, Ar false, Hl, Ht, Hb]

/-- The pinned `linEqReif` delegation reads the reif slot and the constraint
    slots. -/
theorem propLinEqReif_local {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {st1 st2 : State}
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty)
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinEqReif st1 coeffs is b r = propLinEqReif st2 coeffs is b r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Hd := domsIntOnlyB_local his
  have He : propLinEq2 st1 coeffs is b = propLinEq2 st2 coeffs is b :=
    propLinEq2_local (st1 := st1) (st2 := st2) (coeffs := coeffs) (b := b) his
  have Hn : propLinNe st1 coeffs is b = propLinNe st2 coeffs is b :=
    propLinNe_local (st1 := st1) (st2 := st2) (coeffs := coeffs) (b := b) his
  simp only [propLinEqReif, Ar true, Ar false, Hd, He, Hn]

/-- The pinned `linNeReif` delegation reads the reif slot and the constraint
    slots. -/
theorem propLinNeReif_local {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {st1 st2 : State}
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty)
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinNeReif st1 coeffs is b r = propLinNeReif st2 coeffs is b r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Hd := domsIntOnlyB_local his
  have He : propLinEq2 st1 coeffs is b = propLinEq2 st2 coeffs is b :=
    propLinEq2_local (st1 := st1) (st2 := st2) (coeffs := coeffs) (b := b) his
  have Hn : propLinNe st1 coeffs is b = propLinNe st2 coeffs is b :=
    propLinNe_local (st1 := st1) (st2 := st2) (coeffs := coeffs) (b := b) his
  simp only [propLinNeReif, Ar true, Ar false, Hd, He, Hn]

/-- The dual unpinned bounds arm `propLinLeReifBDual` reads only the
    constraint slots (its emitted clause carries the reif literal as a
    constant index and the min causes of `is`). -/
theorem propLinLeReifBDual_local {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {st1 st2 : State}
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinLeReifBDual st1 coeffs is b r = propLinLeReifBDual st2 coeffs is b r := by
  have hpair : ∀ p ∈ coeffs.zip is,
      st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty :=
    fun p hp => his p.2 (mem_zip_snd hp)
  have hs := sumMin_local hpair
  have hc := linCausesMin_local hpair
  simp only [propLinLeReifBDual, hs, hc]

/-- The unpinned bounds arm `propLinLeReifB` reads only the reif slot and the
    constraint slots. -/
theorem propLinLeReifB_local {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {st1 st2 : State}
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty)
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinLeReifB st1 coeffs is b r = propLinLeReifB st2 coeffs is b r := by
  have hpair : ∀ p ∈ coeffs.zip is,
      st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty :=
    fun p hp => his p.2 (mem_zip_snd hp)
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Honly : domBoolOnlyB (Dom.enum (st1.domains.getD r Dom.empty)) =
      domBoolOnlyB (Dom.enum (st2.domains.getD r Dom.empty)) := by rw [hr]
  have Hd := domsIntOnlyB_local his
  have Hall := all_minContrib_isSome_local hpair
  have Hmax := sumMax_local hpair
  have Hcx := linCausesMax_local hpair
  have Hdual := propLinLeReifBDual_local (coeffs := coeffs) (is := is) (b := b)
    (r := r) (st1 := st1) (st2 := st2) his
  simp only [propLinLeReifB, Ar true, Ar false, Honly, Hd, Hall, Hmax, Hcx, Hdual]

/-- The full `linLeReif` delegation reads the reif slot and the constraint
    slots in all three arms (pinned true, pinned false, unpinned bounds). -/
theorem propLinLeReif_local {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {st1 st2 : State}
    (hr : st1.domains.getD r Dom.empty = st2.domains.getD r Dom.empty)
    (his : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinLeReif st1 coeffs is b r = propLinLeReif st2 coeffs is b r := by
  have Ar : ∀ b, domBoolPin st1.domains r b = domBoolPin st2.domains r b :=
    fun b => domBoolPin_local hr
  have Hd := domsIntOnlyB_local his
  have Hle : propLinLe2 st1 coeffs is b = propLinLe2 st2 coeffs is b :=
    propLinLe2_local (st1 := st1) (st2 := st2) (coeffs := coeffs) (b := b) his
  have HleNeg : propLinLe2 st1 (coeffs.map (fun c => -c)) is (-(b + 1))
      = propLinLe2 st2 (coeffs.map (fun c => -c)) is (-(b + 1)) :=
    propLinLe2_local (st1 := st1) (st2 := st2)
      (coeffs := coeffs.map (fun c => -c)) (b := -(b + 1)) his
  have Hb := propLinLeReifB_local (coeffs := coeffs) (is := is) (b := b)
    (r := r) (st1 := st1) (st2 := st2) hr his
  simp only [propLinLeReif, Ar true, Ar false, Hd, Hle, HleNeg, Hb]

/-- `propBool2intSlot` reads only the source and target domains. -/
theorem propBool2intSlot_local {i k : Nat} {st1 st2 : State}
    (hi : st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty)
    (hk : st1.domains.getD k Dom.empty = st2.domains.getD k Dom.empty) :
    propBool2intSlot st1 i k = propBool2intSlot st2 i k := by
  simp only [propBool2intSlot, domBoolPin, implyBool, slotEnum, hi, hk]
  rfl

/-- `propArrayIntElement` watches exactly its index and target slots (the
    table is a compile-time constant). -/
theorem propArrayIntElement_propLocal (xs : List Int) (i k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe k 0],
                   run := fun st => propArrayIntElement st xs i k } := by
  intro f g hstamp
  exact propArrayIntElement_local
    (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-- `propArrayVarIntElement` watches the index slot, the target slot and
    every table slot of `is`. -/
theorem propArrayVarIntElement_propLocal (is : List Nat) (i k : Nat) :
    PropLocalOne { watches := Atom.intLe i 0 :: Atom.intLe k 0 ::
                     is.map (fun j => Atom.intLe j 0),
                   run := fun st => propArrayVarIntElement st is i k } := by
  intro f g hstamp
  have hi := watchStamp_getD hstamp (.intLe i 0) (by simp)
  have hk := watchStamp_getD hstamp (.intLe k 0) (by simp)
  have his : ∀ j ∈ is, (frameState f).domains.getD j Dom.empty =
      (frameState g).domains.getD j Dom.empty :=
    watchStamp_getD_forall hstamp
      (fun j hj => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (mem_map_intLe hj)))
  exact propArrayVarIntElement_local hi hk his

/-- `propArrayVarBoolElement` watches the index slot, the target slot and
    every table slot of `is`. -/
theorem propArrayVarBoolElement_propLocal (is : List Nat) (i k : Nat) :
    PropLocalOne { watches := Atom.intLe i 0 :: Atom.intLe k 0 ::
                     is.map (fun j => Atom.intLe j 0),
                   run := fun st => propArrayVarBoolElement st is i k } := by
  intro f g hstamp
  have hi := watchStamp_getD hstamp (.intLe i 0) (by simp)
  have hk := watchStamp_getD hstamp (.intLe k 0) (by simp)
  have his : ∀ j ∈ is, (frameState f).domains.getD j Dom.empty =
      (frameState g).domains.getD j Dom.empty :=
    watchStamp_getD_forall hstamp
      (fun j hj => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (mem_map_intLe hj)))
  exact propArrayVarBoolElement_local hi hk his

/-- `propLinLe2` watches exactly its constraint's slots. -/
theorem propLinLe2_propLocal (coeffs : List Int) (is : List Nat) (b : Int) :
    PropLocalOne { watches := is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinLe2 st coeffs is b } := by
  intro f g hstamp
  exact propLinLe2_local (watchStamp_getD_map_intLe hstamp)

/-- `propLinEq2` watches exactly its constraint's slots. -/
theorem propLinEq2_propLocal (coeffs : List Int) (is : List Nat) (b : Int) :
    PropLocalOne { watches := is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinEq2 st coeffs is b } := by
  intro f g hstamp
  exact propLinEq2_local (watchStamp_getD_map_intLe hstamp)

/-- `propLinNe` watches exactly its constraint's slots. -/
theorem propLinNe_propLocal (coeffs : List Int) (is : List Nat) (b : Int) :
    PropLocalOne { watches := is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinNe st coeffs is b } := by
  intro f g hstamp
  exact propLinNe_local (watchStamp_getD_map_intLe hstamp)

/-- The reif slot's pin and both operand domains from one watch-stamp equality
    over `[i, j, r]`. -/
theorem watchStamp_getD_reif {f g : BranchFrame} {i j r : Nat}
    (h : watchStamp f [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0] =
         watchStamp g [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0]) :
    (frameState f).domains.getD i Dom.empty = (frameState g).domains.getD i Dom.empty ∧
    (frameState f).domains.getD j Dom.empty = (frameState g).domains.getD j Dom.empty ∧
    (frameState f).domains.getD r Dom.empty = (frameState g).domains.getD r Dom.empty :=
  ⟨watchStamp_getD h (.intLe i 0) (by simp),
   watchStamp_getD h (.intLe j 0) (by simp),
   watchStamp_getD h (.intLe r 0) (by simp)⟩

/-- `propEqReifSlot` watches exactly its two operands and the reif slot. -/
theorem propEqReifSlot_propLocal (i j r : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe r 0],
                   run := fun st => propEqReifSlot st i j r } := by
  intro f g hstamp
  obtain ⟨hi, hj, hr⟩ := watchStamp_getD_reif hstamp
  exact propEqReifSlot_local hi hj hr

/-- `propNeReifSlot` watches exactly its two operands and the reif slot. -/
theorem propNeReifSlot_propLocal (i j r : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe r 0],
                   run := fun st => propNeReifSlot st i j r } := by
  intro f g hstamp
  obtain ⟨hi, hj, hr⟩ := watchStamp_getD_reif hstamp
  exact propNeReifSlot_local hi hj hr

/-- The strengthened `leReifSlot` run watches exactly its two operands and the
    reif slot (including its unpinned bounds arm). -/
theorem propLeReifSlotB_propLocal (i j r : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe j 0, .intLe r 0],
                   run := fun st => propLeReifSlotB st i j r } := by
  intro f g hstamp
  obtain ⟨hi, hj, hr⟩ := watchStamp_getD_reif hstamp
  exact propLeReifSlotB_local hi hj hr

/-- The reif slot and the constraint slots from one watch-stamp equality over
    `r :: is.map (fun i => Atom.intLe i 0)`. -/
theorem watchStamp_getD_reif_lin {f g : BranchFrame} {is : List Nat} {r : Nat}
    (h : watchStamp f (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0)) =
         watchStamp g (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0))) :
    (frameState f).domains.getD r Dom.empty = (frameState g).domains.getD r Dom.empty ∧
    ∀ i ∈ is, (frameState f).domains.getD i Dom.empty = (frameState g).domains.getD i Dom.empty :=
  ⟨watchStamp_getD h (.intLe r 0) (by simp),
   watchStamp_getD_forall h (fun _ hi => List.mem_cons_of_mem _ (mem_map_intLe hi))⟩

/-- `propLinEqReif` watches the reif slot and the constraint slots. -/
theorem propLinEqReif_propLocal (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) :
    PropLocalOne { watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinEqReif st coeffs is b r } := by
  intro f g hstamp
  obtain ⟨hr, his⟩ := watchStamp_getD_reif_lin hstamp
  exact propLinEqReif_local hr his

/-- `propLinNeReif` watches the reif slot and the constraint slots. -/
theorem propLinNeReif_propLocal (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) :
    PropLocalOne { watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinNeReif st coeffs is b r } := by
  intro f g hstamp
  obtain ⟨hr, his⟩ := watchStamp_getD_reif_lin hstamp
  exact propLinNeReif_local hr his

/-- `propLinLeReif` watches the reif slot and the constraint slots. -/
theorem propLinLeReif_propLocal (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) :
    PropLocalOne { watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
                   run := fun st => propLinLeReif st coeffs is b r } := by
  intro f g hstamp
  obtain ⟨hr, his⟩ := watchStamp_getD_reif_lin hstamp
  exact propLinLeReif_local hr his

/-- `propBool2intSlot` watches exactly its source and target slots. -/
theorem propBool2intSlot_propLocal (i k : Nat) :
    PropLocalOne { watches := [.intLe i 0, .intLe k 0],
                   run := fun st => propBool2intSlot st i k } := by
  intro f g hstamp
  exact propBool2intSlot_local
    (by exact watchStamp_getD hstamp (.intLe i 0) (by simp))
    (by exact watchStamp_getD hstamp (.intLe k 0) (by simp))

/-! ## The concrete registration -/

/-- Every registered propagator with a nonempty declared footprint is
    locally sound — including the linear families `linLe`/`linEq`/`linNe`,
    whose runs read exactly their constraint's slots, the reified binary
    families and `linEqReif`/`linNeReif`, and the `bool2int` channel;
    footprint-less registrations (and unregistered families) are excluded
    (they are never scheduled). -/
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
      by_cases ha : a = []
      · subst a
        exact absurd rfl hne
      · intro f g hstamp
        exact propAllDiffLCG_domains_local a
          (watchStamp_getD_map_intLe hstamp)
  | timesSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propTimes_propLocal a b c
  | minSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propMin_propLocal _ _ _
  | maxSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propMax_propLocal _ _ _
  | absSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propAbs_propLocal a b
  | linEq coeffs is b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinEq2_propLocal coeffs is b
  | linLe coeffs is b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinLe2_propLocal coeffs is b
  | linNe coeffs is b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinNe_propLocal coeffs is b
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
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propArrayBoolAnd_propLocal _ _
  | bool2intSlot a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propBool2intSlot_propLocal _ _
  | boolEqSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | arrayIntElementSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propArrayIntElement_propLocal a b c
  | arrayVarIntElementSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propArrayVarIntElement_propLocal a b c
  | arrayVarBoolElementSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propArrayVarBoolElement_propLocal a b c
  | eqReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propEqReifSlot_propLocal _ _ _
  | leReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLeReifSlotB_propLocal _ _ _
  | neReifSlot a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propNeReifSlot_propLocal _ _ _
  | linEqReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinEqReif_propLocal _ _ _ _
  | linLeReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinLeReif_propLocal _ _ _ _
  | linNeReif a b c d =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propLinNeReif_propLocal _ _ _ _
  | maxGen a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propMaxGen_propLocal a b
  | minGen a b =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propMinGen_propLocal a b
  | divGen a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propDiv_propLocal a b c
  | modGen a b c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact propMod_propLocal a b c
  | minPair a b c =>
      cases a <;> cases b <;> cases c <;>
        (simp only [propagatorOfProved, Option.some.injEq] at hp
         subst hp
         first
         | exact propMin_propLocal _ _ _
         | exact propCheck_propLocal _)
  | maxPair a b c =>
      cases a <;> cases b <;> cases c <;>
        (simp only [propagatorOfProved, Option.some.injEq] at hp
         subst hp
         first
         | exact propMax_propLocal _ _ _
         | exact propCheck_propLocal _)
  | setInSlot a b =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)
  | setInReifSlot a b c =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by simp)

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

/-
File: LeanFzn/Solver/Propagation/Proofs/Engine.lean

Purpose:
  Reachability obligations for the LCG propagation engine (PLAN.md
  Step 2, sub-steps 2.1–2.2): the integer-view bound lemmas behind
  `domMinI`/`domMaxI`, the trail↔domain bound correspondence
  (`trail-domain coherence`), and the per-propagator nogood validity
  schema that later files thread through `runPropagators`.

Dependencies:
  - LeanFzn.Solver.Reference.Engine: `propagateLoop`, `runPropagators`,
    `enqueueNorm`, `domOfLit`, `rootFacts`, `initialStateWithRoots`.
  - LeanFzn.Solver.Propagation.Encoding: order-encoding evaluation lemmas
    (`eval_posLe_iff`, `eval_negLe_iff`).
  - LeanFzn.Solver.Propagation.Invariants: `State.TrailSatisfied`, `Clause.EntailedBy`,
    `ProblemSolution`.

DAG:
  LeanFzn.Solver.UIP.Engine + LeanFzn.Solver.UIP.Encoding + LeanFzn.Solver.UIP.Invariants -> Proofs/Engine
  -> Proofs/EngineSound (propagateLoop preservation, future)
  -> Proofs/Search (EngineSafe elimination, future)
-/

import LeanFzn.Solver.Propagation.EngineCore
import LeanFzn.Solver.Propagation.Encoding
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering

/-! ## Locally-defined min/max lemmas

`minI`/`maxI` are local helpers (no Mathlib in the TCB); their
order laws are proved once here. -/

/-- `minI` is below both arguments. -/
theorem minI_le_left (a b : Int) : minI a b ≤ a := by
  unfold minI
  by_cases h : a ≤ b
  · rw [if_pos h]; exact Int.le_refl _
  · rw [if_neg h]; omega

/-- `minI` is below (or at) the second argument. -/
theorem minI_le_right (a b : Int) : minI a b ≤ b := by
  unfold minI
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Int.le_refl _

/-- `maxI` is above (or at) the first argument. -/
theorem maxI_ge_left (a b : Int) : a ≤ maxI a b := by
  unfold maxI
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Int.le_refl _

/-- `maxI` is above the second argument. -/
theorem maxI_ge_right (a b : Int) : b ≤ maxI a b := by
  unfold maxI
  by_cases h : a ≤ b
  · rw [if_pos h]; exact Int.le_refl _
  · rw [if_neg h]; omega

/-! ## Fold bound lemmas -/

/-- Generic fold-min: the folded minimum is `≤` every scanned
    element. -/
theorem foldmin_le_mem : ∀ (ls : List Int) (acc : Option Int) (m : Int),
    (ls.foldl (fun a x => match a with
      | none => some x
      | some c => some (minI c x)) acc) = some m →
    (∀ i ∈ ls, m ≤ i) ∧ (∀ c, acc = some c → m ≤ c) := by
  intro ls
  induction ls with
  | nil =>
      intro acc m h
      cases acc with
      | none =>
          simp only [List.foldl_nil] at h
          exact absurd h (by simp)
      | some c =>
          simp only [List.foldl_nil, Option.some.injEq] at h
          subst h
          refine ⟨by simp, ?_⟩
          intro c' hc
          have : c = c' := by
            rw [Option.some.injEq] at hc; exact hc
          omega
  | cons x rest ih =>
      intro acc m h
      simp only [List.foldl_cons] at h
      cases acc with
      | none =>
          obtain ⟨h1, h2⟩ := ih (some x) m h
          refine ⟨?_, ?_⟩
          · intro i hi
            rcases List.mem_cons.mp hi with heq | hi
            · rw [heq]; exact h2 x rfl
            · exact h1 i hi
          · intro c hc
            exact absurd hc (by simp)
      | some c =>
          obtain ⟨h1, h2⟩ := ih (some (minI c x)) m h
          refine ⟨?_, ?_⟩
          · intro i hi
            rcases List.mem_cons.mp hi with heq | hi
            · rw [heq]
              exact Int.le_trans (h2 (minI c x) rfl) (minI_le_right c x)
            · exact h1 i hi
          · intro c' hc'
            have hcc : c = c' := by
              rw [Option.some.injEq] at hc'; exact hc'
            rw [← hcc]
            exact Int.le_trans (h2 (minI c x) rfl) (minI_le_left c x)

/-- Generic fold-max: the folded maximum is `≥` every scanned
    element. -/
theorem foldmax_ge_mem : ∀ (ls : List Int) (acc : Option Int) (M : Int),
    (ls.foldl (fun a x => match a with
      | none => some x
      | some c => some (maxI c x)) acc) = some M →
    (∀ i ∈ ls, i ≤ M) ∧ (∀ c, acc = some c → c ≤ M) := by
  intro ls
  induction ls with
  | nil =>
      intro acc M h
      cases acc with
      | none =>
          simp only [List.foldl_nil] at h
          exact absurd h (by simp)
      | some c =>
          simp only [List.foldl_nil, Option.some.injEq] at h
          subst h
          refine ⟨by simp, ?_⟩
          intro c' hc
          have : c = c' := by
            rw [Option.some.injEq] at hc; exact hc
          omega
  | cons x rest ih =>
      intro acc M h
      simp only [List.foldl_cons] at h
      cases acc with
      | none =>
          obtain ⟨h1, h2⟩ := ih (some x) M h
          refine ⟨?_, ?_⟩
          · intro i hi
            rcases List.mem_cons.mp hi with heq | hi
            · rw [heq]; exact h2 x rfl
            · exact h1 i hi
          · intro c hc
            exact absurd hc (by simp)
      | some c =>
          obtain ⟨h1, h2⟩ := ih (some (maxI c x)) M h
          refine ⟨?_, ?_⟩
          · intro i hi
            rcases List.mem_cons.mp hi with heq | hi
            · rw [heq]
              exact Int.le_trans (maxI_ge_right c x) (h2 (maxI c x) rfl)
            · exact h1 i hi
          · intro c' hc'
            have hcc : c = c' := by
              rw [Option.some.injEq] at hc'; exact hc'
            rw [← hcc]
            exact Int.le_trans (maxI_ge_left c x) (h2 (maxI c x) rfl)

/-! ## Domain extrema are bounds

`domMinI`/`domMaxI` fold the integer view of a domain; the fold
lemmas make them bounds of every integer value in the domain. -/

/-- `domMinI d = some mn` makes `mn` a lower bound of every integer
    view in `d`. -/
theorem domMinI_le {α : Type} [DomainLike α] {d : α} {mn : Int} (v : Value) (i : Int)
    (hv : Value.intView v = some i) (hmem : v ∈ d)
    (hmin : domMinI d = some mn) : mn ≤ i := by
  have hmemi : i ∈ (DomainElems.elems d).filterMap Value.intView :=
    List.mem_filterMap.mpr ⟨v, (DomainLike.mem_iff d v).mp hmem, hv⟩
  unfold domMinI at hmin
  exact (foldmin_le_mem ((DomainElems.elems d).filterMap Value.intView) none mn hmin).1 i hmemi

/-- `domMaxI d = some mx` makes `mx` an upper bound of every integer
    view in `d`. -/
theorem domMaxI_ge {α : Type} [DomainLike α] {d : α} {mx : Int} (v : Value) (i : Int)
    (hv : Value.intView v = some i) (hmem : v ∈ d)
    (hmax : domMaxI d = some mx) : i ≤ mx := by
  have hmemi : i ∈ (DomainElems.elems d).filterMap Value.intView :=
    List.mem_filterMap.mpr ⟨v, (DomainLike.mem_iff d v).mp hmem, hv⟩
  unfold domMaxI at hmax
  exact (foldmax_ge_mem ((DomainElems.elems d).filterMap Value.intView) none mx hmax).1 i hmemi

/-! ## Trail bounds correspond to satisfied entries

A positive order entry `s ≤ k` on the trail makes `k` an upper bound
of the slot's value in every satisfying assignment; a negative order
entry `¬(s ≤ k)` makes `k+1` a lower bound. The trail folds
`trailHiOf`/`trailLoOf` collect exactly those bounds. -/

/-- A satisfied positive order literal bounds the slot's integer
    view above. -/
theorem sat_posLe_bounds {a : Assignment} {s : Nat} {k : Int}
    (h : (posLe s k).eval a = some true) {i : Int}
    (hslot : slotInt a s = some i) : i ≤ k := by
  rw [eval_posLe_iff] at h
  obtain ⟨i', hi', hik⟩ := h
  rw [hslot] at hi'
  rw [Option.some.injEq] at hi'
  subst hi'
  exact hik

/-- A satisfied negative order literal bounds the slot's integer
    view below. -/
theorem sat_negLe_bounds {a : Assignment} {s : Nat} {k : Int}
    (h : (negLe s k).eval a = some true) {i : Int}
    (hslot : slotInt a s = some i) : k + 1 ≤ i := by
  rw [eval_negLe_iff] at h
  obtain ⟨i', hi', hik⟩ := h
  rw [hslot] at hi'
  rw [Option.some.injEq] at hi'
  subst hi'
  omega


/-! ## Domain-slot plumbing

`updateSlot`/`setSlot` are structural updates; membership at the
updated vs. untouched slots is characterized once here, together with
the out-of-range `getD` degeneracy. -/

/-- Membership in the updated slot at the SAME index is membership in
    the image of the old slot. -/
theorem mem_getD_updateSlot_eq : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain) (v : Value),
    v ∈ (updateSlot doms s f).getD s Dom.empty → v ∈ f (doms.getD s Dom.empty) := by
  intro doms s f v hmem
  by_cases hk : s < doms.length
  · rw [updateSlot, List.getD_eq_getElem?_getD, List.getElem?_set_self hk,
      Option.getD_some] at hmem
    exact hmem
  · exfalso
    rw [updateSlot, List.getD_eq_getElem?_getD, List.getElem?_set] at hmem
    simp only [if_true, if_neg hk] at hmem
    simpa using hmem

/-- Membership at a DIFFERENT index is unchanged. -/
theorem mem_getD_updateSlot_ne : ∀ (doms : List Domain)
    (s s0 : Nat) (f : Domain → Domain) (v : Value),
    s0 ≠ s → v ∈ (updateSlot doms s f).getD s0 Dom.empty →
    v ∈ doms.getD s0 Dom.empty := by
  intro doms s s0 f v hne hmem
  rw [updateSlot, List.getD_eq_getElem?_getD] at hmem
  rw [List.getElem?_set] at hmem
  split at hmem
  · rename_i heq
    exact absurd heq.symm hne
  · rw [List.getD_eq_getElem?_getD]
    exact hmem

/-- Out-of-range `getD` yields the default (empty). -/
theorem getD_nil_of_ge : ∀ (doms : List Domain) (s : Nat),
    doms.length ≤ s → doms.getD s Dom.empty = Dom.empty := by
  intro doms
  induction doms with
  | nil => intro s _; rfl
  | cons d ds ih =>
      intro s hs
      cases s with
      | zero =>
          have : (d :: ds).length = ds.length + 1 := rfl
          omega
      | succ s' =>
          simp only [List.getD_cons_succ]
          refine ih s' ?_
          have : (d :: ds).length = ds.length + 1 := rfl
          omega

/-- The integer filter only removes values. -/
theorem mem_domFilterInt {keep : Int → Bool} {d : Domain} {v : Value}
    (h : v ∈ domFilterInt keep d) : v ∈ d := by
  unfold domFilterInt at h
  dsimp only at h
  split at h
  · exact h
  · rw [mem_ofList_iff, List.mem_filter] at h
    rw [DomainLike.mem_iff, domElems_eq_enum]
    exact h.1

/-- A value of the domain passing the keep test survives the integer
    filter. -/
theorem mem_domFilterInt_of_mem_of_keep {keep : Int → Bool} {d : Domain} {v : Value}
    (hv : v ∈ d) (hk : domFilterIntKeep keep v = true) :
    v ∈ domFilterInt keep d := by
  unfold domFilterInt
  dsimp only
  split
  · exact hv
  · rename_i hne
    rw [mem_ofList_iff, List.mem_filter]
    refine ⟨?_, hk⟩
    rw [← domElems_eq_enum, ← DomainLike.mem_iff]
    exact hv

/-- Every value surviving the integer filter passes the keep test. -/
theorem domFilterInt_keep {keep : Int → Bool} {d : Domain} {v : Value}
    (h : v ∈ domFilterInt keep d) : domFilterIntKeep keep v = true := by
  unfold domFilterInt at h
  dsimp only at h
  split at h
  · rename_i hlen
    have hfil : (Dom.enum d).filter (domFilterIntKeep keep) = Dom.enum d :=
      List.Sublist.eq_of_length List.filter_sublist hlen
    exact List.filter_eq_self.mp hfil v (by
      rw [← domElems_eq_enum, ← DomainLike.mem_iff]
      exact h)
  · rw [mem_ofList_iff, List.mem_filter] at h
    exact h.2

/-- Values of a slot untouched by `domOfLit` are unchanged. -/
theorem domOfLit_getD_ne : ∀ (doms : List Domain) (l : Literal)
    (s0 : Nat) (v : Value), s0 ≠ l.atom.slot →
    v ∈ (domOfLit doms l).getD s0 Dom.empty → v ∈ doms.getD s0 Dom.empty := by
  intro doms l s0 v hne hmem
  cases l with
  | mk atom positive =>
      cases atom with
      | intLe s' k =>
          cases positive <;>
            exact mem_getD_updateSlot_ne doms s' s0 _ v hne hmem
      | boolEq s' b =>
          simp only [domOfLit] at hmem
          cases positive <;>
            exact mem_getD_updateSlot_ne doms s' s0 _ v hne hmem
      | intNe s' k =>
          cases positive <;>
            exact mem_getD_updateSlot_ne doms s' s0 _ v hne hmem

/-- `updateSlot` preserves the slot count. -/
theorem updateSlot_length : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain),
    (updateSlot doms s f).length = doms.length := by
  intro doms s f
  exact List.length_set

/-- `domOfLit` preserves the slot count. -/
theorem domOfLit_length {doms : List Domain} (l : Literal) :
    (domOfLit doms l).length = doms.length := by
  cases l with
  | mk atom positive =>
      cases atom with
      | intLe s k =>
          unfold domOfLit
          cases positive <;>
            show (updateSlot doms s _).length = doms.length <;>
            exact updateSlot_length doms s _
      | boolEq s b =>
          unfold domOfLit
          cases positive <;>
            show (updateSlot doms s _).length = doms.length <;>
            exact updateSlot_length doms s _
      | intNe s k =>
          unfold domOfLit
          cases positive <;>
            show (updateSlot doms s _).length = doms.length <;>
            exact updateSlot_length doms s _

/-- Values in the trail-folded domains are original values or Boolean
    pins introduced by Boolean literals. -/
theorem fits_fold_original : ∀ (trail : List TrailEntry)
    (doms : List Domain) (s0 : Nat) (v : Value),
    v ∈ (trail.foldl (fun acc e => domOfLit acc e.literal) doms).getD s0 Dom.empty →
    (∃ b : Bool, v = .bool b) ∨ v ∈ doms.getD s0 Dom.empty := by
  intro trail
  induction trail with
  | nil =>
      intro doms s0 v hmem
      exact Or.inr hmem
  | cons e rest ih =>
      intro doms s0 v hmem
      rw [List.foldl_cons] at hmem
      have hstep := ih (domOfLit doms e.literal) s0 v hmem
      rcases hstep with ⟨b, hb⟩ | horig
      · exact Or.inl ⟨b, hb⟩
      · by_cases heq : s0 = e.literal.atom.slot
        · cases hlit : e.literal with
          | mk atom positive =>
              rw [heq, hlit] at horig ⊢
              cases atom with
              | intLe s' k =>
                  cases positive
                  · -- negative: keep p > k
                    have hstep2 : v ∈ (updateSlot doms s'
                        (fun d => domFilterInt
                          (fun p => decide (p > k)) d)).getD s' Dom.empty := horig
                    have himg := mem_getD_updateSlot_eq doms s'
                      (fun d => domFilterInt (fun p => decide (p > k)) d) v
                      hstep2
                    exact Or.inr (mem_domFilterInt himg)
                  · -- positive: keep p ≤ k
                    have hstep2 : v ∈ (updateSlot doms s'
                        (fun d => domFilterInt
                          (fun p => decide (p ≤ k)) d)).getD s' Dom.empty := horig
                    have himg := mem_getD_updateSlot_eq doms s'
                      (fun d => domFilterInt (fun p => decide (p ≤ k)) d) v
                      hstep2
                    exact Or.inr (mem_domFilterInt himg)
              | boolEq s' b =>
                  have himg := mem_getD_updateSlot_eq doms s'
                    (fun d => d.filter (fun v => v.eqB
                      (.bool (if positive then b else !b)))) v horig
                  rw [DomainLike.mem_iff, domElems_eq_enum, Dom.enum_filter] at himg
                  refine Or.inr ?_
                  show v ∈ doms.getD s' Dom.empty
                  rw [DomainLike.mem_iff, domElems_eq_enum]
                  exact (List.mem_filter.mp himg).1
              | intNe s' k =>
                  cases positive
                  · -- negative: keep p = k
                    have hstep2 : v ∈ (updateSlot doms s'
                        (fun d => domFilterInt
                          (fun p => decide (p = k)) d)).getD s' Dom.empty := horig
                    have himg := mem_getD_updateSlot_eq doms s'
                      (fun d => domFilterInt (fun p => decide (p = k)) d) v
                      hstep2
                    exact Or.inr (mem_domFilterInt himg)
                  · -- positive: keep p ≠ k
                    have hstep2 : v ∈ (updateSlot doms s'
                        (fun d => domFilterInt
                          (fun p => decide (p ≠ k)) d)).getD s' Dom.empty := horig
                    have himg := mem_getD_updateSlot_eq doms s'
                      (fun d => domFilterInt (fun p => decide (p ≠ k)) d) v
                      hstep2
                    exact Or.inr (mem_domFilterInt himg)
        · exact Or.inr (domOfLit_getD_ne doms e.literal s0 v
            (fun h => heq h) horig)

/-- `domOfLit` only ever removes values. -/
theorem domOfLit_domSub (doms : List Domain) (l : Literal) :
    DomSub (domOfLit doms l) doms := by
  refine ⟨domOfLit_length l, ?_⟩
  intro s0 v hv
  by_cases heq : s0 = l.atom.slot
  · cases l with
    | mk atom positive =>
        cases atom with
        | intLe s' k =>
            cases positive
            all_goals
              first
              | (have himg := mem_getD_updateSlot_eq doms s' _ v
                   (by rw [show s0 = s' from heq] at hv; exact hv)
                 rw [show s0 = s' from heq]
                 exact mem_domFilterInt himg)
        | boolEq s' b =>
            have hv' : v ∈ (updateSlot doms s'
                (fun d => d.filter (fun v => v.eqB
                  (.bool (if positive then b else !b))))).getD s' Dom.empty := by
              rw [show s0 = s' from heq] at hv; exact hv
            have himg := mem_getD_updateSlot_eq doms s' _ v hv'
            rw [show s0 = s' from heq]
            rw [DomainLike.mem_iff, domElems_eq_enum, Dom.enum_filter] at himg
            rw [DomainLike.mem_iff, domElems_eq_enum]
            exact (List.mem_filter.mp himg).1
        | intNe s' k =>
            cases positive
            all_goals
              first
              | (have himg := mem_getD_updateSlot_eq doms s' _ v
                   (by rw [show s0 = s' from heq] at hv; exact hv)
                 rw [show s0 = s' from heq]
                 exact mem_domFilterInt himg)
  · exact domOfLit_getD_ne doms l s0 v heq hv

/-- A fold of `domOfLit` over any trail only removes values. -/
theorem foldl_domOfLit_domSub : ∀ (trail : List TrailEntry)
    (doms : List Domain),
    DomSub (trail.foldl (fun acc e => domOfLit acc e.literal) doms) doms := by
  intro trail
  induction trail with
  | nil => intro doms; exact DomSub.refl doms
  | cons e rest ih =>
      intro doms
      rw [List.foldl_cons]
      exact (ih (domOfLit doms e.literal)).trans (domOfLit_domSub doms e.literal)

/-- `enqueueNorm` only ever removes values. -/
theorem enqueueNorm_domSub (st : State) (l : Literal) (r : Option Reason) :
    DomSub (enqueueNorm st l r).domains st.domains := by
  unfold enqueueNorm
  dsimp only
  split
  · exact DomSub.refl _
  · split
    · exact DomSub.refl _
    · exact domOfLit_domSub _ _

/-- The propagator sweep only ever removes values. -/
theorem runPropagators_go_domSub : ∀ (props : List Propagator) (s : State),
    DomSub (runPropagators.go props s).domains s.domains := by
  intro props
  induction props with
  | nil => intro s; exact DomSub.refl _
  | cons p rest ih =>
      intro s
      simp only [runPropagators.go]
      split
      · exact DomSub.refl _
      · split
        · exact ih s
        · exact DomSub.refl _
        · rename_i l r _
          exact (ih (enqueueNorm s l (some r))).trans (enqueueNorm_domSub s l (some r))

theorem runPropagators_domSub (props : List Propagator) (s : State) :
    DomSub (runPropagators props s).domains s.domains :=
  runPropagators_go_domSub props s

/-- Slot-value extraction: an int-viewed slot of a fitting assignment
    carries the viewed value at an in-range slot. -/
theorem slotInt_mem {doms : List Domain} {a : Assignment}
    (hfit : a.Fits doms) {s : Nat} {i : Int}
    (hslot : slotInt a s = some i) :
    ∃ v, a[s]? = some v ∧ Value.intView v = some i ∧ s < doms.length := by
  obtain ⟨hlen, hmem⟩ := hfit
  rw [slotInt] at hslot
  simp only [Option.bind_eq_some_iff] at hslot
  obtain ⟨v, hv, hvi⟩ := hslot
  refine ⟨v, hv, hvi, ?_⟩
  cases hlt : Nat.lt_or_ge s doms.length with
  | inl h => exact h
  | inr hge =>
      exfalso
      have hnil : doms.getD s Dom.empty = Dom.empty := getD_nil_of_ge doms s hge
      have hvnil : v ∈ doms.getD s Dom.empty := hmem s v hv
      rw [hnil] at hvnil
      exact absurd hvnil (by simp)

/-! ## The single-step coherence theorem -/

/-! ### The single-step coherence theorem

An assignment fitting a `domOfLit`-narrowed domain satisfies the
narrowing literal. Two restrictions make this exact:

* the slot must be within the assignment (the `Fits` length law makes
  this the common case — the engine's slots are always in range);
* the slot's value must have an integer view (the fragment invariant:
  the order encoding only speaks about int/bool slots; `domFilterInt`
  passes set/array values through, for which order literals evaluate
  to `none`). -/

/-- THE SINGLE-STEP COHERENCE (positive order): an assignment fitting
    the narrowed domain satisfies the positive order literal. -/
theorem fits_domOfLit_sat_pos {doms : List Domain} {s : Nat}
    {k : Int} {a : Assignment} {i : Int}
    (hfit : a.Fits (domOfLit doms (posLe s k)))
    (hin : s < a.length)
    (hslot : slotInt a s = some i) :
    (posLe s k).eval a = some true := by
  have hget : a[s]? = some a[s] :=
    (List.getElem?_eq_some_iff).mpr ⟨hin, rfl⟩
  obtain ⟨_, hmem⟩ := hfit
  have hslotmem : a[s] ∈ (domOfLit doms (posLe s k)).getD s Dom.empty :=
    hmem s a[s] hget
  have himg : a[s] ∈ domFilterInt (fun p => decide (p ≤ k))
      (doms.getD s Dom.empty) := by
    have hstep : a[s] ∈ (updateSlot doms s
        (fun d => domFilterInt (fun p => decide (p ≤ k)) d)).getD s Dom.empty :=
      hslotmem
    exact mem_getD_updateSlot_eq doms s _ a[s] hstep
  have hkeep := domFilterInt_keep himg
  -- the int-view premise pins the value shape:
  cases hva : a[s] with
  | int p =>
      rw [hva] at hkeep
      simp only [domFilterIntKeep] at hkeep
      -- hkeep : decide (p ≤ k) = true
      have hpk : p ≤ k := of_decide_eq_true hkeep
      -- slotInt some p
      show (posLe s k).eval a = some true
      rw [eval_posLe_iff]
      refine ⟨p, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some p
      rw [hget, hva]
      rfl
  | bool b =>
      rw [hva] at hkeep
      have hpk : (if b then 1 else 0) ≤ k := of_decide_eq_true hkeep
      show (posLe s k).eval a = some true
      rw [eval_posLe_iff]
      refine ⟨if b then 1 else 0, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some (if b then 1 else 0)
      rw [hget, hva]
      rfl
  | setOfInt x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])
  | array x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])


/-- THE SINGLE-STEP COHERENCE (negative order): an assignment fitting
    the narrowed domain satisfies the negative order literal. -/
theorem fits_domOfLit_sat_neg {doms : List Domain} {s : Nat}
    {k : Int} {a : Assignment} {i : Int}
    (hfit : a.Fits (domOfLit doms (negLe s k)))
    (hin : s < a.length)
    (hslot : slotInt a s = some i) :
    (negLe s k).eval a = some true := by
  have hget : a[s]? = some a[s] :=
    (List.getElem?_eq_some_iff).mpr ⟨hin, rfl⟩
  obtain ⟨_, hmem⟩ := hfit
  have hslotmem : a[s] ∈ (domOfLit doms (negLe s k)).getD s Dom.empty :=
    hmem s a[s] hget
  have himg : a[s] ∈ domFilterInt (fun p => decide (p > k))
      (doms.getD s Dom.empty) := by
    have hstep : a[s] ∈ (updateSlot doms s
        (fun d => domFilterInt (fun p => decide (p > k)) d)).getD s Dom.empty :=
      hslotmem
    exact mem_getD_updateSlot_eq doms s _ a[s] hstep
  have hkeep : domFilterIntKeep (fun p => decide (p > k)) a[s] = true :=
    domFilterInt_keep himg
  cases hva : a[s] with
  | int p =>
      rw [hva] at hkeep
      simp only [domFilterIntKeep] at hkeep
      have hpk : p > k := of_decide_eq_true hkeep
      show (negLe s k).eval a = some true
      rw [eval_negLe_iff]
      refine ⟨p, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some p
      rw [hget, hva]
      rfl
  | bool b =>
      rw [hva] at hkeep
      have hpk : (if b then 1 else 0) > k := of_decide_eq_true hkeep
      show (negLe s k).eval a = some true
      rw [eval_negLe_iff]
      refine ⟨if b then 1 else 0, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some (if b then 1 else 0)
      rw [hget, hva]
      rfl
  | setOfInt x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])
  | array x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])

theorem eqB_bool_true {v : Value} {b : Bool} (h : v.eqB (.bool b) = true) :
    v = .bool b := by
  cases v <;> simp_all [Value.eqB]

/-- THE SINGLE-STEP COHERENCE (Boolean pin): an assignment fitting
    the Boolean-pinned domain satisfies the Boolean literal. -/
theorem fits_domOfLit_sat_bool {doms : List Domain} {s : Nat}
    {b : Bool} {a : Assignment}
    (hfit : a.Fits (domOfLit doms (posBool s b)))
    (hin : s < a.length) :
    (posBool s b).eval a = some true := by
  have hget : a[s]? = some a[s] :=
    (List.getElem?_eq_some_iff).mpr ⟨hin, rfl⟩
  obtain ⟨_, hmem⟩ := hfit
  have hslotmem : a[s] ∈ (domOfLit doms (posBool s b)).getD s Dom.empty :=
    hmem s a[s] hget
  have himg : a[s] ∈ (doms.getD s Dom.empty).filter
      (fun v => v.eqB (.bool b)) := by
    have hstep : a[s] ∈ (updateSlot doms s
        (fun d => d.filter (fun v => v.eqB (.bool b)))).getD s Dom.empty := hslotmem
    exact mem_getD_updateSlot_eq doms s _ a[s] hstep
  have hf : a[s].eqB (.bool b) = true := by
    have hmem' : a[s] ∈ Dom.enum ((doms.getD s Dom.empty).filter
        (fun v => v.eqB (.bool b))) := by
      rw [← domElems_eq_enum, ← DomainLike.mem_iff]
      exact himg
    rw [Dom.enum_filter, List.mem_filter] at hmem'
    exact hmem'.2
  have hval : a[s] = Value.bool b := eqB_bool_true hf
  show (posBool s b).eval a = some true
  simp only [posBool, Literal.eval, Atom.eval]
  rw [hget, hval]
  cases b <;> rfl


/-- THE SINGLE-STEP COHERENCE (positive value removal): an assignment
    fitting the value-removal-narrowed domain satisfies the positive
    value-removal literal. -/
theorem fits_domOfLit_sat_posNe {doms : List Domain} {s : Nat}
    {k : Int} {a : Assignment} {i : Int}
    (hfit : a.Fits (domOfLit doms (posNe s k)))
    (hin : s < a.length)
    (hslot : slotInt a s = some i) :
    (posNe s k).eval a = some true := by
  have hget : a[s]? = some a[s] :=
    (List.getElem?_eq_some_iff).mpr ⟨hin, rfl⟩
  obtain ⟨_, hmem⟩ := hfit
  have hslotmem : a[s] ∈ (domOfLit doms (posNe s k)).getD s Dom.empty :=
    hmem s a[s] hget
  have himg : a[s] ∈ domFilterInt (fun p => decide (p ≠ k))
      (doms.getD s Dom.empty) := by
    have hstep : a[s] ∈ (updateSlot doms s
        (fun d => domFilterInt (fun p => decide (p ≠ k)) d)).getD s Dom.empty :=
      hslotmem
    exact mem_getD_updateSlot_eq doms s _ a[s] hstep
  have hkeep : domFilterIntKeep (fun p => decide (p ≠ k)) a[s] = true :=
    domFilterInt_keep himg
  cases hva : a[s] with
  | int p =>
      rw [hva] at hkeep
      simp only [domFilterIntKeep] at hkeep
      have hpk : p ≠ k := of_decide_eq_true hkeep
      show (posNe s k).eval a = some true
      rw [eval_posNe_iff]
      refine ⟨p, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some p
      rw [hget, hva]
      rfl
  | bool b =>
      rw [hva] at hkeep
      have hpk : (if b then 1 else 0) ≠ k := of_decide_eq_true hkeep
      show (posNe s k).eval a = some true
      rw [eval_posNe_iff]
      refine ⟨if b then 1 else 0, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some (if b then 1 else 0)
      rw [hget, hva]
      rfl
  | setOfInt x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])
  | array x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])

/-- THE SINGLE-STEP COHERENCE (negative value removal): an assignment
    fitting the value-pinned domain satisfies the negative
    value-removal literal. -/
theorem fits_domOfLit_sat_negNe {doms : List Domain} {s : Nat}
    {k : Int} {a : Assignment} {i : Int}
    (hfit : a.Fits (domOfLit doms (negNe s k)))
    (hin : s < a.length)
    (hslot : slotInt a s = some i) :
    (negNe s k).eval a = some true := by
  have hget : a[s]? = some a[s] :=
    (List.getElem?_eq_some_iff).mpr ⟨hin, rfl⟩
  obtain ⟨_, hmem⟩ := hfit
  have hslotmem : a[s] ∈ (domOfLit doms (negNe s k)).getD s Dom.empty :=
    hmem s a[s] hget
  have himg : a[s] ∈ domFilterInt (fun p => decide (p = k))
      (doms.getD s Dom.empty) := by
    have hstep : a[s] ∈ (updateSlot doms s
        (fun d => domFilterInt (fun p => decide (p = k)) d)).getD s Dom.empty :=
      hslotmem
    exact mem_getD_updateSlot_eq doms s _ a[s] hstep
  have hkeep : domFilterIntKeep (fun p => decide (p = k)) a[s] = true :=
    domFilterInt_keep himg
  cases hva : a[s] with
  | int p =>
      rw [hva] at hkeep
      simp only [domFilterIntKeep] at hkeep
      have hpk : p = k := of_decide_eq_true hkeep
      show (negNe s k).eval a = some true
      rw [eval_negNe_iff]
      refine ⟨p, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some p
      rw [hget, hva]
      rfl
  | bool b =>
      rw [hva] at hkeep
      have hpk : (if b then 1 else 0) = k := of_decide_eq_true hkeep
      show (negNe s k).eval a = some true
      rw [eval_negNe_iff]
      refine ⟨if b then 1 else 0, ?_, hpk⟩
      show (a[s]?.bind Value.intView) = some (if b then 1 else 0)
      rw [hget, hva]
      rfl
  | setOfInt x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])
  | array x =>
      exfalso
      rw [slotInt, hget, hva] at hslot
      exact absurd hslot (by simp [Value.intView])


/-! ## Boolean clause scanning (Step 2.1)

`scanClause` is the reference clause-propagation semantics: a clause
whose literals are all trail-false is a conflict; a clause with exactly
one non-false literal is unit. Both reports are sound against
trail-satisfying assignments. -/
/-! ### Boolean clause scanning (2.1): scanClause correctness -/

/-- If a trail entry matches `l.negate.norm`, then any assignment
    satisfying the trail makes `l` FALSE: the entry's literal is
    (up to norm) the negation of `l`. -/
theorem negOnTrail_falsifies {st : State} {l : Literal}
    (h : st.negOnTrail l = true) {a : Assignment}
    (hsat : st.TrailSatisfied a)
    (hnorm : l = l.norm) :
    l.eval a = some false := by
  -- st.negOnTrail l = trail.any (fun e => litEqB e.literal l.negate.norm)
  unfold State.negOnTrail at h
  rw [List.any_eq_true] at h
  obtain ⟨e, hem, heb⟩ := h
  -- e.literal = l.negate.norm (litEqB → equality)
  have hlit : e.literal = l.negate.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  -- e.literal.eval a = some true (trail satisfaction)
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit] at hev
  -- (l.negate.norm).eval a = some true; with l = l.norm:
  -- (l.norm.negate.norm).eval = some true ⟹ l.eval = some false
  -- via eval_negate + norm_eval + eval_negate:
  have h1 : (l.negate.norm).eval a = some true := hev
  rw [Literal.norm_eval (l.negate) a] at h1
  rw [Literal.eval_negate l a] at h1
  -- h1 : (l.eval a).map (! ·) = some true
  cases h : l.eval a with
  | none => rw [h] at h1; simp at h1
  | some b =>
      rw [h] at h1
      cases b <;> simp at h1
      rfl

/-- If a trail entry matches `l.norm`, then any assignment satisfying
    the trail makes `l` TRUE (l normalized). -/
theorem litOnTrail_satisfies {st : State} {l : Literal}
    (h : st.litOnTrail l = true) {a : Assignment}
    (hsat : st.TrailSatisfied a) :
    l.eval a = some true := by
  unfold State.litOnTrail at h
  rw [List.any_eq_true] at h
  obtain ⟨e, hem, heb⟩ := h
  have hlit : e.literal = l.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit] at hev
  -- (l.norm).eval a = some true; l.eval = (l.norm).eval:
  rw [← Literal.norm_eval l a]
  exact hev

/-- A conflict reported by `scanClause` is falsified by every
    assignment satisfying the trail: every literal of the clause is
    trail-negated (all its non-false literals were filtered out).
    The normalized-lits premise can be dropped: the scan code filters
    with `!st.negOnTrail l`, and `negOnTrail` checks `l.negate.norm`,
    which evaluates exactly like `l.negate` — so the falsification
    transfers to each (possibly non-normalized) `l` through
    `negate_norm_square`. -/

theorem scanClause_conflict_falsified {st : State} {c : Clause}
    (h : scanClause st c = some (.inl c))
    (hsat : st.TrailSatisfied a)
    (hnorms : ∀ l ∈ c, l = l.norm) :
    ∀ l ∈ c, l.eval a = some false := by
  intro l hl
  refine negOnTrail_falsifies ?_ hsat (hnorms l hl)
  unfold scanClause at h
  split at h
  · -- the any-branch fired: contradiction (h : none = some (.inl c))
    exact absurd h (by simp)
  · -- filter result is [] : every literal of c is negOnTrail
    rename_i hany
    have hfil : (c.filter (fun l => !st.negOnTrail l)) = [] := by
      match hh : (c.filter (fun l => !st.negOnTrail l)) with
      | [] => rfl
      | l' :: rest =>
          rw [hh] at h
          -- the match on a cons of unknown length reduces casewise:
          match rest with
          | [] =>
              -- [l'] : the unit case gives .inr, contradicting .inl
              simp only [] at h
              cases h
          | l2 :: rest2 =>
              -- length ≥ 2 : none
              simp only [] at h
              cases h
    -- l ∈ c and the filter is empty ⇒ the keep-condition is false ⇒
    -- negOnTrail l = true. Prove the contrapositive: if negOnTrail l
    -- were false, l would be in the (empty) filter:
    by_cases hneg : st.negOnTrail l = true
    · exact hneg
    · exfalso
      have hbb : st.negOnTrail l = false := by
        cases hbb : st.negOnTrail l with
        | true => exact absurd hbb hneg
        | false => rfl
      have hkeep : (!st.negOnTrail l) = true := by
        rw [hbb]
        rfl
      have hmem2 : l ∈ c.filter (fun l => !st.negOnTrail l) :=
        List.mem_filter.mpr ⟨hl, hkeep⟩
      rw [hfil] at hmem2
      exact absurd hmem2 (by simp)

/-- A unit reported by `scanClause` is justified: the reported literal
    is the UNIQUE filter survivor, so given the clause satisfied at a
    trail-satisfying assignment (its entailment), the survivor is the
    true witness — reported as the unit to enqueue. -/
theorem scanClause_unit_justified {st : State} {c : Clause} {l : Literal}
    {r : Reason} {a : Assignment}
    (h : scanClause st c = some (.inr (l, r)))
    (hsat : st.TrailSatisfied a)
    (hnorms : ∀ l' ∈ c, l' = l'.norm)
    (hsatc : ∃ l2 ∈ c, l2.eval a = some true) :
    l.eval a = some true := by
  unfold scanClause at h
  split at h
  · -- satisfied branch: none = some (.inr ...)
    cases h
  · rename_i hany
    match hh : (c.filter (fun l => !st.negOnTrail l)) with
    | [] =>
        rw [hh] at h
        cases h
    | [l'] =>
        rw [hh] at h
        obtain ⟨hl, hr⟩ : l' = l ∧ { clause := c } = r := by
          simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
          exact h
        -- the reported unit l (= l') is the true witness:
        obtain ⟨l2, hm2, hev2⟩ := hsatc
        -- if l2 ≠ l' then l2 is trail-negated hence false at a:
        by_cases hne : l2 = l'
        · -- l2 = l' = l
          rw [← hl, ← hne]
          exact hev2
        · exfalso
          have hnt : st.negOnTrail l2 = true := by
            by_cases hkeep : (!st.negOnTrail l2) = true
            · have hmem2 : l2 ∈ c.filter (fun l => !st.negOnTrail l) :=
                List.mem_filter.mpr ⟨hm2, hkeep⟩
              rw [hh] at hmem2
              simp only [List.mem_singleton] at hmem2
              exact absurd hmem2 hne
            · cases hbb : st.negOnTrail l2 with
              | true => rfl
              | false =>
                  have : (!st.negOnTrail l2) = true := by rw [hbb]; rfl
                  exact absurd this hkeep
          -- l2 trail-negated and normalized ⟹ false at a:
          have hfalse := negOnTrail_falsifies hnt hsat (hnorms l2 hm2)
          rw [hev2] at hfalse
          exact absurd hfalse (by simp)
    | l1 :: l2 :: rest =>
        rw [hh] at h
        simp only [] at h
        cases h

/-- The norm-free unit-justification lemma (used by the propagation
    lift, where scanned original clauses need not be normalized). The
    trail-negation falsification of a non-witness clause literal goes
    through the entry-level argument directly. -/
theorem scanClause_unit_justified' {st : State} {c : Clause} {l : Literal}
    {r : Reason} {a : Assignment}
    (h : scanClause st c = some (.inr (l, r)))
    (hsat : st.TrailSatisfied a)
    (hsatc : ∃ l2 ∈ c, l2.eval a = some true) :
    l.eval a = some true := by
  unfold scanClause at h
  split at h
  · -- satisfied branch: none = some (.inr ...)
    cases h
  · rename_i hany
    match hh : (c.filter (fun l => !st.negOnTrail l)) with
    | [] =>
        rw [hh] at h
        cases h
    | [l'] =>
        rw [hh] at h
        obtain ⟨hl, hr⟩ : l' = l ∧ { clause := c } = r := by
          simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
          exact h
        -- the reported unit l (= l') is the true witness:
        obtain ⟨l2, hm2, hev2⟩ := hsatc
        -- if l2 ≠ l' then l2 is trail-negated hence false at a:
        by_cases hne : l2 = l'
        · -- l2 = l' = l
          rw [← hl, ← hne]
          exact hev2
        · exfalso
          have hnt : st.negOnTrail l2 = true := by
            by_cases hkeep : (!st.negOnTrail l2) = true
            · have hmem2 : l2 ∈ c.filter (fun l => !st.negOnTrail l) :=
                List.mem_filter.mpr ⟨hm2, hkeep⟩
              rw [hh] at hmem2
              simp only [List.mem_singleton] at hmem2
              exact absurd hmem2 hne
            · cases hbb : st.negOnTrail l2 with
              | true => rfl
              | false =>
                  have : (!st.negOnTrail l2) = true := by rw [hbb]; rfl
                  exact absurd this hkeep
          -- l2 trail-negated ⟹ false at a (entry-level argument,
          -- no normalization premise needed):
          unfold State.negOnTrail at hnt
          rw [List.any_eq_true] at hnt
          obtain ⟨e, hem, heb⟩ := hnt
          have hlit : e.literal = l2.negate.norm := by
            simpa only [litEqB, decide_eq_true_eq] using heb
          have hev : e.literal.eval a = some true := hsat e hem
          rw [hlit, Literal.norm_eval (l2.negate) a,
            Literal.eval_negate l2 a] at hev
          -- hev : (l2.eval a).map (!·) = some true
          rw [hev2] at hev
          simp at hev
    | l1 :: l2 :: rest =>
        rw [hh] at h
        simp only [] at h
        cases h


theorem scanClause_conflict_falsified' {st : State} {c : Clause}
    {a : Assignment}
    (h : scanClause st c = some (.inl c))
    (hsat : st.TrailSatisfied a) :
    ∀ l ∈ c, l.eval a = some false := by
  intro l hl
  -- the second component of negOnTrail_falsifies is `l = l.norm`;
  -- supply the entry-level argument directly instead (no norm need)
  have hneg : st.negOnTrail l = true := by
    unfold scanClause at h
    split at h
    · exact absurd h (by simp)
    · rename_i hany
      have hfil : (c.filter (fun l => !st.negOnTrail l)) = [] := by
        match hh : (c.filter (fun l => !st.negOnTrail l)) with
        | [] => rfl
        | l' :: rest =>
            rw [hh] at h
            match rest with
            | [] => simp only [] at h; cases h
            | l2 :: rest2 => simp only [] at h; cases h
      by_cases hbb : st.negOnTrail l = true
      · exact hbb
      · exfalso
        have hfalse : st.negOnTrail l = false := by
          cases hbb2 : st.negOnTrail l with
          | true => exact absurd hbb2 hbb
          | false => rfl
        have hkeep : (!st.negOnTrail l) = true := by rw [hfalse]; rfl
        have hmem2 : l ∈ c.filter (fun l => !st.negOnTrail l) :=
          List.mem_filter.mpr ⟨hl, hkeep⟩
        rw [hfil] at hmem2
        exact absurd hmem2 (by simp)
  -- unfold the any-hit: some trail entry's literal is `l.negate.norm`,
  -- so it evaluates true at `a`, forcing `l` false by negation/norm
  -- eval identities (no normalization of `l` itself is needed)
  unfold State.negOnTrail at hneg
  rw [List.any_eq_true] at hneg
  obtain ⟨e, hem, heb⟩ := hneg
  have hlit : e.literal = l.negate.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit, Literal.norm_eval (l.negate) a,
    Literal.eval_negate l a] at hev
  -- hev : (l.eval a).map (! ·) = some true
  cases hval : l.eval a with
  | none => rw [hval] at hev; simp at hev
  | some b' =>
      rw [hval] at hev
      cases b' <;> simp at hev <;> rfl

/-! ## Root-fact validity (Step 2)

Every root fact pinning a slot's initial integer bounds is true at any
assignment fitting the domains, provided the slot's values have integer
views (the fragment invariant). -/

/-- Every literal of the root-fact scan satisfies the fitting
    assignment: the head literals bound slot `s`'s value by the domain
    extrema of `d` (which equals `doms`'s slot `s` by the suffix
    correspondence), and the tail recurses. The correspondence is an
    equality of slot domains plus a length bound. -/
theorem rootFacts_go_valid : ∀ (ds : List Domain) (s : Nat)
    (l : Literal) (doms : List Domain) (a : Assignment),
    s + ds.length ≤ doms.length →
    (∀ i, ds.getD i Dom.empty = doms.getD (s + i) Dom.empty) →
    l ∈ rootFacts.go s ds →
    a.Fits doms →
    (∀ v, v ∈ doms.getD l.atom.slot Dom.empty → Value.intView v ≠ none) →
    l.eval a = some true := by
  intro ds
  induction ds with
  | nil =>
      intro s l doms a _ _ hmem _ _
      rw [show rootFacts.go s [] = [] from rfl] at hmem
      exact absurd hmem (by simp)
  | cons d rest ih =>
      intro s l doms a hlen hcorr hmem hfit hview
      rw [show rootFacts.go s (d :: rest) =
        (match domMinI d, domMaxI d with
          | some mn, some mx =>
              negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
          | _, _ => rootFacts.go (s + 1) rest) from rfl] at hmem
      have hd0 : doms.getD s Dom.empty = d := by
        have h1 := hcorr 0
        simp only [List.getD_cons_zero, Nat.add_zero] at h1
        exact h1.symm
      have hslot : s < a.length := by
        obtain ⟨hl1, _⟩ := hfit
        -- domMinI doms-slot nonempty needed only when head literals
        -- exist; for the tail case recurse. For a uniform in-range
        -- bound note ds = d :: rest has length ≥ 1, so s < doms.length:
        rw [hl1]
        have : (d :: rest).length = rest.length + 1 := rfl
        omega
      have hget : a[s]? = some a[s] :=
        (List.getElem?_eq_some_iff).mpr ⟨hslot, rfl⟩
      cases hmn : domMinI d with
      | none =>
          rw [hmn] at hmem
          simp only [] at hmem
          exact ih (s + 1) l doms a
            (by
              have : (d :: rest).length = rest.length + 1 := rfl
              omega)
            (fun i => by
              have h1 := hcorr (i + 1)
              simp only [List.getD_cons_succ] at h1
              show rest.getD i Dom.empty = doms.getD (s + 1 + i) Dom.empty
              rw [show s + 1 + i = s + (i + 1) from by omega]
              exact h1)
            hmem hfit hview
      | some mn =>
          rw [hmn] at hmem
          cases hmx : domMaxI d with
          | none =>
              rw [hmx] at hmem
              simp only [] at hmem
              exact ih (s + 1) l doms a
                (by
                  have : (d :: rest).length = rest.length + 1 := rfl
                  omega)
                (fun i => by
                  have h1 := hcorr (i + 1)
                  simp only [List.getD_cons_succ] at h1
                  show rest.getD i Dom.empty = doms.getD (s + 1 + i) Dom.empty
                  rw [show s + 1 + i = s + (i + 1) from by omega]
                  exact h1)
                hmem hfit hview
          | some mx =>
              rw [hmx] at hmem
              simp only [] at hmem
              rw [List.mem_cons] at hmem
              -- (keep this simp: it reduces the match now that both
              -- scrutinees are constructors)
              rcases hmem with rfl | hmem
              · -- l = negLe s (mn − 1): value at slot s ≥ mn
                have hmemV0 : a[s] ∈ doms.getD s Dom.empty := hfit.2 s a[s] hget
                have hmemV : a[s] ∈ d := by rw [← hd0]; exact hmemV0
                have hslotEq : (negLe s (mn - 1)).atom.slot = s := rfl
                have hv : Value.intView a[s] ≠ none := by
                  have := hview a[s]
                    (by
                      rw [hslotEq]
                      exact hmemV0)
                  exact this
                cases hva : Value.intView a[s] with
                | none => exact absurd hva hv
                | some i =>
                    have hbnd := domMinI_le a[s] i hva hmemV hmn
                    show (negLe s (mn - 1)).eval a = some true
                    rw [eval_negLe_iff]
                    refine ⟨i, ?_, ?_⟩
                    · show slotInt a s = some i
                      rw [slotInt, hget]
                      exact hva
                    · omega
              · rw [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · -- l = posLe s mx : value at slot s ≤ mx
                  have hmemV0 : a[s] ∈ doms.getD s Dom.empty := hfit.2 s a[s] hget
                  have hmemV : a[s] ∈ d := by rw [← hd0]; exact hmemV0
                  have hslotEq : (posLe s mx).atom.slot = s := rfl
                  have hv : Value.intView a[s] ≠ none := by
                    have := hview a[s]
                      (by
                        rw [hslotEq]
                        exact hmemV0)
                    exact this
                  cases hva : Value.intView a[s] with
                  | none => exact absurd hva hv
                  | some i =>
                      have hbnd := domMaxI_ge a[s] i hva hmemV hmx
                      show (posLe s mx).eval a = some true
                      rw [eval_posLe_iff]
                      refine ⟨i, ?_, ?_⟩
                      · show slotInt a s = some i
                        rw [slotInt, hget]
                        exact hva
                      · exact hbnd
                · -- tail: recurse
                  exact ih (s + 1) l doms a
                    (by
                      have : (d :: rest).length = rest.length + 1 := rfl
                      omega)
                    (fun i => by
                      have h1 := hcorr (i + 1)
                      simp only [List.getD_cons_succ] at h1
                      show rest.getD i Dom.empty = doms.getD (s + 1 + i) Dom.empty
                      rw [show s + 1 + i = s + (i + 1) from by omega]
                      exact h1)
                    hmem hfit hview

/-- The suffix correspondence for the base call: `doms`'s own suffixes
    and identity correspondence. -/
theorem rootFacts_valid {doms : List Domain} {a : Assignment}
    (hfit : a.Fits doms)
    (hview : ∀ l ∈ rootFacts doms,
      ∀ v, v ∈ doms.getD l.atom.slot Dom.empty → Value.intView v ≠ none) :
    ∀ l ∈ rootFacts doms, l.eval a = some true := by
  intro l hl
  have hgo : rootFacts doms = rootFacts.go 0 doms := rfl
  have hlgo : l ∈ rootFacts.go 0 doms := by rw [← hgo]; exact hl
  have hvw : ∀ v, v ∈ doms.getD l.atom.slot Dom.empty → Value.intView v ≠ none :=
    hview l hl
  exact rootFacts_go_valid doms 0 l doms a
    (by omega)
    (fun i => by
      show doms.getD i Dom.empty = doms.getD (0 + i) Dom.empty
      rw [Nat.zero_add])
    hlgo hfit hvw


/-! ## Domain coherence of the engine's state transitions (Step 2)

The invariant `DomainCoherent` — the state's domains equal the
`domOfLit` fold of its own trail from the problem's domains — is
preserved by `enqueueNorm` (all branches: skip / conflict-set /
fresh), rebuilt by construction in `repairAfterBackjump`, and
initiated trivially (root-fact enqueueing never changes the domains;
`domOfLit` at a root fact is the identity by the slot's own
extrema). -/

def DomainCoherent (problem : Problem Constraint Objective)
    (st : State) : Prop :=
  st.domains = st.trail.foldl (fun acc e => domOfLit acc e.literal)
    problem.domains

theorem enqueueNorm_fresh_coherent {problem : Problem Constraint Objective}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hcoh : DomainCoherent problem st)
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false) :
    DomainCoherent problem (enqueueNorm st l0 reason) := by
  unfold DomainCoherent at hcoh ⊢
  unfold enqueueNorm
  simp only [hnew, hneg, Bool.false_eq_true, if_false]
  -- Now zeta-reduce the let via show:
  show domOfLit (enqueue st l0.norm reason).domains l0.norm
    = (enqueue st l0.norm reason |>.trail).foldl
        (fun acc e => domOfLit acc e.literal) problem.domains
  -- (enqueue st l reason).domains = st.domains (enqueue doesn't touch them):
  have hdom : (enqueue st l0.norm reason).domains = st.domains := rfl
  rw [hdom]
  -- the trail fold: enqueue's trail = st.trail ++ [entry]:
  have htr : (enqueue st l0.norm reason).trail
      = st.trail ++ [TrailEntry.mk l0.norm st.decisionLevel reason] := rfl
  rw [htr, List.foldl_append]
  -- singleton fold: foldl f acc [e] = f acc e
  rw [List.foldl_cons, List.foldl_nil]
  -- both sides now: domOfLit st.domains l0.norm =
  -- domOfLit (foldl ... problem.domains st.trail) l0.norm
  rw [hcoh]

/-- The already-on-trail branch: no state change, so coherence is
    trivially preserved. -/
theorem enqueueNorm_skip_coherent {problem : Problem Constraint Objective}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hcoh : DomainCoherent problem st)
    (hnew : st.litOnTrail l0.norm = true) :
    DomainCoherent problem (enqueueNorm st l0 reason) := by
  unfold enqueueNorm
  simp only [hnew, if_pos]
  exact hcoh

/-- The opposite-fact branch: coherence still holds (only the
    conflict field is set). -/
theorem enqueueNorm_conflict_coherent {problem : Problem Constraint Objective}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hcoh : DomainCoherent problem st)
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = true) :
    DomainCoherent problem (enqueueNorm st l0 reason) := by
  unfold enqueueNorm
  simp only [hnew, hneg, Bool.false_eq_true, if_false, if_pos]
  exact hcoh

/-- `enqueueNorm` preserves domain coherence in every branch. -/
theorem enqueueNorm_coherent {problem : Problem Constraint Objective}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hcoh : DomainCoherent problem st) :
    DomainCoherent problem (enqueueNorm st l0 reason) := by
  unfold enqueueNorm
  cases hnew : st.litOnTrail (Literal.norm l0) with
  | true =>
      simp only [hnew, if_pos]
      exact hcoh
  | false =>
      simp only [hnew, Bool.false_eq_true, if_false]
      cases hneg : st.negOnTrail (Literal.norm l0) with
      | true =>
          simp only [hneg, if_pos]
          exact hcoh
      | false =>
          simp only [hneg, Bool.false_eq_true, if_false]
          -- the fresh branch — same proof as enqueueNorm_fresh_coherent:
          unfold DomainCoherent at hcoh ⊢
          show domOfLit (enqueue st (Literal.norm l0) reason).domains
              (Literal.norm l0)
            = List.foldl (fun acc e => domOfLit acc e.literal)
                problem.domains (enqueue st (Literal.norm l0) reason).trail
          have hdom : (enqueue st (Literal.norm l0) reason).domains
              = st.domains := rfl
          rw [hdom]
          have htr : (enqueue st (Literal.norm l0) reason).trail
              = st.trail ++ [TrailEntry.mk (Literal.norm l0)
                  st.decisionLevel reason] := rfl
          rw [htr, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [hcoh]

/-- Filter over an all-passing list is the identity. -/
theorem filter_all_true_id {α : Type} {p : α → Bool} {ls : List α}
    (h : ∀ x ∈ ls, p x = true) : ls.filter p = ls := by
  induction ls with
  | nil => rfl
  | cons x rest ih =>
      have hx : p x = true := h x (List.mem_cons_self)
      have hrest : ∀ y ∈ rest, p y = true :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      show List.filter p (x :: rest) = x :: rest
      rw [List.filter_cons, hx]
      simp only [reduceIte]
      rw [ih hrest]

/-- `domFilterInt` is the identity when every enumerated value passes. -/
theorem domFilterInt_self {d : Domain} {keep : Int → Bool}
    (h : ∀ v ∈ Dom.enum d, domFilterIntKeep keep v = true) :
    domFilterInt keep d = d := by
  unfold domFilterInt
  dsimp only
  have hfil : (Dom.enum d).filter (domFilterIntKeep keep) = Dom.enum d :=
    filter_all_true_id h
  split
  · rfl
  · rename_i hne
    exfalso
    apply hne
    rw [hfil]

/-- `updateSlot` with an identity-on-target-slot function is the
    identity. -/
theorem updateSlot_id : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain),
    f (doms.getD s Dom.empty) = doms.getD s Dom.empty →
    updateSlot doms s f = doms := by
  intro doms s f h
  unfold updateSlot
  rw [h]
  induction doms generalizing s with
  | nil => cases s <;> rfl
  | cons d ds ih =>
      cases s with
      | zero => rfl
      | succ s' =>
          simp only [List.set_cons_succ, List.getD_cons_succ]
          rw [ih s' (by simpa only [List.getD_cons_succ] using h)]

/-- Values within their own domain's maximum pass the `≤ mx` filter. -/
theorem domOfLit_rootFact_pos {doms : List Domain} {s : Nat}
    {mx : Int}
    (hmax : domMaxI (doms.getD s Dom.empty) = some mx) :
    domOfLit doms (posLe s mx) = doms := by
  unfold domOfLit updateSlot
  show (updateSlot doms s
      (fun d => domFilterInt (fun p => decide (p ≤ mx)) d)) = doms
  refine updateSlot_id doms s _ ?_
  -- every value of the slot passes:
  refine domFilterInt_self ?_
  intro v hv
  cases hva : Value.intView v with
  | none =>
      cases v with
      | int p => exact absurd hva (by simp [Value.intView])
      | bool b => exact absurd hva (by simp [Value.intView])
      | setOfInt x => rfl
      | array x => rfl
  | some i =>
      have hbnd := domMaxI_ge v i hva ((DomainLike.mem_iff _ v).mpr hv) hmax
      cases v with
      | int p =>
          rw [Value.intView] at hva
          rw [Option.some.injEq] at hva
          -- p = i
          show decide (p ≤ mx) = true
          exact decide_eq_true (by omega)
      | bool b =>
          have hview : Value.intView (Value.bool b) =
              some (if b then 1 else 0) := rfl
          show decide ((if b then 1 else 0) ≤ mx) = true
          rw [hview] at hva
          rw [Option.some.injEq] at hva
          exact decide_eq_true (by omega)
      | setOfInt x => exact absurd hva (by simp [Value.intView])
      | array x => exact absurd hva (by simp [Value.intView])

/-- Values within their own domain's minimum pass the `> mn-1`
    filter. -/
theorem domOfLit_rootFact_neg {doms : List Domain} {s : Nat}
    {mn : Int}
    (hmin : domMinI (doms.getD s Dom.empty) = some mn) :
    domOfLit doms (negLe s (mn - 1)) = doms := by
  unfold domOfLit updateSlot
  show (updateSlot doms s
      (fun d => domFilterInt (fun p => decide (p > mn - 1)) d)) = doms
  refine updateSlot_id doms s _ ?_
  refine domFilterInt_self ?_
  intro v hv
  cases hva : Value.intView v with
  | none =>
      cases v with
      | int p => exact absurd hva (by simp [Value.intView])
      | bool b => exact absurd hva (by simp [Value.intView])
      | setOfInt x => rfl
      | array x => rfl
  | some i =>
      have hbnd := domMinI_le v i hva ((DomainLike.mem_iff _ v).mpr hv) hmin
      cases v with
      | int p =>
          rw [Value.intView] at hva
          rw [Option.some.injEq] at hva
          show decide (p > mn - 1) = true
          exact decide_eq_true (by omega)
      | bool b =>
          have hview : Value.intView (Value.bool b) =
              some (if b then 1 else 0) := rfl
          show decide ((if b then 1 else 0) > mn - 1) = true
          rw [hview] at hva
          rw [Option.some.injEq] at hva
          exact decide_eq_true (by omega)
      | setOfInt x => exact absurd hva (by simp [Value.intView])
      | array x => exact absurd hva (by simp [Value.intView])

/-- The initial state is trivially coherent (empty trail). -/
theorem initialState_coherent (problem : Problem Constraint Objective) :
    (initialState problem).domains = problem.domains := rfl

/-- THE INITIAL-STATE FOLD: the fold over root facts with plain
    `enqueue` leaves the state's domains unchanged (enqueue doesn't
    touch domains). -/
theorem rootFold_domains : ∀ (rs : List Literal) (st : State),
    ((rs.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none) st).domains
        = st.domains) := by
  intro rs
  induction rs with
  | nil => intro st; rfl
  | cons l rest ih =>
      intro st
      rw [List.foldl_cons]
      cases hnew : st.litOnTrail l with
      | true =>
          show (List.foldl (fun st l =>
              if st.litOnTrail l then st else enqueue st l none) st rest).domains
            = st.domains
          exact ih st
      | false =>
          rw [show ((if false = true then st else enqueue st l none) : State)
              = enqueue st l none from if_neg (by intro h; exact Bool.noConfusion h)]
          have hdom := ih (enqueue st l none)
          rw [hdom]
          rfl

/-- initialValues: initialStateWithRoots' domains are the problem's
    (the root fold never changes them). -/
theorem initialStateWithRoots_domains (problem : Problem Constraint Objective) :
    (initialStateWithRoots problem).domains = problem.domains := by
  unfold initialStateWithRoots
  exact rootFold_domains (rootFacts problem.domains) (initialState problem)

/-- `repairAfterBackjump` rebuilds domains exactly as the coherence
    fold over the KEPT trail — regardless of the incoming state, the
    output is coherent by construction. -/
theorem repairAfterBackjump_coherent (problem : Problem Constraint Objective)
    (level : Nat) (st : State) :
    DomainCoherent problem (repairAfterBackjump problem level st) := by
  unfold DomainCoherent repairAfterBackjump
  show (st.trail.filter fun e => e.level ≤ level).foldl
      (fun acc e => domOfLit acc e.literal) problem.domains =
    (st.trail.filter fun e => e.level ≤ level).foldl
      (fun acc e => domOfLit acc e.literal) problem.domains
  rfl

/-! ### The root-fact fold identity -/

/-- The root-fact list's fold of `domOfLit` is the identity, given the
    suffix correspondence and accumulator agreement. -/
theorem rootFacts_go_fold_id : ∀ (ds : List Domain) (s : Nat)
    (doms acc : List Domain),
    (∀ i, ds.getD i Dom.empty = doms.getD (s + i) Dom.empty) →
    (∀ j, acc.getD j Dom.empty = doms.getD j Dom.empty) →
    (rootFacts.go s ds).foldl (fun acc l => domOfLit acc l) acc = acc := by
  intro ds
  induction ds with
  | nil => intro s doms acc _ _; rfl
  | cons d rest ih =>
      intro s doms acc hcorr haccinv
      -- the accumulator's slot s is exactly d:
      have hd0 : acc.getD s Dom.empty = d := by
        have h1 := hcorr 0
        simp only [List.getD_cons_zero, Nat.add_zero] at h1
        rw [haccinv s, h1]
      -- accumulator agreement for the recursive call: unchanged by
      -- the two identity steps, so we only need the tail's ih
      have hreccorr : ∀ i, rest.getD i Dom.empty = doms.getD (s + 1 + i) Dom.empty := by
        intro i
        have h1 := hcorr (i + 1)
        simp only [List.getD_cons_succ] at h1
        rw [show s + 1 + i = s + (i + 1) from by omega]
        exact h1
      have htail := ih (s + 1) doms acc hreccorr haccinv
      -- now case the two extrema of d:
      cases hmn : domMinI d with
      | none =>
          rw [show rootFacts.go s (d :: rest) =
              (match domMinI d, domMaxI d with
                | some mn, some mx =>
                    negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
                | _, _ => rootFacts.go (s + 1) rest) from rfl,
              hmn]
          exact htail
      | some mn =>
          cases hmx : domMaxI d with
          | none =>
              rw [show rootFacts.go s (d :: rest) =
                  (match domMinI d, domMaxI d with
                    | some mn, some mx =>
                        negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
                    | _, _ => rootFacts.go (s + 1) rest) from rfl,
                  hmn, hmx]
              exact htail
          | some mx =>
              rw [show rootFacts.go s (d :: rest) =
                  (match domMinI d, domMaxI d with
                    | some mn, some mx =>
                        negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
                    | _, _ => rootFacts.go (s + 1) rest) from rfl,
                  hmn, hmx,
                List.foldl_cons, List.foldl_cons]
              -- step 1: domOfLit acc (negLe s (mn - 1)) = acc
              have hstep1 : domOfLit acc (negLe s (mn - 1)) = acc := by
                refine domOfLit_rootFact_neg (doms := acc) (s := s) (mn := mn) ?_
                rw [hd0, hmn]
              -- step 2: domOfLit acc (posLe s mx) = acc
              have hstep2 : domOfLit acc (posLe s mx) = acc := by
                refine domOfLit_rootFact_pos (doms := acc) (s := s) (mx := mx) ?_
                rw [hd0, hmx]
              rw [hstep1, hstep2]
              exact htail

/-! ### Root-fact membership characterization -/

/-- Root-fact membership characterization: every literal of the scan at
    base slot `s` is `negLe s' (k−1)` with `domMinI` of `doms`'s slot
    `s'` equal to `some k`, or `posLe s' k` with the matching max, for
    some slot `s' ≥ s`. -/
theorem rootFacts_go_mem : ∀ (ds doms : List Domain) (s : Nat)
    (l : Literal), l ∈ rootFacts.go s ds →
    (∀ i, ds.getD i Dom.empty = doms.getD (s + i) Dom.empty) →
    (∃ s' k, s ≤ s' ∧ l = negLe s' (k - 1) ∧
        domMinI (doms.getD s' Dom.empty) = some k) ∨
    (∃ s' k, s ≤ s' ∧ l = posLe s' k ∧
        domMaxI (doms.getD s' Dom.empty) = some k) := by
  intro ds
  induction ds with
  | nil =>
      intro doms s l hmem _
      rw [show rootFacts.go s [] = [] from rfl] at hmem
      exact absurd hmem (by simp)
  | cons d rest ih =>
      intro doms s l hmem hcorr
      have hd0 : doms.getD s Dom.empty = d := by
        have h1 := hcorr 0
        simp only [List.getD_cons_zero, Nat.add_zero] at h1
        exact h1.symm
      have hreccorr : ∀ i, rest.getD i Dom.empty = doms.getD (s + 1 + i) Dom.empty := by
        intro i
        have h1 := hcorr (i + 1)
        simp only [List.getD_cons_succ] at h1
        rw [show s + 1 + i = s + (i + 1) from by omega]
        exact h1
      rw [show rootFacts.go s (d :: rest) =
        (match domMinI d, domMaxI d with
          | some mn, some mx =>
              negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
          | _, _ => rootFacts.go (s + 1) rest) from rfl] at hmem
      cases hmn : domMinI d with
      | none =>
          have hred : (match domMinI d, domMaxI d with
              | some mn, some mx =>
                  negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
              | _, _ => rootFacts.go (s + 1) rest) = rootFacts.go (s + 1) rest := by
            rw [hmn]
          rw [hred] at hmem
          rcases ih doms (s + 1) l hmem hreccorr with
            ⟨s', k, hle, hlit, hext⟩ | ⟨s', k, hle, hlit, hext⟩
          · exact Or.inl ⟨s', k, by omega, hlit, hext⟩
          · exact Or.inr ⟨s', k, by omega, hlit, hext⟩
      | some mn =>
          cases hmx : domMaxI d with
          | none =>
              have hred : (match domMinI d, domMaxI d with
                  | some mn, some mx =>
                      negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
                  | _, _ => rootFacts.go (s + 1) rest) = rootFacts.go (s + 1) rest := by
                rw [hmn, hmx]
              rw [hred] at hmem
              rcases ih doms (s + 1) l hmem hreccorr with
                ⟨s', k, hle, hlit, hext⟩ | ⟨s', k, hle, hlit, hext⟩
              · exact Or.inl ⟨s', k, by omega, hlit, hext⟩
              · exact Or.inr ⟨s', k, by omega, hlit, hext⟩
          | some mx =>
              have hred : (match domMinI d, domMaxI d with
                  | some mn, some mx =>
                      negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest
                  | _, _ => rootFacts.go (s + 1) rest) =
                  negLe s (mn - 1) :: posLe s mx :: rootFacts.go (s + 1) rest := by
                rw [hmn, hmx]
              rw [hred] at hmem
              rw [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact Or.inl ⟨s, mn, Nat.le_refl _, rfl,
                  by rw [hd0]; exact hmn⟩
              · rw [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · exact Or.inr ⟨s, mx, Nat.le_refl _, rfl,
                    by rw [hd0]; exact hmx⟩
                · rcases ih doms (s + 1) l hmem hreccorr with
                    ⟨s', k, hle, hlit, hext⟩ | ⟨s', k, hle, hlit, hext⟩
                  · exact Or.inl ⟨s', k, by omega, hlit, hext⟩
                  · exact Or.inr ⟨s', k, by omega, hlit, hext⟩

/-! ### The initial-fold trail coherence -/

/-- THE INITIAL-FOLD COHERENCE (carried invariant form): folding
    (skip-or-enqueue) over a list of domain-identity literals from an
    initial state whose trail-fold already equals its domains
    preserves exactly that: every enqueue step appends an entry whose
    `domOfLit` is the identity on the current fold accumulator (which
    agrees with `doms` on every slot). -/
theorem initialFold_trail_fold : ∀ (rs : List Literal)
    (doms : List Domain) (st : State),
    (∀ l ∈ rs, ∀ acc, (∀ j, acc.getD j Dom.empty = doms.getD j Dom.empty) →
      domOfLit acc l = acc) →
    (st.domains = doms) →
    (st.trail.foldl (fun acc e => domOfLit acc e.literal) st.domains
      = st.domains) →
    ((rs.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none) st).trail.foldl
        (fun acc e => domOfLit acc e.literal) st.domains
      = st.domains) := by
  intro rs
  induction rs with
  | nil => intro doms st _ _ hinv; exact hinv
  | cons l rest ih =>
      intro doms st hid hdom hinv
      rw [List.foldl_cons]
      cases hnew : st.litOnTrail l with
      | true =>
          rw [show ((if true = true then st else enqueue st l none) : State)
              = st from if_pos rfl]
          exact ih doms st
            (fun l' hl' => hid l' (List.mem_cons_of_mem _ hl')) hdom hinv
      | false =>
          rw [show ((if false = true then st else enqueue st l none) : State)
              = enqueue st l none from
              if_neg (by intro h; exact Bool.noConfusion h)]
          -- the new state's trail-fold:
          have htr1 : (enqueue st l none).trail
              = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
          have hnewinv : (enqueue st l none).trail.foldl
              (fun acc e => domOfLit acc e.literal) st.domains
              = st.domains := by
            rw [htr1, List.foldl_append, List.foldl_cons, List.foldl_nil]
            -- fold st.trail = st.domains (hinv), then one identity step:
            rw [show List.foldl (fun acc e => domOfLit acc e.literal)
                st.domains st.trail = st.domains from hinv]
            -- the step: domOfLit st.domains l = st.domains — by hid
            -- with agreement (st.domains = doms):
            rw [show domOfLit st.domains l = st.domains from
              hid l (List.mem_cons_self) st.domains
                (fun j => by
                  have : st.domains.getD j Dom.empty = doms.getD j Dom.empty := by
                    rw [hdom]
                  rw [this])]
          exact ih doms (enqueue st l none)
            (fun l' hl' => hid l' (List.mem_cons_of_mem _ hl'))
            (by rw [show (enqueue st l none).domains = st.domains from rfl,
              hdom])
            hnewinv

/-- THE INITIAL-STATE COHERENCE (final): the domains of
    `initialStateWithRoots` equal the trail-fold of `domOfLit` over its
    own trail from the problem's domains. -/
theorem initialStateWithRoots_coherent (problem : Problem Constraint Objective) :
    (initialStateWithRoots problem).domains =
    (initialStateWithRoots problem).trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains := by
  -- the per-literal identity premise over root facts:
  have hid : ∀ l ∈ rootFacts problem.domains,
      ∀ acc, (∀ j, acc.getD j Dom.empty = problem.domains.getD j Dom.empty) →
        domOfLit acc l = acc := by
    intro l hl acc hagree
    have hgo : rootFacts problem.domains
        = rootFacts.go 0 problem.domains := rfl
    rcases rootFacts_go_mem problem.domains problem.domains 0 l
      (by rw [← hgo]; exact hl)
      (fun i => by
        show problem.domains.getD i Dom.empty = problem.domains.getD (0 + i) Dom.empty
        rw [Nat.zero_add]) with
      ⟨s, k, _, hlit, hext⟩ | ⟨s, k, _, hlit, hext⟩
    · rw [hlit]
      refine domOfLit_rootFact_neg (doms := acc) (s := s) (mn := k) ?_
      rw [hagree s]
      exact hext
    · rw [hlit]
      refine domOfLit_rootFact_pos (doms := acc) (s := s) (mx := k) ?_
      rw [hagree s]
      exact hext
  -- assemble from the initial state:
  have hdom : (initialState problem).domains = problem.domains := rfl
  have hempty : (initialState problem).trail = [] := rfl
  have hbase : (initialState problem).trail.foldl
      (fun acc e => domOfLit acc e.literal) (initialState problem).domains
      = (initialState problem).domains := by
    rw [hempty, List.foldl_nil]
  have hres := initialFold_trail_fold (rootFacts problem.domains)
    problem.domains (initialState problem) hid
    (by rw [hdom])
    (by rw [hdom] at hbase; exact hbase)
  unfold initialStateWithRoots
  show (List.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none)
      (initialState problem) (rootFacts problem.domains)).domains =
    List.foldl (fun acc e => domOfLit acc e.literal) problem.domains
      (List.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none)
      (initialState problem) (rootFacts problem.domains)).trail
  -- the fold-result's domains = (initialState problem).domains
  -- (enqueue never changes domains — rootFold_domains):
  have hfolddom : (List.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none)
      (initialState problem) (rootFacts problem.domains)).domains
      = (initialState problem).domains :=
    rootFold_domains (rootFacts problem.domains) (initialState problem)
  rw [hfolddom, hdom]
  exact hres.symm

end LeanFzn.Solver.Propagation

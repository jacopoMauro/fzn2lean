/-
Purpose: LinearExt propagators: reified definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.LinearExt.Plans
DAG: LeanFzn.Engine.Props.LinearExt.Plans -> LeanFzn.Engine.Props.LinearExt.Reified.
-/
import LeanFzn.Engine.Props.LinearExt.Plans

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Reification: shared plan glue -/

theorem Entailed_append_lit (p : CompiledProblem DomConstraint) (l : Literal)
    {c : Clause} (h : Entailed p c) : Entailed p (c ++ [l]) := by
  intro a ha hacc
  obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp (h a ha hacc)
  exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

def linPlanAppendLit (plan : LinPlan) (l : Literal) : LinPlan :=
  { conflict? := plan.conflict?.map (fun ls => ls ++ [l])
    prunes := plan.prunes.map (fun q => (q.1, q.2 ++ [l])) }

theorem linPlanAppendLit_conf_mem {plan : LinPlan} {l : Literal} {ls : List Literal}
    (h : (linPlanAppendLit plan l).conflict? = some ls) :
    ∃ ls0, plan.conflict? = some ls0 ∧ ls = ls0 ++ [l] := by
  unfold linPlanAppendLit at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨ls0, hls0, hls⟩ := h
  exact ⟨ls0, hls0, hls.symm⟩

theorem linPlanAppendLit_prunes_mem {plan : LinPlan} {l l' : Literal} {r : Clause}
    (h : (l', r) ∈ (linPlanAppendLit plan l).prunes) :
    ∃ r0, (l', r0) ∈ plan.prunes ∧ r = r0 ++ [l] := by
  unfold linPlanAppendLit at h
  rw [List.mem_map] at h
  obtain ⟨⟨ql, qr⟩, hq, hpair⟩ := h
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨h1, h2⟩ := hpair
  subst h1
  subst h2
  exact ⟨qr, hq, rfl⟩

theorem linPlanAppendLit_conf_entailed {p : CompiledProblem DomConstraint} {plan : LinPlan}
    {l : Literal} (h : ∀ ls, plan.conflict? = some ls → Entailed p ls) :
    ∀ ls, (linPlanAppendLit plan l).conflict? = some ls → Entailed p ls := by
  intro ls hls
  obtain ⟨ls0, h0, rfl⟩ := linPlanAppendLit_conf_mem hls
  exact Entailed_append_lit p l (h ls0 h0)

theorem linPlanAppendLit_prunes_entailed {p : CompiledProblem DomConstraint} {plan : LinPlan}
    {l : Literal} (h : ∀ l' r, (l', r) ∈ plan.prunes → Entailed p r) :
    ∀ l' r, (l', r) ∈ (linPlanAppendLit plan l).prunes → Entailed p r := by
  intro l' r hr
  obtain ⟨r0, h0, rfl⟩ := linPlanAppendLit_prunes_mem hr
  exact Entailed_append_lit p l (h l' r0 h0)

def linPlanSingle (l : Literal) (reason : Clause) : LinPlan :=
  { conflict? := none, prunes := [(l, reason)] }

def linPlanEmpty : LinPlan :=
  { conflict? := none, prunes := [] }

theorem linPlanSingle_prunes {l : Literal} {reason : Clause} {l' : Literal} {r : Clause}
    (h : (l', r) ∈ (linPlanSingle l reason).prunes) :
    l' = l ∧ r = reason := by
  simp only [linPlanSingle, List.mem_singleton] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Boolean reification literals -/

theorem domC_evalLit_posBool_true_iff {d : DomC} {r : Nat} {b : Bool} :
    d.evalLit (posBool r b) = some true ↔ d.fixedValue = some (.bool b) := by
  simp only [DomC.evalLit, posBool]
  cases h : d.fixedValue with
  | none => simp
  | some v =>
      cases v with
      | bool x => cases b <;> cases x <;> simp
      | int x => simp
      | setOfInt x => simp
      | array x => simp

theorem domC_evalLit_posBool_false_iff {d : DomC} {r : Nat} {b : Bool} :
    d.evalLit (posBool r b) = some false ↔ d.fixedValue = some (.bool (!b)) := by
  simp only [DomC.evalLit, posBool]
  cases h : d.fixedValue with
  | none => simp
  | some v =>
      cases v with
      | bool x => cases b <;> cases x <;> simp
      | int x => simp
      | setOfInt x => simp
      | array x => simp

theorem domC_evalLit_posBool_none_iff {d : DomC} {r : Nat} {b : Bool} :
    d.evalLit (posBool r b) = none ↔ ∀ x, d.fixedValue ≠ some (.bool x) := by
  simp only [DomC.evalLit, posBool]
  cases h : d.fixedValue with
  | none => simp
  | some v =>
      cases v with
      | bool x =>
          cases b <;> cases x <;> simp
      | int x => simp
      | setOfInt x => simp
      | array x => simp

/-! ## Accepted-assignment facts for the reifications -/

/-- Under the problem-level integer guard the dot product exists. -/
theorem dotProduct_some_of_slotsIntB (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hslots : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains) :
    ∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some d := by
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    obtain ⟨x, hx⟩ := slotsIntB_spec hslots ha (by simpa using hs)
    refine ⟨x, ?_⟩
    rw [List.getElem!_eq_getElem?_getD, hx]
    rfl
  -- the size needed by `dotProduct_eq_linDotSum` is only `bds.size = slots.size`
  obtain ⟨bds, hbds⟩ : ∃ bds : Array (Int × Int), bds.size = is.toArray.size :=
    ⟨is.toArray.map fun _ => (0, 0), by simp⟩
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
    (slots := is.toArray) (bds := bds) hsize hbds a hxall
  exact ⟨_, hbridge⟩

theorem linLeReif_rel_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) :
    ∃ rb, a[r]? = some (.bool rb) ∧
      (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
        ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≤ b) ∧
      (rb = false → b + 1 ≤ linDotSum (linTerms coeffs.toArray is.toArray bds) a) := by
  have hdc : (DomConstraint.linLeReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdef : (DomConstraint.linLeReif coeffs is b r).satisfiedB a =
      (match a[r]? with
       | some (.bool rb') =>
           decide (rb' = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b)
       | _ => false) := rfl
  rw [hdef] at hdc
  split at hdc
  · rename_i rb hrb
    have hrel : rb = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b :=
      of_decide_eq_true hdc
    obtain ⟨d, hdp⟩ := dotProduct_some_of_slotsIntB p coeffs is hsize hslots ha
    have hdp' : dotProduct (intVals coeffs)
        (is.map (fun i => a[i]?.getD default)) = some d := by simpa using hdp
    have hdle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = decide (d ≤ b) := by
      simp [dotLe, hdp']
    rw [hdle] at hrel
    have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
    have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
      intro s hs
      exact dotProduct_reads_int_local (is := is) hdp s (by simpa using hs)
    have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
      (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
    have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
      Option.some.inj (hdp.symm.trans hbridge)
    refine ⟨rb, hrb, ?_, ?_, ?_⟩
    · exact linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hdp
    · intro hrbt
      rw [hrbt] at hrel
      have hle : decide (d ≤ b) = true := hrel.symm
      have := of_decide_eq_true hle
      omega
    · intro hrbf
      rw [hrbf] at hrel
      have hle : decide (d ≤ b) = false := hrel.symm
      have := of_decide_eq_false hle
      omega
  · simp at hdc

theorem linEqReif_rel_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) :
    ∃ rb, a[r]? = some (.bool rb) ∧
      (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
        ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) ∧
      (rb = false → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) := by
  have hdc : (DomConstraint.linEqReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdef : (DomConstraint.linEqReif coeffs is b r).satisfiedB a =
      (match a[r]? with
       | some (.bool rb') =>
           decide (rb' =
             (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
              | some d => decide (d = b)
              | none => false))
       | _ => false) := rfl
  rw [hdef] at hdc
  split at hdc
  · rename_i rb hrb
    have hrel : rb =
        (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
         | some d => decide (d = b)
         | none => false) := of_decide_eq_true hdc
    obtain ⟨d, hdp⟩ := dotProduct_some_of_slotsIntB p coeffs is hsize hslots ha
    have hdp' : dotProduct (intVals coeffs)
        (is.map (fun i => a[i]?.getD default)) = some d := by simpa using hdp
    have hrel' : rb = decide (d = b) := by simpa [hdp'] using hrel
    have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
    have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
      intro s hs
      exact dotProduct_reads_int_local (is := is) hdp s (by simpa using hs)
    have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
      (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
    have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
      Option.some.inj (hdp.symm.trans hbridge)
    refine ⟨rb, hrb, ?_, ?_, ?_⟩
    · exact linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hdp
    · intro hrbt
      rw [hrbt] at hrel'
      have hdec : decide (d = b) = true := hrel'.symm
      have := of_decide_eq_true hdec
      omega
    · intro hrbf
      rw [hrbf] at hrel'
      have hdec : decide (d = b) = false := hrel'.symm
      have := of_decide_eq_false hdec
      omega
  · simp at hdc

theorem linNeReif_rel_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) :
    ∃ rb, a[r]? = some (.bool rb) ∧
      (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
        ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) ∧
      (rb = false → linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) := by
  have hdc : (DomConstraint.linNeReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdef : (DomConstraint.linNeReif coeffs is b r).satisfiedB a =
      (match a[r]? with
       | some (.bool rb') =>
           decide (rb' = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b)
       | _ => false) := rfl
  rw [hdef] at hdc
  split at hdc
  · rename_i rb hrb
    have hrel : rb = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b :=
      of_decide_eq_true hdc
    obtain ⟨d, hdp⟩ := dotProduct_some_of_slotsIntB p coeffs is hsize hslots ha
    have hdp' : dotProduct (intVals coeffs)
        (is.map (fun i => a[i]?.getD default)) = some d := by simpa using hdp
    have hdne : dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = decide (d ≠ b) := by
      simp [dotNe, hdp']
    rw [hdne] at hrel
    have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
    have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
      intro s hs
      exact dotProduct_reads_int_local (is := is) hdp s (by simpa using hs)
    have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
      (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
    have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
      Option.some.inj (hdp.symm.trans hbridge)
    refine ⟨rb, hrb, ?_, ?_, ?_⟩
    · exact linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hdp
    · intro hrbt
      rw [hrbt] at hrel
      have hne : decide (d ≠ b) = true := hrel.symm
      have := of_decide_eq_true hne
      omega
    · intro hrbf
      rw [hrbf] at hrel
      have hne : decide (d ≠ b) = false := hrel.symm
      have := of_decide_eq_false hne
      omega
  · simp at hdc

/-! ## Decision plans for the reifications -/

theorem linMaxLits_satisfied_or_all_false {terms : List LinTerm} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x) :
    Clause.SatisfiedBy (linMaxLits terms) a ∨
      ∀ l ∈ linMaxLits terms, l.eval a = some false := by
  by_cases hs : Clause.SatisfiedBy (linMaxLits terms) a
  · exact Or.inl hs
  · right
    intro l hl
    obtain ⟨t, ht, hft⟩ := List.mem_map.mp hl
    subst hft
    obtain ⟨x, hx⟩ := hint t ht
    exact linMaxNegLit_eval_false_of_not_true hx (by
      intro htrue
      exact hs (Clause.satisfiedBy_iff.mpr
        ⟨linMaxNegLit t.s t.c t.lo t.hi, List.mem_map.mpr ⟨t, ht, rfl⟩, htrue⟩))

theorem linConflictLits_satisfied_or_all_false {terms : List LinTerm} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x) :
    Clause.SatisfiedBy (linConflictLits terms) a ∨
      ∀ l ∈ linConflictLits terms, l.eval a = some false := by
  by_cases hs : Clause.SatisfiedBy (linConflictLits terms) a
  · exact Or.inl hs
  · right
    intro l hl
    obtain ⟨t, ht, hft⟩ := List.mem_map.mp hl
    subst hft
    obtain ⟨x, hx⟩ := hint t ht
    exact linMinNegLit_eval_false_of_not_true hx (by
      intro htrue
      exact hs (Clause.satisfiedBy_iff.mpr
        ⟨linMinNegLit t.s t.c t.lo t.hi, List.mem_map.mpr ⟨t, ht, rfl⟩, htrue⟩))

def linLeReifDecidePlan (r : Nat) (terms : List LinTerm) (b : Int) : LinPlan :=
  if linTotalMax terms ≤ b then
    linPlanSingle (posBool r true) (linMaxLits terms ++ [posBool r true])
  else if b < linTotalMin terms then
    linPlanSingle (posBool r false) (linConflictLits terms ++ [posBool r false])
  else
    linPlanEmpty

def linEqReifDecidePlan (r : Nat) (terms : List LinTerm) (b : Int) : LinPlan :=
  if linTotalMin terms = b ∧ linTotalMax terms = b then
    linPlanSingle (posBool r true)
      (linConflictLits terms ++ linMaxLits terms ++ [posBool r true])
  else if b < linTotalMin terms then
    linPlanSingle (posBool r false) (linConflictLits terms ++ [posBool r false])
  else if linTotalMax terms < b then
    linPlanSingle (posBool r false) (linMaxLits terms ++ [posBool r false])
  else
    linPlanEmpty

def linNeReifDecidePlan (r : Nat) (terms : List LinTerm) (b : Int) : LinPlan :=
  if b < linTotalMin terms then
    linPlanSingle (posBool r true) (linConflictLits terms ++ [posBool r true])
  else if linTotalMax terms < b then
    linPlanSingle (posBool r true) (linMaxLits terms ++ [posBool r true])
  else if linTotalMin terms = b ∧ linTotalMax terms = b then
    linPlanSingle (posBool r false)
      (linConflictLits terms ++ linMaxLits terms ++ [posBool r false])
  else
    linPlanEmpty

theorem linLeReifDecidePlan_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linLeReifDecidePlan r
      (linTerms coeffs.toArray is.toArray bds) b).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linLeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  unfold linLeReifDecidePlan at h
  split at h
  · rename_i hmax
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    subst hl
    subst hr
    by_cases hs : Clause.SatisfiedBy (linMaxLits (linTerms coeffs.toArray is.toArray bds)) a
    · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hs
      exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
    · have hall := (linMaxLits_satisfied_or_all_false hint).resolve_left hs
      have hle := linDotSum_le_linTotalMax
        (linTerms coeffs.toArray is.toArray bds) a hall
      have hrbT : rb' = true := by
        cases rb' with
        | true => rfl
        | false =>
            have := hfalse rfl
            omega
      exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
        rw [eval_posBool_iff, hrb', hrbT]⟩
  · split at h
    · rename_i hnotmax hmin
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      subst hl
      subst hr
      by_cases hs : Clause.SatisfiedBy (linConflictLits (linTerms coeffs.toArray is.toArray bds)) a
      · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hs
        exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      · have hall := (linConflictLits_satisfied_or_all_false hint).resolve_left hs
        have hge := linTotalMin_le_linDotSum
          (linTerms coeffs.toArray is.toArray bds) a hall
        have hrbF : rb' = false := by
          cases rb' with
          | false => rfl
          | true =>
              have := htrue rfl
              omega
        exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
          rw [eval_posBool_iff, hrb', hrbF]⟩
    · simp [linPlanEmpty] at h

theorem linEqReifDecidePlan_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linEqReifDecidePlan r
      (linTerms coeffs.toArray is.toArray bds) b).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linEqReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  unfold linEqReifDecidePlan at h
  split at h
  · rename_i heq
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    subst hl
    subst hr
    by_cases hminSat : Clause.SatisfiedBy
        (linConflictLits (linTerms coeffs.toArray is.toArray bds)) a
    · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hminSat
      exact Clause.satisfiedBy_iff.mpr
        ⟨l0, List.mem_append_left _ (List.mem_append_left _ hl0), hsat⟩
    · by_cases hmaxSat : Clause.SatisfiedBy
          (linMaxLits (linTerms coeffs.toArray is.toArray bds)) a
      · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hmaxSat
        exact Clause.satisfiedBy_iff.mpr
          ⟨l0, List.mem_append_left _ (List.mem_append_right _ hl0), hsat⟩
      · have hminAll := (linConflictLits_satisfied_or_all_false hint).resolve_left hminSat
        have hmaxAll := (linMaxLits_satisfied_or_all_false hint).resolve_left hmaxSat
        have hge := linTotalMin_le_linDotSum
          (linTerms coeffs.toArray is.toArray bds) a hminAll
        have hle := linDotSum_le_linTotalMax
          (linTerms coeffs.toArray is.toArray bds) a hmaxAll
        have hrbT : rb' = true := by
          cases rb' with
          | true => rfl
          | false =>
              have := hfalse rfl
              omega
        exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
          rw [eval_posBool_iff, hrb', hrbT]⟩
  · split at h
    · rename_i hneq hminconf
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      subst hl
      subst hr
      by_cases hminSat : Clause.SatisfiedBy
          (linConflictLits (linTerms coeffs.toArray is.toArray bds)) a
      · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hminSat
        exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      · have hminAll := (linConflictLits_satisfied_or_all_false hint).resolve_left hminSat
        have hge := linTotalMin_le_linDotSum
          (linTerms coeffs.toArray is.toArray bds) a hminAll
        have hrbF : rb' = false := by
          cases rb' with
          | false => rfl
          | true =>
              have := htrue rfl
              omega
        exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
          rw [eval_posBool_iff, hrb', hrbF]⟩
    · split at h
      · rename_i hnotmin hmaxconf
        obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
        subst hl
        subst hr
        by_cases hmaxSat : Clause.SatisfiedBy
            (linMaxLits (linTerms coeffs.toArray is.toArray bds)) a
        · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hmaxSat
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
        · have hmaxAll := (linMaxLits_satisfied_or_all_false hint).resolve_left hmaxSat
          have hle := linDotSum_le_linTotalMax
            (linTerms coeffs.toArray is.toArray bds) a hmaxAll
          have hrbF : rb' = false := by
            cases rb' with
            | false => rfl
            | true =>
                have := htrue rfl
                omega
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb', hrbF]⟩
      · simp [linPlanEmpty] at h

theorem linNeReifDecidePlan_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linNeReifDecidePlan r
      (linTerms coeffs.toArray is.toArray bds) b).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linNeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  unfold linNeReifDecidePlan at h
  split at h
  · rename_i hminconf
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    subst hl
    subst hr
    by_cases hminSat : Clause.SatisfiedBy
        (linConflictLits (linTerms coeffs.toArray is.toArray bds)) a
    · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hminSat
      exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
    · have hminAll := (linConflictLits_satisfied_or_all_false hint).resolve_left hminSat
      have hge := linTotalMin_le_linDotSum
        (linTerms coeffs.toArray is.toArray bds) a hminAll
      have hrbT : rb' = true := by
        cases rb' with
        | true => rfl
        | false =>
            have := hfalse rfl
            omega
      exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
        rw [eval_posBool_iff, hrb', hrbT]⟩
  · split at h
    · rename_i hnotmin hmaxconf
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      subst hl
      subst hr
      by_cases hmaxSat : Clause.SatisfiedBy
          (linMaxLits (linTerms coeffs.toArray is.toArray bds)) a
      · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hmaxSat
        exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      · have hmaxAll := (linMaxLits_satisfied_or_all_false hint).resolve_left hmaxSat
        have hle := linDotSum_le_linTotalMax
          (linTerms coeffs.toArray is.toArray bds) a hmaxAll
        have hrbT : rb' = true := by
          cases rb' with
          | true => rfl
          | false =>
              have := hfalse rfl
              omega
        exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
          rw [eval_posBool_iff, hrb', hrbT]⟩
    · split at h
      · rename_i hnoteq heq
        obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
        subst hl
        subst hr
        by_cases hminSat : Clause.SatisfiedBy
            (linConflictLits (linTerms coeffs.toArray is.toArray bds)) a
        · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hminSat
          exact Clause.satisfiedBy_iff.mpr
            ⟨l0, List.mem_append_left _ (List.mem_append_left _ hl0), hsat⟩
        · by_cases hmaxSat : Clause.SatisfiedBy
              (linMaxLits (linTerms coeffs.toArray is.toArray bds)) a
          · obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp hmaxSat
            exact Clause.satisfiedBy_iff.mpr
              ⟨l0, List.mem_append_left _ (List.mem_append_right _ hl0), hsat⟩
          · have hminAll := (linConflictLits_satisfied_or_all_false hint).resolve_left hminSat
            have hmaxAll := (linMaxLits_satisfied_or_all_false hint).resolve_left hmaxSat
            have hge := linTotalMin_le_linDotSum
              (linTerms coeffs.toArray is.toArray bds) a hminAll
            have hle := linDotSum_le_linTotalMax
              (linTerms coeffs.toArray is.toArray bds) a hmaxAll
            have hrbF : rb' = false := by
              cases rb' with
              | false => rfl
              | true =>
                  have := htrue rfl
                  omega
            exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
              rw [eval_posBool_iff, hrb', hrbF]⟩
      · simp [linPlanEmpty] at h

/-! ## Fixed-reification plan entailment -/

theorem linEqReif_fixed_conf_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {ls : List Literal}
    (h : (linPlanAppendLit
      (if rb then linEqPlan (linTerms coeffs.toArray is.toArray bds) b
       else linNePlan (linTerms coeffs.toArray is.toArray bds) b
         (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l))
      (posBool r (!rb))).conflict? = some ls) :
    Entailed p ls := by
  intro a ha hacc
  obtain ⟨ls0, h0, rfl⟩ := linPlanAppendLit_conf_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linEqReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linEqPlan_conf_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linNePlan_conf_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linEqReif_fixed_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linPlanAppendLit
      (if rb then linEqPlan (linTerms coeffs.toArray is.toArray bds) b
       else linNePlan (linTerms coeffs.toArray is.toArray bds) b
         (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l))
      (posBool r (!rb))).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨r0, h0, rfl⟩ := linPlanAppendLit_prunes_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linEqReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (l, r0) ∈ (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linEqPlan_prunes_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (l, r0) ∈ (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linNePlan_prunes_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linLeReif_fixed_conf_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {ls : List Literal}
    (h : (linPlanAppendLit
      (if rb then linLePlan (linTerms coeffs.toArray is.toArray bds) b
       else linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1))
      (posBool r (!rb))).conflict? = some ls) :
    Entailed p ls := by
  intro a ha hacc
  obtain ⟨ls0, h0, rfl⟩ := linPlanAppendLit_conf_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linLeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (linLePlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linLePlan_conf_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1)).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linGePlan_conf_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linLeReif_fixed_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linPlanAppendLit
      (if rb then linLePlan (linTerms coeffs.toArray is.toArray bds) b
       else linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1))
      (posBool r (!rb))).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨r0, h0, rfl⟩ := linPlanAppendLit_prunes_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linLeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (l, r0) ∈ (linLePlan (linTerms coeffs.toArray is.toArray bds) b).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linLePlan_prunes_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (l, r0) ∈ (linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1)).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linGePlan_prunes_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linNeReif_fixed_conf_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {ls : List Literal}
    (h : (linPlanAppendLit
      (if rb then linNePlan (linTerms coeffs.toArray is.toArray bds) b
         (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
       else linEqPlan (linTerms coeffs.toArray is.toArray bds) b)
      (posBool r (!rb))).conflict? = some ls) :
    Entailed p ls := by
  intro a ha hacc
  obtain ⟨ls0, h0, rfl⟩ := linPlanAppendLit_conf_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linNeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linNePlan_conf_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 := by simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linEqPlan_conf_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linNeReif_fixed_prunes_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (rb : Bool) {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linPlanAppendLit
      (if rb then linNePlan (linTerms coeffs.toArray is.toArray bds) b
         (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
       else linEqPlan (linTerms coeffs.toArray is.toArray bds) b)
      (posBool r (!rb))).prunes) :
    Entailed p reason := by
  intro a ha hacc
  obtain ⟨r0, h0, rfl⟩ := linPlanAppendLit_prunes_mem h
  obtain ⟨rb', hrb', hint, htrue, hfalse⟩ :=
    linNeReif_rel_facts p coeffs is b r view hmem hsize bds hbds hslots ha hacc
  cases rb with
  | true =>
      have h0' : (l, r0) ∈ (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linNePlan_prunes_entailed h0' hint (htrue rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩
      | false =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r false, by simp, by
            rw [eval_posBool_iff, hrb']⟩
  | false =>
      have h0' : (l, r0) ∈ (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).prunes := by
        simpa using h0
      cases rb' with
      | true =>
          exact Clause.satisfiedBy_iff.mpr ⟨posBool r true, by simp, by
            rw [eval_posBool_iff, hrb']⟩
      | false =>
          obtain ⟨l0, hl0, hsat⟩ := Clause.satisfiedBy_iff.mp
            (linEqPlan_prunes_entailed h0' hint (hfalse rfl))
          exact Clause.satisfiedBy_iff.mpr ⟨l0, List.mem_append_left _ hl0, hsat⟩

theorem linLeReifDecidePlan_conflict_none (r : Nat) (terms : List LinTerm) (b : Int) :
    (linLeReifDecidePlan r terms b).conflict? = none := by
  unfold linLeReifDecidePlan linPlanSingle linPlanEmpty
  repeat' split
  all_goals rfl

theorem linEqReifDecidePlan_conflict_none (r : Nat) (terms : List LinTerm) (b : Int) :
    (linEqReifDecidePlan r terms b).conflict? = none := by
  unfold linEqReifDecidePlan linPlanSingle linPlanEmpty
  repeat' split
  all_goals rfl

theorem linNeReifDecidePlan_conflict_none (r : Nat) (terms : List LinTerm) (b : Int) :
    (linNeReifDecidePlan r terms b).conflict? = none := by
  unfold linNeReifDecidePlan linPlanSingle linPlanEmpty
  repeat' split
  all_goals rfl

/-- Fixed and decision reification output for `linEqReif`. -/
def linEqReifOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true) : PropOut p T :=
  let terms := linTerms coeffs.toArray is.toArray bds
  let ev := fun l : Literal => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l
  let d := view.doms.getD r DomC.empty
  if _htrue : d.evalLit (posBool r true) = some true then
    linPlanOut p T
      (linPlanAppendLit (linEqPlan terms b) (posBool r false))
      (fun ls hls => linEqReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots true hls)
      (fun l reason hpr => linEqReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots true hpr)
  else if _hfalse : d.evalLit (posBool r true) = some false then
    linPlanOut p T
      (linPlanAppendLit (linNePlan terms b ev) (posBool r true))
      (fun ls hls => linEqReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots false hls)
      (fun l reason hpr => linEqReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots false hpr)
  else
    linPlanOut p T (linEqReifDecidePlan r terms b)
      (fun ls hls => by
        rw [linEqReifDecidePlan_conflict_none r terms b] at hls
        simp at hls)
      (fun l reason hpr => linEqReifDecidePlan_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots hpr)

/-- Fixed and decision reification output for `linLeReif`. -/
def linLeReifOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true) : PropOut p T :=
  let terms := linTerms coeffs.toArray is.toArray bds
  let d := view.doms.getD r DomC.empty
  if _htrue : d.evalLit (posBool r true) = some true then
    linPlanOut p T
      (linPlanAppendLit (linLePlan terms b) (posBool r false))
      (fun ls hls => linLeReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots true hls)
      (fun l reason hpr => linLeReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots true hpr)
  else if _hfalse : d.evalLit (posBool r true) = some false then
    linPlanOut p T
      (linPlanAppendLit (linGePlan terms (b + 1)) (posBool r true))
      (fun ls hls => linLeReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots false hls)
      (fun l reason hpr => linLeReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots false hpr)
  else
    linPlanOut p T (linLeReifDecidePlan r terms b)
      (fun ls hls => by
        rw [linLeReifDecidePlan_conflict_none r terms b] at hls
        simp at hls)
      (fun l reason hpr => linLeReifDecidePlan_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots hpr)

/-- Fixed and decision reification output for `linNeReif`. -/
def linNeReifOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true) : PropOut p T :=
  let terms := linTerms coeffs.toArray is.toArray bds
  let ev := fun l : Literal => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l
  let d := view.doms.getD r DomC.empty
  if _htrue : d.evalLit (posBool r true) = some true then
    linPlanOut p T
      (linPlanAppendLit (linNePlan terms b ev) (posBool r false))
      (fun ls hls => linNeReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots true hls)
      (fun l reason hpr => linNeReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots true hpr)
  else if _hfalse : d.evalLit (posBool r true) = some false then
    linPlanOut p T
      (linPlanAppendLit (linEqPlan terms b) (posBool r true))
      (fun ls hls => linNeReif_fixed_conf_entailed p coeffs is b r view hmem hsize bds hbds hslots false hls)
      (fun l reason hpr => linNeReif_fixed_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots false hpr)
  else
    linPlanOut p T (linNeReifDecidePlan r terms b)
      (fun ls hls => by
        rw [linNeReifDecidePlan_conflict_none r terms b] at hls
        simp at hls)
      (fun l reason hpr => linNeReifDecidePlan_prunes_entailed p coeffs is b r view hmem hsize bds hbds hslots hpr)


end LeanFzn.Engine

/-
Purpose: R1d frame/trail synchronisation, provenance part. The synchronisation
definitions and proofs (`syncOne`, `syncSlot`, `syncAll`, ...) live in
`ExplainedPropagation.lean` (the explained closure uses them); this module
adds the learned-clause provenance transfer along trail extensions.
Dependencies: ExplainedPropagation (`narrowState`, `explainedStep_narrow_*`),
LcgAnalyzer (`impliesP`).
-/
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.Propagation.DomExplained
open LeanFzn.Semantics LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

variable {leaf : Assignment → Bool}

/-! ## Trail-extension transfer -/

theorem clauseProvenance_mono {bs bs' : BranchState leaf} {c : Clause}
    (hsub : ∀ e ∈ bs.trail, e ∈ bs'.trail) (h : ClauseProvenance leaf bs c) :
    ClauseProvenance leaf bs' c := by
  obtain ⟨p, hp, hm, hr⟩ := h
  refine ⟨p, hp, hm, fun q hq hne => ?_⟩
  obtain ⟨e, he, heq⟩ := List.mem_map.mp (hr q hq hne)
  exact List.mem_map.mpr ⟨e, hsub e he, heq⟩

theorem learnedProvenance_mono {bs bs' : BranchState leaf}
    (hsub : ∀ e ∈ bs.trail, e ∈ bs'.trail) (hl : bs'.learned = bs.learned)
    (h : LearnedProvenance leaf bs) : LearnedProvenance leaf bs' :=
  fun c hc => clauseProvenance_mono hsub (h c (hl ▸ hc))


/-! ## The shape of the pushed entries -/

/-- Every entry of the pushed segment is a reasoned entry at the branch level
whose literal is the normalization of the pushed literal and whose reason
clause is the pushed literal followed by negations of earlier trail
literals (the domain explanation). -/
def SyncEntry (lit : Literal) (lvl : Nat) (tr : List TrailEntry) (e : TrailEntry) :
    Prop :=
  ∃ ex : Clause, e = ⟨lit.norm, lvl, some ⟨lit.norm :: ex⟩⟩ ∧
    ∀ q ∈ ex, ∃ t ∈ tr, q = t.literal.negate

theorem syncOne_entries (orig : List Domain) (bs : BranchState leaf)
    (lit : Literal) :
    ∃ ex, (syncOne orig bs lit).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, SyncEntry lit bs.level bs.trail e := by
  unfold syncOne
  cases h : syncClause orig bs lit with
  | none => exact ⟨[], by simp, by simp⟩
  | some c =>
    obtain ⟨d, ex, -, -, -, -, hx, rfl⟩ := syncClause_spec h
    refine ⟨[⟨lit.norm, bs.level, some ⟨lit.norm :: ex⟩⟩], rfl, ?_⟩
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨ex, rfl, (syncExplain_spec hx).1⟩

/-- Entries pushed by `syncSlot`: candidate literals, level, explanation. -/
theorem syncSlot_entries (orig : List Domain) (bs : BranchState leaf) (s : Nat) :
    ∃ ex, (syncSlot orig bs s).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, ∃ lit ∈ syncCands orig bs.frame s,
        SyncEntry lit bs.level (syncSlot orig bs s).trail e := by
  -- track the invariant along the fold, with the trail only growing
  unfold syncSlot
  have key : ∀ (cs : List Literal), (∀ l ∈ cs, l ∈ syncCands orig bs.frame s) →
      ∀ (b : BranchState leaf), b.level = bs.level →
      ∃ ex, (cs.foldl (syncOne orig) b).trail = b.trail ++ ex ∧
        ∀ e ∈ ex, ∃ lit ∈ syncCands orig bs.frame s,
          SyncEntry lit bs.level (cs.foldl (syncOne orig) b).trail e := by
    intro cs
    induction cs with
    | nil => intro _ b _; exact ⟨[], by simp, by simp⟩
    | cons l rest ih =>
      intro hcs b hb
      obtain ⟨ex1, h1, h1'⟩ := syncOne_entries orig b l
      obtain ⟨ex2, h2, h2'⟩ := ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
        (syncOne orig b l) (by simp [hb])
      refine ⟨ex1 ++ ex2, ?_, ?_⟩
      · simp only [List.foldl_cons]
        rw [h2, h1, List.append_assoc]
      · intro e he
        simp only [List.foldl_cons]
        rcases List.mem_append.mp he with he | he
        · refine ⟨l, hcs l (List.mem_cons_self), ?_⟩
          obtain ⟨q, hq, hq'⟩ := h1' e he
          refine ⟨q, by rw [hq, hb], fun x hx => ?_⟩
          obtain ⟨t, ht, htq⟩ := hq' x hx
          refine ⟨t, ?_, htq⟩
          rw [h2, h1]
          exact List.mem_append_left _ (List.mem_append_left _ ht)
        · obtain ⟨lit, hlit, hq⟩ := h2' e he
          exact ⟨lit, hlit, hq⟩
  exact key _ (fun l hl => hl) bs rfl


theorem syncAll_entries (orig : List Domain) (bs : BranchState leaf) :
    ∃ ex, (syncAll orig bs).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, ∃ i, i < bs.frame.doms.length ∧
        ∃ lit ∈ syncCands orig bs.frame i,
          SyncEntry lit bs.level (syncAll orig bs).trail e := by
  unfold syncAll
  have key : ∀ (is : List Nat), (∀ i ∈ is, i < bs.frame.doms.length) →
      ∀ (b : BranchState leaf), b.level = bs.level → b.frame = bs.frame →
      ∃ ex, (is.foldl (fun b i => syncSlot orig b i) b).trail
          = b.trail ++ ex ∧
        ∀ e ∈ ex, ∃ i, i < bs.frame.doms.length ∧
          ∃ lit ∈ syncCands orig bs.frame i,
          SyncEntry lit bs.level
            (is.foldl (fun b i => syncSlot orig b i) b).trail e := by
    intro is
    induction is with
    | nil => intro _ b _ _; exact ⟨[], by simp, by simp⟩
    | cons i rest ih =>
      intro hcs b hb hf
      obtain ⟨ex1, h1, h1'⟩ := syncSlot_entries orig b i
      obtain ⟨ex2, h2, h2'⟩ := ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
        (syncSlot orig b i) (by simp [hb]) (by simp [hf])
      refine ⟨ex1 ++ ex2, ?_, ?_⟩
      · simp only [List.foldl_cons]
        rw [h2, h1, List.append_assoc]
      · intro e he
        simp only [List.foldl_cons]
        rcases List.mem_append.mp he with he | he
        · obtain ⟨lit, hlit, q, hq, hq'⟩ := h1' e he
          refine ⟨i, hcs i List.mem_cons_self, lit, by rw [hf] at hlit; exact hlit, ?_⟩
          refine ⟨q, by rw [hq, hb], fun x hx => ?_⟩
          obtain ⟨t, ht, htq⟩ := hq' x hx
          refine ⟨t, ?_, htq⟩
          have ht' : t ∈ b.trail ++ ex1 := h1 ▸ ht
          rw [h2, h1]
          exact List.mem_append_left _ ht'
        · exact h2' e he
  exact key _ (fun i hi => List.mem_range.mp hi) bs rfl rfl


/-! ## Generic trail-property transfer -/

/-- Inversion of candidate membership. -/
theorem syncCands_cases {orig : List Domain} {f : BranchFrame} {s : Nat}
    {lit : Literal} (h : lit ∈ syncCands orig f s) :
    s < orig.length ∧ ∃ d, f.doms[s]? = some d ∧
      ((∃ lo, ((Dom.enum d).filterMap Value.intView).min? = some lo ∧
          lo ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = negLe s (lo - 1)) ∨
       (∃ hi, ((Dom.enum d).filterMap Value.intView).max? = some hi ∧
          hi ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = posLe s hi) ∨
       (∃ i, Dom.enum d = [Value.int i] ∧
          i ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = negNe s i) ∨
       (∃ b, Dom.enum d = [Value.bool b] ∧ lit = posBool s b) ∨
       (∃ lo hi h, ((Dom.enum d).filterMap Value.intView).min? = some lo ∧
          ((Dom.enum d).filterMap Value.intView).max? = some hi ∧
          h ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = posNe s h)) := by
  unfold syncCands at h
  by_cases hc : s < orig.length
  · rw [if_pos hc] at h
    refine ⟨hc, ?_⟩
    cases hd : f.doms[s]? with
    | none => rw [hd] at h; simp at h
    | some d =>
      rw [hd] at h
      refine ⟨d, rfl, ?_⟩
      simp only [List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · left
        cases hm : ((Dom.enum d).filterMap Value.intView).min? with
        | none => simp [hm] at h
        | some lo =>
          simp only [hm] at h
          by_cases hl : lo ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
          · rw [if_pos hl] at h
            simp only [List.mem_singleton] at h
            exact ⟨lo, rfl, hl, h⟩
          · rw [if_neg hl] at h; simp at h
      · right; left
        cases hm : ((Dom.enum d).filterMap Value.intView).max? with
        | none => simp [hm] at h
        | some hi =>
          simp only [hm] at h
          by_cases hl : hi ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
          · rw [if_pos hl] at h
            simp only [List.mem_singleton] at h
            exact ⟨hi, rfl, hl, h⟩
          · rw [if_neg hl] at h; simp at h
      · right; right
        cases hde : Dom.enum d with
        | nil => simp [hde] at h
        | cons v rest =>
          cases rest with
          | nil =>
            cases v with
            | int i =>
              simp only [hde] at h
              by_cases hv : i ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
              · rw [if_pos hv] at h
                simp only [valueLiteral, Option.toList_some, List.mem_singleton] at h
                exact Or.inl ⟨i, rfl, hv, h⟩
              · rw [if_neg hv] at h; simp at h
            | bool b =>
              simp only [hde, valueLiteral, Option.toList_some,
                List.mem_singleton] at h
              exact Or.inr (Or.inl ⟨b, rfl, h⟩)
            | setOfInt _ => simp [hde] at h
            | array _ => simp [hde] at h
          | cons w rest => simp [hde] at h
      · right; right; right; right
        cases hm : ((Dom.enum d).filterMap Value.intView).min? with
        | none => simp [hm] at h
        | some lo =>
          cases hM : ((Dom.enum d).filterMap Value.intView).max? with
          | none => simp [hm, hM] at h
          | some hi =>
            simp only [hm, hM, List.mem_map] at h
            obtain ⟨h0, hh0, rfl⟩ := h
            have := List.mem_eraseDups.mp hh0
            exact ⟨lo, hi, h0, rfl, rfl, (List.mem_filter.mp this).1, rfl⟩
  · rw [if_neg hc] at h; simp at h

theorem syncCands_slot {orig : List Domain} {f : BranchFrame} {s : Nat} :
    ∀ lit ∈ syncCands orig f s, lit.atom.slot = s := by
  intro lit hlit
  obtain ⟨-, d, -, h⟩ := syncCands_cases hlit
  rcases h with ⟨lo, -, -, rfl⟩ | ⟨hi, -, -, rfl⟩ | ⟨i, -, -, rfl⟩ | ⟨b, -, rfl⟩ |
    ⟨lo, hi, h, -, -, -, rfl⟩ <;> rfl

/-- A literal-level property of the pushed literals lifts to the trail. -/
theorem syncSlot_trail_prop (orig : List Domain) (bs : BranchState leaf) (s : Nat)
    {Q : Literal → Prop} (hc : ∀ lit ∈ syncCands orig bs.frame s, Q lit.norm)
    (hbs : ∀ e ∈ bs.trail, Q e.literal) :
    ∀ e ∈ (syncSlot orig bs s).trail, Q e.literal := by
  obtain ⟨ex, hex, hent⟩ := syncSlot_entries orig bs s
  intro e he
  rw [hex] at he
  rcases List.mem_append.mp he with he | he
  · exact hbs e he
  · obtain ⟨lit, hlit, q, rfl, -⟩ := hent e he
    exact hc lit hlit

theorem syncAll_trail_prop (orig : List Domain) (bs : BranchState leaf)
    {Q : Literal → Prop}
    (hc : ∀ i, i < bs.frame.doms.length →
      ∀ lit ∈ syncCands orig bs.frame i, Q lit.norm)
    (hbs : ∀ e ∈ bs.trail, Q e.literal) :
    ∀ e ∈ (syncAll orig bs).trail, Q e.literal := by
  obtain ⟨ex, hex, hent⟩ := syncAll_entries orig bs
  intro e he
  rw [hex] at he
  rcases List.mem_append.mp he with he | he
  · exact hbs e he
  · obtain ⟨i, hi, lit, hlit, q, rfl, -⟩ := hent e he
    exact hc i hi lit hlit

end LeanFzn.Solver.Propagation

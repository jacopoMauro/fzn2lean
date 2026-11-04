/-
Purpose: Evaluate clauses against finite-domain boxes for conflict and unit propagation.

  Two representations (M2/M3): the sparse scheduled `BranchFrame` (shared
  names: `literalImpossible`/`clauseRemaining` read `f.doms` at absolute
  slots) and the positional `PrefixFrame` the chronological/reference cone
  keeps (`prefixLiteralImpossible`/`prefixClauseRemaining`).

Dependencies: FrameFilter connects box coverage, domain membership and literal truth;
Encoding supplies slot-indexed literal syntax. DAG: FrameFilter -> ClausePropagation -> pruned search.
-/
import LeanFzn.Solver.Propagation.FrameFilter
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Sparse clause evaluation (scheduled cone) -/

/-- A literal is impossible when every value in its box slot falsifies it. -/
def literalImpossible (f : BranchFrame) (l : Literal) : Bool :=
  ((Frame.domains f).getD l.atom.slot Dom.empty).enum.all fun v => !l.valueHolds v

/-- Literals whose truth has not been excluded by the current box. -/
def clauseRemaining (f : BranchFrame) (c : Clause) : Clause :=
  c.filter fun l => !literalImpossible f l

theorem literalImpossible_false {f : BranchFrame} {a : Assignment} {l : Literal}
    (hc : FrameCovers f a) (he : l.eval a = some true) :
    literalImpossible f l = false := by
  have hf := hc.fits
  have hget : ∃ v, a[l.atom.slot]? = some v := by
    cases hg : a[l.atom.slot]? with
    | some v => exact ⟨v, rfl⟩
    | none =>
      cases l with
      | mk atom positive =>
        cases atom <;> simp only [Atom.slot] at hg
        all_goals simp [Literal.eval, Atom.eval, slotInt, hg] at he
  obtain ⟨v, hv⟩ := hget
  have hm := hf.2 l.atom.slot v hv
  have hh := (valueHolds_read hv).mpr he
  cases hb : literalImpossible f l with
  | false => rfl
  | true =>
    have hb' : ((Frame.domains f).getD l.atom.slot Dom.empty).enum.all
        (fun v => !l.valueHolds v) = true := by
      simpa [literalImpossible] using hb
    have hm' : v ∈ ((Frame.domains f).getD l.atom.slot Dom.empty).enum := by
      rw [← domElems_eq_enum, ← DomainLike.mem_iff]
      exact hm
    have ha := List.all_eq_true.mp hb' v hm'
    simp [hh] at ha

theorem clauseRemaining_true {f : BranchFrame} {a : Assignment} {c : Clause}
    (hc : FrameCovers f a) (hs : c.SatisfiedBy a) :
    ∃ l ∈ clauseRemaining f c, l.eval a = some true := by
  obtain ⟨l, hl, he⟩ := hs
  refine ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, he⟩
  simp [literalImpossible_false hc he]

theorem clauseRemaining_empty_excludes {f : BranchFrame} {a : Assignment} {c : Clause}
    (hc : FrameCovers f a) (hempty : clauseRemaining f c = []) :
    ¬ c.SatisfiedBy a := by
  intro hs
  obtain ⟨l, hl, _⟩ := clauseRemaining_true hc hs
  simp [hempty] at hl

theorem clauseRemaining_singleton_implies {f : BranchFrame} {a : Assignment}
    {c : Clause} {l : Literal}
    (hc : FrameCovers f a) (hs : c.SatisfiedBy a)
    (hunit : clauseRemaining f c = [l]) : l.eval a = some true := by
  obtain ⟨q, hq, he⟩ := clauseRemaining_true hc hs
  have hql : q = l := by simpa [hunit] using hq
  simpa [hql] using he

/-! ## Positional clause evaluation (chronological/reference cone) -/

/-- Positional variant: a literal is impossible when every value of the full
box at its slot falsifies it. -/
def prefixLiteralImpossible (f : PrefixFrame) (l : Literal) : Bool :=
  ((PrefixFrame.domains f).getD l.atom.slot Dom.empty).enum.all fun v => !l.valueHolds v

/-- Positional variant of `clauseRemaining`. -/
def prefixClauseRemaining (f : PrefixFrame) (c : Clause) : Clause :=
  c.filter fun l => !prefixLiteralImpossible f l

theorem prefixLiteralImpossible_false {f : PrefixFrame} {a : Assignment}
    {l : Literal} (hc : PrefixCovers f a) (he : l.eval a = some true) :
    prefixLiteralImpossible f l = false := by
  have hf := PrefixCovers.fits hc
  have hget : ∃ v, a[l.atom.slot]? = some v := by
    cases hg : a[l.atom.slot]? with
    | some v => exact ⟨v, rfl⟩
    | none =>
      cases l with
      | mk atom positive =>
        cases atom <;> simp only [Atom.slot] at hg
        all_goals simp [Literal.eval, Atom.eval, slotInt, hg] at he
  obtain ⟨v, hv⟩ := hget
  have hm := hf.2 l.atom.slot v hv
  have hh := (valueHolds_read hv).mpr he
  cases hb : prefixLiteralImpossible f l with
  | false => rfl
  | true =>
    have hb' : ((PrefixFrame.domains f).getD l.atom.slot Dom.empty).enum.all
        (fun v => !l.valueHolds v) = true := by
      simpa [prefixLiteralImpossible] using hb
    have hm' : v ∈ ((PrefixFrame.domains f).getD l.atom.slot Dom.empty).enum := by
      rw [← domElems_eq_enum, ← DomainLike.mem_iff]
      exact hm
    have ha := List.all_eq_true.mp hb' v hm'
    simp [hh] at ha

theorem prefixClauseRemaining_true {f : PrefixFrame} {a : Assignment} {c : Clause}
    (hc : PrefixCovers f a) (hs : c.SatisfiedBy a) :
    ∃ l ∈ prefixClauseRemaining f c, l.eval a = some true := by
  obtain ⟨l, hl, he⟩ := hs
  refine ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, he⟩
  simp [prefixLiteralImpossible_false hc he]

theorem prefixClauseRemaining_empty_excludes {f : PrefixFrame} {a : Assignment}
    {c : Clause} (hc : PrefixCovers f a) (hempty : prefixClauseRemaining f c = []) :
    ¬ c.SatisfiedBy a := by
  intro hs
  obtain ⟨l, hl, _⟩ := prefixClauseRemaining_true hc hs
  simp [hempty] at hl

theorem prefixClauseRemaining_singleton_implies {f : PrefixFrame} {a : Assignment}
    {c : Clause} {l : Literal}
    (hc : PrefixCovers f a) (hs : c.SatisfiedBy a)
    (hunit : prefixClauseRemaining f c = [l]) : l.eval a = some true := by
  obtain ⟨q, hq, he⟩ := prefixClauseRemaining_true hc hs
  have hql : q = l := by simpa [hunit] using hq
  simpa [hql] using he

end LeanFzn.Solver.Propagation

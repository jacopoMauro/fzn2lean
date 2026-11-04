import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The linear-constraint propagators (bounds propagation) -/

/-- The linear combination `Σ cᵢ·xᵢ`, appending no terms past the
    shorter list (lengths agree whenever the encodings below use it). -/
private def linSum : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | c :: cs, x :: xs => c * x + linSum cs xs

/-- Term `c·x`'s contribution to the dot product's minimum over
    `x ∈ [lo, hi]`. -/
private def termMin (c : Int) (lo hi : Int) : Int :=
  if 0 ≤ c then c * lo else c * hi

/-- Term `c·x`'s contribution to the dot product's maximum over
    `x ∈ [lo, hi]`. -/
private def termMax (c : Int) (lo hi : Int) : Int :=
  if 0 ≤ c then c * hi else c * lo

/-- The dot product's minimum over the listed domains. -/
private def linTotalMin : List Int → List (Int × Int) → Int
  | c :: cs, (lo, hi) :: bds => termMin c lo hi + linTotalMin cs bds
  | _, _ => 0

/-- The dot product's maximum over the listed domains. -/
private def linTotalMax : List Int → List (Int × Int) → Int
  | c :: cs, (lo, hi) :: bds => termMax c lo hi + linTotalMax cs bds
  | _, _ => 0

/-- Extract the integer extrema of each listed slot, or `none` when
    some listed slot lacks integers. -/
private def linExtract (is : List Nat) (doms : List (List Value)) :
    Option (List (Int × Int)) :=
  match is with
  | [] => some []
  | idx :: rest =>
      match domMin (getSlot doms idx), domMax (getSlot doms idx) with
      | some lo, some hi => (linExtract rest doms).map (fun bds => (lo, hi) :: bds)
      | _, _ => none

/-- `linEq`'s feasibility interval for a single term: values `p` of the
    term whose other terms' contributions can close the equality. -/
private def linNarrowEq (c : Int) (b otherMin otherMax : Int) (d : List Value) :
    List Value :=
  d.filter (fun v =>
    match v with
    | .int p => decide (b - otherMax ≤ c * p && c * p ≤ b - otherMin)
    | _ => false)

/-- `linLe`'s feasibility condition for a single term: values `p` whose
    term's contribution, together with the other terms at their
    minimum, fits under `b`. -/
private def linNarrowLe (c : Int) (b otherMin : Int) (d : List Value) :
    List Value :=
  d.filter (fun v =>
    match v with
    | .int p => decide (c * p ≤ b - otherMin)
    | _ => false)

/-- Narrow every listed slot's domain to the values that can
    participate in a feasible assignment, computing each other-term
    bound from the pre-extracted extrema; `contradiction` as soon as a
    listed slot empties (or the terms mismatch). -/
private def linNarrowAll (cs : List Int) (is : List Nat) (bds : List (Int × Int))
    (totalMin totalMax : Int) (eq : Bool) (b : Int)
    (doms : List (List Value)) : PropResult :=
  match cs, is, bds with
  | [], [], [] => .narrowed doms
  | c :: cs', idx :: is', (lo, hi) :: bds' =>
      -- the other terms' extrema: the whole's totals minus this term's extrema
      let cLo := termMin c lo hi
      let cHi := termMax c lo hi
      let otherMin := totalMin - cLo
      let otherMax := totalMax - cHi
      let d' := if eq then
          linNarrowEq c b otherMin otherMax (getSlot doms idx)
        else
          linNarrowLe c b otherMin (getSlot doms idx)
      if d'.isEmpty then .contradiction
      else linNarrowAll cs' is' bds' totalMin totalMax eq b (setSlot doms idx d')
  | _, _, _ => .contradiction

/-- **The `int_lin_eq` propagator** (`int_lin_eq` style, canonical
    form): bounds propagation for `Σ cᵢ·xᵢ = b`.  Each listed slot
    keeps the values `p` whose term's contribution can still be offset
    by the other terms (their contributions and the target's extrema);
    `contradiction` when some listed slot has no integers, some
    narrowed slot empties, or the terms mismatch. -/
def propLinEq (coeffs : List Int) (is : List Nat) (b : Int)
    (doms : List (List Value)) : PropResult :=
  if coeffs.length = is.length then
    match linExtract is doms with
    | none => .contradiction
    | some bds =>
        linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
          true b doms
  else
    -- a mismatched-shape linear constraint has no satisfying assignment
    -- (the dot product needs equal lengths), so contradiction is sound
    .contradiction

/-- **The `int_lin_le` propagator** (`int_lin_le` style, canonical
    form): bounds propagation for `Σ cᵢ·xᵢ ≤ b`.  Each listed slot
    keeps the values `p` whose term's contribution, together with the
    other terms at their minimum, stays under `b`; `contradiction`
    when some listed slot has no integers, some narrowed slot empties,
    or the terms mismatch. -/
def propLinLe (coeffs : List Int) (is : List Nat) (b : Int)
    (doms : List (List Value)) : PropResult :=
  if coeffs.length = is.length then
    match linExtract is doms with
    | none => .contradiction
    | some bds =>
        linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
          false b doms
  else
    -- a mismatched-shape linear constraint has no satisfying assignment
    -- (the dot product needs equal lengths), so contradiction is sound
    .contradiction


/-! ## The linear propagators' preservation theorems -/

/-- A term's contribution is bounded by its extrema. -/
private theorem term_bound (c lo hi x : Int) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    termMin c lo hi ≤ c * x ∧ c * x ≤ termMax c lo hi := by
  unfold termMin termMax
  by_cases hc : 0 ≤ c
  · rw [if_pos hc, if_pos hc]
    have hw1 : 0 ≤ x - lo := by omega
    have hw2 : 0 ≤ hi - x := by omega
    have h1 : 0 ≤ c * (x - lo) := Int.mul_nonneg hc hw1
    have h2 : 0 ≤ c * (hi - x) := Int.mul_nonneg hc hw2
    rw [Int.mul_sub] at h1
    rw [Int.mul_sub] at h2
    omega
  · rw [if_neg hc, if_neg hc]
    have hn : 0 ≤ -c := by omega
    have hw1 : 0 ≤ hi - x := by omega
    have hw2 : 0 ≤ x - lo := by omega
    have h1 : 0 ≤ -c * (hi - x) := Int.mul_nonneg hn hw1
    have h2 : 0 ≤ -c * (x - lo) := Int.mul_nonneg hn hw2
    have e1 : -c * (hi - x) = c * x - c * hi := by
      have h1' : c * (hi - x) = c * hi - c * x := Int.mul_sub c hi x
      have h2' : -c * (hi - x) = -(c * (hi - x)) := (Int.neg_mul_eq_neg_mul c (hi - x)).symm
      rw [h2', h1']
      omega
    have e2 : -c * (x - lo) = c * lo - c * x := by
      have h1' : c * (x - lo) = c * x - c * lo := Int.mul_sub c x lo
      have h2' : -c * (x - lo) = -(c * (x - lo)) := (Int.neg_mul_eq_neg_mul c (x - lo)).symm
      rw [h2', h1']
      omega
    rw [e1] at h1
    rw [e2] at h2
    omega

/-- The `dotProduct`-level sum of a satisfying assignment's term
    contributions, decomposed at the head term. -/
private theorem dotProduct_cons_eq (a x : Int) (as_ xs : List Value) (s : Int)
    (h : dotProduct (.int a :: as_) (.int x :: xs) = some s) :
    ∃ s', dotProduct as_ xs = some s' ∧ s = a * x + s' := by
  simp only [dotProduct] at h
  cases h' : dotProduct as_ xs with
  | none => rw [h'] at h; exact absurd h (by simp)
  | some s' =>
      rw [h'] at h
      have hs : s = a * x + s' := (Option.some.inj h).symm
      exact ⟨s', rfl, hs⟩



/-! ## The linear propagators' preservation theorems

Both theorems share one induction over the term triple
`(coeffs, is, bds)`.  The proof spine is the same as the arithmetic
propagators': an assignment of the input domains (spec
`allAssigns_spec`) whose listed values satisfy the constraint is
rebuilt as an assignment of the narrowed domains
(`allAssigns_intro`); the per-term filter passes because the other
terms' contribution to a satisfying sum is bounded by their
extrema sums (`totalMin`/`totalMax` minus this term's extrema). -/

/-- The value-level dot-product sum (the `dotProduct` fold, made
    total). -/
private def dotSum : List Value → List Value → Int
  | .int a :: as_, .int x :: xs => a * x + dotSum as_ xs
  | _, _ => 0

/-- A successful `dotProduct` computes `dotSum`. -/
private theorem dotProduct_eq_sum :
    ∀ (cs xs : List Value) (s : Int),
    dotProduct cs xs = some s → s = dotSum cs xs := by
  intro cs
  induction cs with
  | nil =>
      intro xs s h
      cases xs with
      | nil =>
          have hs : s = 0 := (Option.some.inj h).symm
          subst hs
          rfl
      | cons x xs' => exact absurd h (by simp [dotProduct])
  | cons c cs' ih =>
      intro xs s h
      cases c with
      | int a =>
          cases xs with
          | nil => exact absurd h (by simp [dotProduct])
          | cons x xs'' =>
              cases x with
              | int xv =>
                  simp only [dotProduct] at h
                  cases hrest : dotProduct cs' xs'' with
                  | none => rw [hrest] at h; exact absurd h (by simp)
                  | some s' =>
                      rw [hrest] at h
                      have hs : s = a * xv + s' := (Option.some.inj h).symm
                      rw [hs]
                      have := ih xs'' s' hrest
                      rw [this]
                      rfl
              | _ => exact absurd h (by simp [dotProduct])
      | _ => exact absurd h (by simp [dotProduct])

/-- The head decomposition of `dotSum` on coefficient/value conses. -/
private theorem dotSum_cons (a x : Int) (as_ xs : List Value) :
    dotSum (.int a :: as_) (.int x :: xs) = a * x + dotSum as_ xs := rfl

/-- The extrema-sum bounds on the dot sum, by induction on the
    term triple: when every listed value `x` sits in its extracted
    bounds `(lo, hi)` (the `hbds` conjunct, pointwise), the dot sum of
    the coefficients against the values lies between the term-min and
    term-max sums. -/
private theorem dotSum_bounds :
    ∀ (cs : List Int) (xs : List Value) (bds : List (Int × Int)),
    cs.length = xs.length → xs.length = bds.length →
    (∀ (j : Nat), j < xs.length →
        ∃ p, xs[j]! = LeanFzn.Semantics.Value.int p ∧
          bds[j]!.1 ≤ p ∧ p ≤ bds[j]!.2) →
    linTotalMin cs bds ≤ dotSum (intVals cs) xs ∧
      dotSum (intVals cs) xs ≤ linTotalMax cs bds := by
  intro cs
  induction cs with
  | nil =>
      intro xs bds hlen1 hlen2 _
      cases xs with
      | nil =>
          cases bds with
          | nil =>
              -- dotSum [] [] = 0; linTotalMin [] [] = 0; linTotalMax [] [] = 0
              show 0 ≤ 0 ∧ 0 ≤ 0
              omega
          | cons bd bds' =>
              have h := hlen2
              simp only [List.length_nil] at h
              exact absurd h (by simp)
      | cons x xs' =>
          have h := hlen1
          simp only [List.length_nil] at h
          exact absurd h (by simp)
  | cons c cs' ih =>
      intro xs bds hlen1 hlen2 hbds
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen1
          exact absurd hlen1 (by omega)
      | cons x xs'' =>
          cases bds with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen2
              exact absurd hlen2 (by omega)
          | cons bd bds'' =>
              obtain ⟨p, hx, hlo, hhi⟩ := hbds 0 (Nat.succ_pos xs''.length)
              subst hx
              obtain ⟨hllo, hlhi⟩ := ih xs'' bds''
                (by simp only [List.length_cons] at hlen1; omega)
                (by simp only [List.length_cons] at hlen2; omega)
                (by intro j hj
                    exact hbds (j + 1) (by simp only [List.length_cons]; omega))
              -- the head term's bounds within the extracted interval
              obtain ⟨htlo, hthi⟩ := term_bound c bd.1 bd.2 p hlo hhi
              -- the cons sums
              have hsum : dotSum (intVals (c :: cs')) (LeanFzn.Semantics.Value.int p :: xs'')
                  = c * p + dotSum (intVals cs') xs'' := rfl
              have hmin : linTotalMin (c :: cs') (bd :: bds'')
                  = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
              have hmax : linTotalMax (c :: cs') (bd :: bds'')
                  = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
              show termMin c bd.1 bd.2 + linTotalMin cs' bds''
                  ≤ c * p + dotSum (intVals cs') xs'' ∧
                c * p + dotSum (intVals cs') xs''
                  ≤ termMax c bd.1 bd.2 + linTotalMax cs' bds''
              constructor <;> omega


/-! ### The narrowing-soundness induction -/

/-- **The other terms' bound** (the filter-soundness core): for the
    aligned term/value/bound lists, position `k`'s value `p` lies in
    its extracted interval, and the sum of the terms at positions ≠ k
    is bounded by the total extrema minus position `k`'s term
    extrema. -/
private theorem others_bound :
    ∀ (cs : List Int) (xs : List Value) (bds : List (Int × Int)) (k : Nat),
    cs.length = xs.length → xs.length = bds.length →
    (∀ (j : Nat), j < xs.length →
        ∃ p, xs[j]! = LeanFzn.Semantics.Value.int p ∧
          bds[j]!.1 ≤ p ∧ p ≤ bds[j]!.2) →
    k < xs.length →
    ∃ ck p, cs[k]! = ck ∧ xs[k]! = LeanFzn.Semantics.Value.int p ∧
      bds[k]!.1 ≤ p ∧ p ≤ bds[k]!.2 ∧
      linTotalMin cs bds - termMin ck bds[k]!.1 bds[k]!.2
        ≤ dotSum (intVals cs) xs - ck * p ∧
      dotSum (intVals cs) xs - ck * p
        ≤ linTotalMax cs bds - termMax ck bds[k]!.1 bds[k]!.2 := by
  intro cs
  induction cs with
  | nil =>
      intro xs bds k hlen1 hlen2 _ hk
      cases xs with
      | nil =>
          simp only [List.length_nil] at hk
          exact absurd hk (by omega)
      | cons _ _ =>
          simp only [List.length_nil] at hlen1
          omega
  | cons c cs' ih =>
      intro xs bds k hlen1 hlen2 hcov hk
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen1
          omega
      | cons x xs'' =>
          cases bds with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen2
              omega
          | cons bd bds'' =>
              obtain ⟨p, hx, hlo, hhi⟩ := hcov 0 (Nat.succ_pos xs''.length)
              subst hx
              cases k with
              | zero =>
                  -- head position: the tail's bounds via dotSum_bounds
                  obtain ⟨hllo, hlhi⟩ := dotSum_bounds cs' xs'' bds''
                    (by simp only [List.length_cons] at hlen1; omega)
                    (by simp only [List.length_cons] at hlen2; omega)
                    (by intro j hj
                        exact hcov (j + 1) (by simp only [List.length_cons]; omega))
                  refine ⟨c, p, rfl, rfl, hlo, hhi, ?_, ?_⟩
                  · show linTotalMin (c :: cs') (bd :: bds'') - termMin c bd.1 bd.2
                      ≤ c * p + dotSum (intVals cs') xs'' - c * p
                    have h1 : linTotalMin (c :: cs') (bd :: bds'')
                        = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
                    rw [h1]
                    show termMin c bd.1 bd.2 + linTotalMin cs' bds'' - termMin c bd.1 bd.2
                      ≤ c * p + dotSum (intVals cs') xs'' - c * p
                    omega
                  · show c * p + dotSum (intVals cs') xs'' - c * p
                      ≤ linTotalMax (c :: cs') (bd :: bds'') - termMax c bd.1 bd.2
                    have h2 : linTotalMax (c :: cs') (bd :: bds'')
                        = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
                    rw [h2]
                    show c * p + dotSum (intVals cs') xs'' - c * p
                      ≤ termMax c bd.1 bd.2 + linTotalMax cs' bds'' - termMax c bd.1 bd.2
                    omega
              | succ kk =>
                  -- tail position: recurse, then add the head's bounds
                  obtain ⟨ck, p', hck, hxp, hlo', hhi', hlo2, hhi2⟩ :=
                    ih xs'' bds'' kk
                      (by simp only [List.length_cons] at hlen1; omega)
                      (by simp only [List.length_cons] at hlen2; omega)
                      (by intro j hj
                          exact hcov (j + 1) (by simp only [List.length_cons]; omega))
                      (by simp only [List.length_cons] at hk; omega)
                  obtain ⟨htlo, hthi⟩ := term_bound c bd.1 bd.2 p hlo hhi
                  -- the goal indexes the cons lists at kk+1; the IH gives the tails
                  have hgetk : (c :: cs')[kk + 1]! = cs'[kk]! := rfl
                  have hgetx : (LeanFzn.Semantics.Value.int p :: xs'')[kk + 1]! = xs''[kk]! := rfl
                  have hgetb : (bd :: bds'')[kk + 1]! = bds''[kk]! := rfl
                  rw [hgetk, hgetx, hgetb]
                  refine ⟨ck, p', hck, hxp, hlo', hhi', ?_, ?_⟩
                  · show linTotalMin (c :: cs') (bd :: bds'')
                        - termMin ck bds''[kk]!.1 bds''[kk]!.2
                      ≤ c * p + dotSum (intVals cs') xs'' - ck * p'
                    have h1 : linTotalMin (c :: cs') (bd :: bds'')
                        = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
                    rw [h1]
                    omega
                  · show c * p + dotSum (intVals cs') xs'' - ck * p'
                      ≤ linTotalMax (c :: cs') (bd :: bds'')
                        - termMax ck bds''[kk]!.1 bds''[kk]!.2
                    have h2 : linTotalMax (c :: cs') (bd :: bds'')
                        = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
                    rw [h2]
                    omega

/-- The parameterized linear satisfaction (`linEq`'s `= b` when `eq`,
    `linLe`'s `≤ b` otherwise). -/
private def LinSat (eqv : Bool) (cs xs : List Value) (b : Int) : Prop :=
  if eqv then dotProduct cs xs = some b
  else ∃ d, dotProduct cs xs = some d ∧ d ≤ b

/-- The coverage invariant: every listed slot's assignment value is an
    integer inside the extracted bounds, and the assignment picks
    values of the (progressively narrowed) domains. -/
private def LinCover (is : List Nat) (bds : List (Int × Int))
    (doms : List (List Value)) (a : List Value) : Prop :=
  ∀ (k : Nat), k < is.length →
    a[is[k]!]! ∈ getSlot doms (is[k]!) ∧
      ∃ p, a[is[k]!]! = .int p ∧
        bds[k]!.1 ≤ p ∧ p ≤ bds[k]!.2

/-- The j-th element of a mapped list, in bounds. -/
private theorem map_getElem!_in_bounds (a : List Value) (is : List Nat) (j : Nat)
    (hj : j < is.length) :
    (is.map (fun i => a[i]!))[j]! = a[is[j]!]! := by
  have h1 : j < (is.map (fun i => a[i]!)).length := by
    simp only [List.length_map]
    omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem_map]
  have hisj : is[j]! = is[j] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [← hisj]
  cases a[is[j]!]? with
  | none => rfl
  | some v => rfl


/-- The identity propagator: narrows nothing (the sound placeholder for
    constraint kinds whose bounds-propagation preservation theorem is
    not yet proven — e.g. the linear kinds, whose filters are defined
    but whose master induction is future work). -/
def propIdSlot (doms : List (List Value)) : PropResult := .narrowed doms

/-- The identity propagator preserves every constraint. -/
theorem propIdSlot_preserves (c : DomConstraint) :
    Preserves c propIdSlot := by
  constructor
  · intro doms doms' h a ha _hsat
    have hd : doms' = doms := (PropResult.narrowed.inj h).symm
    rw [hd]
    exact ha
  · intro doms doms' h
    have hd : doms' = doms := (PropResult.narrowed.inj h).symm
    rw [hd]
    exact DomPointwiseSub.refl doms
  · intro doms h a _ha _hsat
    exact absurd h (by simp [propIdSlot])

/-- The cons-transport of the dot-sum satisfaction: a satisfying
    assignment of the whole (head-cons) triple restricts to a
    satisfying assignment of the tail against `b` minus the head
    term's actual contribution (for `eq`; for `le` the same
    subtraction gives a valid bound). -/
private theorem LinSat_cons {eq : Bool} {c p : Int} {cs : List Int}
    {xs : List Value} {b : Int}
    (hsat : LinSat eq (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b) :
    LinSat eq (intVals cs) xs (b - c * p) := by
  cases heq : eq with
  | true =>
      rw [heq] at hsat
      rw [show LinSat true (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b
          = (dotProduct (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs)
              = some b) from rfl] at hsat
      rw [show LinSat true (intVals cs) xs (b - c * p)
          = (dotProduct (intVals cs) xs = some (b - c * p)) from rfl]
      -- unfold one step of dotProduct on both sides
      rw [show intVals (c :: cs) = LeanFzn.Semantics.Value.int c :: intVals cs from rfl,
        dotProduct] at hsat
      cases hrest : dotProduct (intVals cs) xs with
      | none => rw [hrest] at hsat; exact absurd hsat (by simp)
      | some s' =>
          rw [hrest] at hsat
          have hsb : c * p + s' = b := (Option.some.inj hsat)
          rw [show b - c * p = s' from by omega]
  | false =>
      rw [heq] at hsat
      rw [show LinSat false (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b
          = (∃ d, dotProduct (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs)
              = some d ∧ d ≤ b) from rfl] at hsat
      rw [show LinSat false (intVals cs) xs (b - c * p)
          = (∃ d, dotProduct (intVals cs) xs = some d ∧ d ≤ b - c * p) from rfl]
      obtain ⟨d, hd, hle⟩ := hsat
      rw [show intVals (c :: cs) = LeanFzn.Semantics.Value.int c :: intVals cs from rfl,
        dotProduct] at hd
      cases hrest : dotProduct (intVals cs) xs with
      | none => rw [hrest] at hd; exact absurd hd (by simp)
      | some s' =>
          rw [hrest] at hd
          have hsd : c * p + s' = d := (Option.some.inj hd)
          exact ⟨s', rfl, by omega⟩

/-- The extrema sums against an empty bounds list are zero. -/
private theorem linTotal_nil_right : ∀ (l : List Int),
    linTotalMin l [] = 0 ∧ linTotalMax l [] = 0 := by
  intro l
  cases l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs => exact ⟨rfl, rfl⟩

/-- The prefix-current totals decomposition: the extrema sums of
    aligned lists split over any position. -/
private theorem linTotal_split (cs : List Int) (bds : List (Int × Int)) (k : Nat) :
    linTotalMin cs bds
      = linTotalMin (List.take k cs) (List.take k bds)
        + linTotalMin (List.drop k cs) (List.drop k bds) ∧
    linTotalMax cs bds
      = linTotalMax (List.take k cs) (List.take k bds)
        + linTotalMax (List.drop k cs) (List.drop k bds) := by
  induction cs generalizing bds k with
  | nil =>
      cases k with
      | zero => simp only [List.take, List.drop]; exact ⟨rfl, rfl⟩
      | succ k' =>
          have h1 : (List.drop (k' + 1) ([] : List Int)) = ([] : List Int) := rfl
          have h2 : (List.take (k' + 1) ([] : List Int)) = ([] : List Int) := rfl
          rw [h1, h2]
          exact ⟨rfl, rfl⟩
  | cons c cs' ih =>
      cases bds with
      | nil =>
          cases k with
          | zero => simp only [List.take, List.drop]; exact ⟨rfl, rfl⟩
          | succ k' =>
              -- all six sums are 0 by the nil-right lemma
              obtain ⟨e1, e2⟩ := linTotal_nil_right (c :: cs')
              obtain ⟨e3, e4⟩ := linTotal_nil_right (List.take (k' + 1) (c :: cs'))
              obtain ⟨e5, e6⟩ := linTotal_nil_right (List.drop (k' + 1) (c :: cs'))
              have t2 : List.take (k' + 1) ([] : List (Int × Int)) = [] := rfl
              have d2 : List.drop (k' + 1) ([] : List (Int × Int)) = [] := rfl
              rw [t2, d2]
              omega
      | cons bd bds' =>
          cases k with
          | zero =>
              simp only [List.take, List.drop]
              have hz1 : linTotalMin ([] : List Int) ([] : List (Int × Int)) = 0 := rfl
              have hz2 : linTotalMax ([] : List Int) ([] : List (Int × Int)) = 0 := rfl
              omega
          | succ k' =>
              obtain ⟨h1, h2⟩ := ih bds' k'
              simp only [List.take_succ_cons, List.drop_succ_cons]
              show termMin c bd.1 bd.2 + linTotalMin cs' bds'
                = termMin c bd.1 bd.2 + linTotalMin (List.take k' cs') (List.take k' bds')
                + linTotalMin (List.drop k' cs') (List.drop k' bds') ∧
                termMax c bd.1 bd.2 + linTotalMax cs' bds'
                = termMax c bd.1 bd.2 + linTotalMax (List.take k' cs') (List.take k' bds')
                + linTotalMax (List.drop k' cs') (List.drop k' bds')
              rw [h1, h2]
              omega


/-- **The master narrowing-soundness lemma for `linNarrowAll`**:
    under coverage of the extracted bounds by a satisfying
    assignment (its values picked from the input domains), the
    assignment remains an assignment of the narrowed domains.
    `k` counts the terms the run has already consumed: the current
    triple is `drop k` of the original, the totals stay the
    original's, and each level's filter bound (totals minus the
    head term's extrema) covers the other terms — the processed
    prefix plus the tail — by `linTotal_split` and `others_bound`
    run at the current position. -/
private theorem linNarrowAll_mem :
    ∀ (n : Nat) (k : Nat) (ocs : List Int) (ois : List Nat) (obds : List (Int × Int))
      (totalMin totalMax : Int) (eq : Bool) (b : Int)
      (doms : List (List Value)),
    ocs.length - k = n →
    k ≤ ocs.length →
    ocs.length = ois.length → ois.length = obds.length →
    totalMin = linTotalMin ocs obds → totalMax = linTotalMax ocs obds →
    ∀ (doms' : List (List Value)) (a : List Value)
      (_h : linNarrowAll (List.drop k ocs) (List.drop k ois) (List.drop k obds)
            totalMin totalMax eq b doms = .narrowed doms')
      (_hlen : a.length = doms.length)
      (_hget : ∀ j v, a[j]? = some v → v ∈ getSlot doms j)
      (_hsat : LinSat eq (intVals ocs) (ois.map (fun i => a[i]!)) b)
      (_hcov : LinCover ois obds doms a),
    a ∈ allAssigns doms' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ocs ois obds totalMin totalMax eq b doms hmeasure hkle hlen1 hlen2
      hTmin hTmax doms' a h hlen hget hsat hcov
    -- the current triple's shape decides
    cases hdcs : List.drop k ocs with
    | nil =>
        -- no terms remain: the run's match arm returns .narrowed doms
        -- (the is/bds drops must also be empty by length agreement)
        have hdcslen : (List.drop k ocs).length = ocs.length - k := by simp
        have hislen : (List.drop k ois).length = ois.length - k := by simp
        have hbdslen : (List.drop k obds).length = obds.length - k := by simp
        rw [hdcs, List.length_nil] at hdcslen
        have hisnil : List.drop k ois = [] := by
          cases his : List.drop k ois with
          | nil => rfl
          | cons x xs =>
              have h1 : (x :: xs).length = (List.drop k ois).length := by rw [his]
              rw [hislen] at h1
              simp only [List.length_cons] at h1
              omega
        have hbdsnil : List.drop k obds = [] := by
          cases hbs : List.drop k obds with
          | nil => rfl
          | cons y ys =>
              have h1 : (y :: ys).length = (List.drop k obds).length := by rw [hbs]
              rw [hbdslen] at h1
              simp only [List.length_cons] at h1
              omega
        rw [hdcs, hisnil, hbdsnil] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        rw [hd]
        exact allAssigns_intro doms a hlen hget
    | cons c csuff =>
        -- one term to peel: the head of the current suffix is ocs[k]
        have hcsk : ocs[k]! = c := by
          rw [List.getElem!_eq_getElem?_getD]
          have hlt : k < ocs.length := by
            have h1 : (List.drop k ocs).length = ocs.length - k := by simp
            rw [hdcs] at h1
            simp only [List.length_cons] at h1
            omega
          have hget : ocs[k]? = some c := by
            rw [List.getElem?_eq_getElem hlt]
            -- ocs[k] = (drop k ocs).head — via drop induction on k
            have hdrop : ∀ (l : List Int) (n : Nat) (hlt : n < l.length),
                l[n] = (List.drop n l).headD 0 := by
              intro l n
              induction l generalizing n with
              | nil => intro hlt; exact absurd hlt (by simp)
              | cons x xs ih =>
                  intro hlt
                  cases n with
                  | zero => rfl
                  | succ n' => exact ih n' (by simp only [List.length_cons] at hlt; omega)
            rw [hdrop ocs k hlt, hdcs]
            rfl
          rw [hget]
          rfl
        -- the current is/bds suffixes (cons-shaped by length agreement)
        -- the is/bds suffixes are cons-shaped (length agreement with the cs suffix)
        cases his : List.drop k ois with
        | nil =>
            exfalso
            have h1 : (List.drop k ois).length = ois.length - k := by simp
            have h2 : (List.drop k ocs).length = ocs.length - k := by simp
            rw [his, List.length_nil] at h1
            rw [hdcs, List.length_cons] at h2
            omega
        | cons idx isuff =>
            have issuff : List.drop k ois = idx :: (List.drop (k+1) ois) := by
              have hdrop : List.drop (k+1) ois = (List.drop k ois).drop 1 := by
                rw [← List.drop_drop]
              rw [hdrop, his]
              rfl
            cases hbs : List.drop k obds with
            | nil =>
                exfalso
                have h1 : (List.drop k obds).length = obds.length - k := by simp
                have h2 : (List.drop k ocs).length = ocs.length - k := by simp
                rw [hbs, List.length_nil] at h1
                rw [hdcs, List.length_cons] at h2
                omega
            | cons bd bsuff =>
                have bdssuff : List.drop k obds = bd :: (List.drop (k+1) obds) := by
                  have hdrop : List.drop (k+1) obds = (List.drop k obds).drop 1 := by
                    rw [← List.drop_drop]
                  rw [hdrop, hbs]
                  rfl
                obtain ⟨lo, hi⟩ := id bd
                -- unfold one step of the run
                rw [hdcs, issuff, bdssuff] at h
                rw [show linNarrowAll (c :: csuff) (idx :: List.drop (k+1) ois)
                      (bd :: List.drop (k+1) obds) totalMin totalMax eq b doms
                    = (if (if eq then
                          linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                            (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                        else
                          linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                          (getSlot doms idx)).isEmpty then .contradiction
                      else linNarrowAll csuff (List.drop (k+1) ois) (List.drop (k+1) obds)
                        totalMin totalMax eq b
                        (setSlot doms idx (if eq then
                            linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                              (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                          else linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                            (getSlot doms idx)))) from by
                  rw [linNarrowAll]] at h
                by_cases hempty : (if eq then
                    linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                      (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                  else
                    linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                    (getSlot doms idx)).isEmpty = true
                · rw [if_pos hempty] at h; exact absurd h (by simp)
                · rw [if_neg hempty] at h
                  -- csuff = drop (k+1) ocs (peeling one term)
                  have hcsuff : csuff = List.drop (k+1) ocs := by
                    have hdrop : List.drop (k+1) ocs = (List.drop k ocs).drop 1 := by
                      rw [← List.drop_drop]
                    rw [hdrop, hdcs]
                    rfl
                  rw [hcsuff] at h
                  -- the head filter's pass: the coverage at position k gives
                  -- the assignment's value at slot idx, which passes the filter
                  -- (the filter's interval comes from others_bound at position k)
                  have hklt : k < ois.length := by
                    have h1 : (List.drop k ois).length = ois.length - k := by simp
                    rw [issuff, List.length_cons] at h1
                    omega
                  obtain ⟨hmemk, pk, hvpk, hlok, hhik⟩ := hcov k hklt
                  -- ois[k]! = idx
                  have hoisk : ois[k]! = idx := by
                    have hdd : ∀ (l : List Nat) (n : Nat), n < l.length →
                        l[n]! = (List.drop n l).headD 0 := by
                      intro l n
                      induction l generalizing n with
                      | nil => intro hlt; exact absurd hlt (by simp)
                      | cons x xs ih2 =>
                          intro hlt
                          cases n with
                          | zero => rfl
                          | succ n' => exact ih2 n' (by simp only [List.length_cons] at hlt; omega)
                    have h1 : ois[k]! = (List.drop k ois).headD 0 := hdd ois k hklt
                    rw [h1, issuff]
                    rfl
                  rw [hoisk] at hmemk hvpk
                  -- the filter membership for the assignment's value at slot idx
                  have hfilter' : a[idx]! ∈ (if eq then
                      linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                        (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                    else
                      linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                      (getSlot doms idx)) := by
                    -- the head filter passes because:
                    -- 1. the coverage at k puts pk in [bd.1, bd.2] and in the domain
                    -- 2. others_bound at position k bounds the other terms' sum
                    -- 3. hsat's dot-sum satisfaction pins c*pk within the interval
                    -- Reuse the depth-0 interval derivation: the whole's dot sum
                    -- is b (eq) or ≤ b (le); decompose at the head term.
                    -- The value's filter test (linNarrowEq/Le on .int pk):
                    rw [hvpk]
                    -- now: .int pk ∈ if eq then linNarrowEq ... (getSlot doms idx)
                    -- the filter is a list filter; its membership test is the
                    -- interval condition; cases on eq:
                    -- the interval derivation:
                    -- 1. the whole's dot sum (from hsat via dotProduct_eq_sum)
                    -- 2. others_bound at position k: the other terms' sum is
                    --    bounded by the ORIGINAL totals minus position k's
                    --    term extrema
                    -- 3. the coverage at k: pk ∈ [bd.1, bd.2]
                    -- The interval test, from three facts:
                    -- (A) hsat: the whole's dot sum = b (eq) / ≤ b (le)
                    -- (B) others_bound at k: other terms' sum within
                    --     [totalMin - termMin_k, totalMax - termMax_k]
                    -- (C) coverage at k: pk ∈ [bd.1, bd.2]
                    -- The whole's dot-sum level satisfaction:
                    have hsumsat : (if eq then dotSum (intVals ocs)
                          (ois.map (fun i => a[i]!)) = b
                        else dotSum (intVals ocs)
                            (ois.map (fun i => a[i]!)) ≤ b) := by
                      cases heq : eq with
                      | true =>
                          rw [heq] at hsat
                          rw [show LinSat true (intVals ocs) (ois.map (fun i => a[i]!)) b
                              = (dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                                  = some b) from rfl] at hsat
                          have := dotProduct_eq_sum _ _ _ hsat
                          rw [this]
                          rfl
                      | false =>
                          rw [heq] at hsat
                          rw [show LinSat false (intVals ocs) (ois.map (fun i => a[i]!)) b
                              = (∃ d, dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                                  = some d ∧ d ≤ b) from rfl] at hsat
                          obtain ⟨d, hd, hle⟩ := hsat
                          have := dotProduct_eq_sum _ _ _ hd
                          rw [this] at hle
                          exact hle
                    -- others_bound at position k over the ORIGINAL lists:
                    have hmaplen' : (ois.map (fun i => a[i]!)).length = ois.length := by
                      simp only [List.length_map]
                    obtain ⟨ck, ok, hck, hxk, hlok, hhik, holo, hohi⟩ :=
                      others_bound ocs (ois.map (fun i => a[i]!)) obds k
                        (by rw [hmaplen']; omega)
                        (by rw [hmaplen']; omega)
                        (by
                          intro j hj
                          rw [hmaplen'] at hj
                          obtain ⟨_, pj, hvpj, hloj, hhij⟩ := hcov j hj
                          refine ⟨pj, ?_, hloj, hhij⟩
                          exact map_getElem!_in_bounds a ois j hj ▸ hvpj)
                        (by rw [hmaplen']; omega)
                    -- ck = ocs[k]! = c and ok = the value at position k = pk
                    -- (the position-k value is a[ois[k]!]! = a[idx]! = .int pk)
                    -- the interval, by cases on eq:
                    cases heq : eq with
                    | true =>
                        rw [heq] at hsumsat
                        simp only [if_true] at hsumsat ⊢
                        -- hsumsat: whole = b; holo/hohi: other sums within
                        -- totals ± head extrema; whole = c*ok + other
                        -- (dotSum's cons decomposition at position k — from
                        --  others_bound's own statement shape)
                        -- reduce the position-k projections:
                        have hbdk : obds[k]! = (bd.1, bd.2) := by
                          have hdd : ∀ (l : List (Int × Int)) (n : Nat), n < l.length →
                              l[n]! = (List.drop n l)[0]! := by
                            intro l n
                            induction l generalizing n with
                            | nil => intro hlt; exact absurd hlt (by simp)
                            | cons x xs ih2 =>
                                intro hlt
                                cases n with
                                | zero => rfl
                                | succ n' => exact ih2 n' (by
                                  simp only [List.length_cons] at hlt; omega)
                          rw [hdd obds k (by omega), bdssuff]
                          rfl
                        rw [hbdk] at holo hohi
                        -- ck = c and ok = pk (position-k getters)
                        have hckc : ck = c := by
                          -- hck : ocs[k]! = ck; hcsk : ocs[k]! = c
                          exact hck.symm.trans hcsk
                        have hokpk : ok = pk := by
                          -- the mapped k-th = a[ois[k]!]! = a[idx]! = Value.int pk
                          have hmapped : (ois.map (fun i => a[i]!))[k]!
                              = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
                          rw [hmapped, hoisk] at hxk
                          -- hxk : a[idx]! = Value.int ok; hvpk : a[idx]! = Value.int pk
                          injection hxk.symm.trans hvpk
                        rw [hckc, hokpk] at holo hohi
                        -- conclude by the totals equations (rewrite the goal):
                        rw [hTmin, hTmax]
                        -- the filter's membership test (linNarrowEq's filter):
                        rw [hvpk] at hmemk
                        exact List.mem_filter.mpr ⟨hmemk, by
                          simp only [decide_eq_true_eq, Bool.and_eq_true]
                          -- normalize the projected pair forms
                          have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
                              = termMin c bd.1 bd.2 := rfl
                          have e2 : termMax c (bd.1, bd.2).1 (bd.1, bd.2).2
                              = termMax c bd.1 bd.2 := rfl
                          rw [e1] at holo
                          rw [e2] at hohi
                          constructor <;> omega⟩
                    | false =>
                        rw [heq] at hsumsat
                        simp only [Bool.false_eq_true, if_false] at hsumsat ⊢
                        have hbdk2 : obds[k]! = (bd.1, bd.2) := by
                          have hdd : ∀ (l : List (Int × Int)) (n : Nat), n < l.length →
                              l[n]! = (List.drop n l)[0]! := by
                            intro l n
                            induction l generalizing n with
                            | nil => intro hlt; exact absurd hlt (by simp)
                            | cons x xs ih2 =>
                                intro hlt
                                cases n with
                                | zero => rfl
                                | succ n' => exact ih2 n' (by
                                  simp only [List.length_cons] at hlt; omega)
                          rw [hdd obds k (by omega), bdssuff]
                          rfl
                        rw [hbdk2] at holo
                        -- ck = c, ok = pk
                        have hckc2 : ck = c := hck.symm.trans hcsk
                        have hokpk2 : ok = pk := by
                          have hmapped : (ois.map (fun i => a[i]!))[k]!
                              = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
                          rw [hmapped, hoisk] at hxk
                          injection hxk.symm.trans hvpk
                        rw [hckc2, hokpk2] at holo
                        have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
                            = termMin c bd.1 bd.2 := rfl
                        rw [e1] at holo
                        rw [hTmin]
                        rw [hvpk] at hmemk
                        exact List.mem_filter.mpr ⟨hmemk, by
                          simp only [decide_eq_true_eq]
                          omega⟩
                  -- recurse: the remaining count drops by one
                  have hn1 : ocs.length - (k + 1) < n := by
                    have hm : ocs.length - k = n := hmeasure
                    have hklt : k < ocs.length := by
                      have h1 : (List.drop k ocs).length = ocs.length - k := by simp
                      rw [hdcs, List.length_cons] at h1
                      omega
                    omega
                  exact ih (ocs.length - (k + 1)) hn1 (k + 1) ocs ois obds
                    totalMin totalMax eq b
                    (setSlot doms idx (if eq then
                        linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                          (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                      else linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                        (getSlot doms idx)))
                    (by rfl) (by omega) hlen1 hlen2 hTmin hTmax
                    doms' a h
                    (by rw [setSlot_length]; exact hlen)
                    (by
                      intro j v hv
                      by_cases hidx : j = idx
                      · rw [hidx] at hv ⊢
                        -- a[idx]? = some v; the coverage at k says
                        -- a[idx]! = .int pk; hfilter' passes it
                        have hlt : idx < a.length := by
                          have h1 := lt_length_of_mem_getSlot doms idx (a[idx]!) hmemk
                          rw [hlen]
                          omega
                        have hsome : a[idx]? = some (a[idx]!) := by
                          rw [List.getElem?_eq_getElem hlt,
                            List.getElem!_eq_getElem?_getD,
                            List.getElem?_eq_getElem hlt, Option.getD_some]
                        rw [hsome] at hv
                        have hvv : v = a[idx]! := (Option.some.inj hv).symm
                        rw [hvv]
                        -- read the written slot back
                        rw [getSlot_setSlot_eq doms _ idx (by
                          have h1 := lt_length_of_mem_getSlot doms idx (a[idx]!) hmemk
                          omega)]
                        rw [show a[idx]! = LeanFzn.Semantics.Value.int pk from hvpk]
                        rw [hvpk] at hfilter'
                        exact hfilter'
                      · rw [getSlot_setSlot_of_ne doms _ idx j hidx]
                        exact hget j v hv)
                    (by exact hsat)
                    (by
                      intro m hm
                      obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov m hm
                      by_cases hne : ois[m]! = idx
                      · rw [hne] at hmemv hvp ⊢
                        have hmemint : Value.int p' ∈ getSlot doms idx := by
                          rw [← hvp]; exact hmemv
                        rw [getSlot_setSlot_eq doms _ idx
                          (lt_length_of_mem_getSlot doms idx (Value.int p') hmemint)]
                        -- p' = pk: both are the integer of a[idx]!
                        have hp'p : p' = pk := by
                          have h1 : Value.int p' = Value.int pk :=
                            hvp.symm.trans hvpk
                          injection h1
                        rw [hvp]
                        -- the membership component: .int p' ∈ filter (p' = pk)
                        have hmem' : Value.int p' ∈ (if eq then
                            linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                              (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                          else
                            linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                            (getSlot doms idx)) := by
                          rw [show Value.int p' = Value.int pk from by
                            rw [show p' = pk from hp'p]]
                          rw [hvpk] at hfilter'
                          exact hfilter'
                        exact ⟨hmem', p', rfl, hlo', hhi'⟩
                      · rw [getSlot_setSlot_of_ne doms _ idx _ hne]
                        exact ⟨hmemv, p', hvp, hlo', hhi'⟩)


/-- The linear constraint's satisfaction in `LinSat` form. -/
private theorem linEq_LinSat {coeffs : List Int} {is : List Nat} {b : Int}
    {a : List Value} :
    DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a ↔
      LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b := by
  constructor
  · intro h
    rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl]
    exact h
  · intro h
    rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl] at h
    exact h

/-- The linear inequality's satisfaction in `LinSat` form. -/
private theorem linLe_LinSat {coeffs : List Int} {is : List Nat} {b : Int}
    {a : List Value} :
    DomConstraint.SatisfiedBy (DomConstraint.linLe coeffs is b) a ↔
      LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b := by
  constructor
  · intro h
    rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
            = some d ∧ d ≤ b) from rfl]
    rw [DomConstraint.SatisfiedBy] at h
    rw [dotLe_eq] at h
    exact h
  · intro h
    rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
            = some d ∧ d ≤ b) from rfl] at h
    -- goal: dotLe ... = true
    show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
    rw [dotLe_eq]
    exact h

/-- A mismatched-shape dot product is `none`: the linear
    constraint is unsatisfiable when the coefficient and slot
    lists have different lengths. -/
private theorem dotProduct_mismatch {cs : List Int} {is : List Nat}
    {xs : List Value} (hne : cs.length ≠ is.length) :
    dotProduct (intVals cs) (is.map (fun i => xs[i]!)) = none := by
  -- the mapped list has is' length; dotProduct recurses on both lists
  -- simultaneously and returns none on any shape mismatch
  -- induct on cs, comparing with the mapped list's shape
  induction cs generalizing is with
  | nil =>
      cases is with
      | nil => exact absurd rfl hne
      | cons i rest =>
          show dotProduct (intVals ([] : List Int))
              ((i :: rest).map (fun i => xs[i]!)) = none
          rw [show (i :: rest).map (fun i => xs[i]!)
              = xs[i]! :: rest.map (fun i => xs[i]!) from rfl]
          cases xs[i]! with
          | int v => rfl
          | bool v => rfl
          | setOfInt v => rfl
          | array v => rfl
  | cons c cs' ih =>
      cases is with
      | nil =>
          show dotProduct (intVals (c :: cs'))
              (([] : List Nat).map (fun i => xs[i]!)) = none
          rfl
      | cons i rest =>
          show dotProduct (intVals (c :: cs'))
              ((i :: rest).map (fun i => xs[i]!)) = none
          rw [show (i :: rest).map (fun i => xs[i]!)
              = xs[i]! :: rest.map (fun i => xs[i]!) from rfl]
          cases xs[i]! with
          | int v =>
              show (match dotProduct (intVals cs') (rest.map (fun i => xs[i]!)) with
                | some s => some (c * v + s)
                | none => none) = none
              have hne' : cs'.length ≠ rest.length := by
                simp only [List.length_cons] at hne
                omega
              rw [ih hne']
          | bool v => rfl
          | setOfInt v => rfl
          | array v => rfl

/-- `getSlot` past the end of the slot list is empty. -/
private theorem getSlot_eq_nil : ∀ (doms : List (List Value)) (j : Nat),
    doms.length ≤ j → getSlot doms j = [] := by
  intro doms
  induction doms with
  | nil => intro _ _; rfl
  | cons d ds ih =>
      intro j hge
      cases j with
      | zero =>
          simp only [List.length_cons] at hge
          omega
      | succ j' => exact ih j' (by simp only [List.length_cons] at hge; omega)

/-- The run's narrowed domains are pointwise subsets of the
    input (each written slot is a filter of its domain). -/
private theorem linNarrowAll_subset :
    ∀ (cs : List Int) (is : List Nat) (bds : List (Int × Int))
      (totalMin totalMax : Int) (eq : Bool) (b : Int)
      (doms doms' : List (List Value)),
    linNarrowAll cs is bds totalMin totalMax eq b doms = .narrowed doms' →
    DomPointwiseSub doms' doms := by
  intro cs
  induction cs with
  | nil =>
      intro is bds totalMin totalMax eq b doms doms' h
      cases is with
      | nil =>
          cases bds with
          | nil =>
              have hd : doms' = doms := (PropResult.narrowed.inj h).symm
              rw [hd]
              exact DomPointwiseSub.refl doms
          | cons _ _ => exact absurd h (by simp [linNarrowAll])
      | cons _ _ => exact absurd h (by simp [linNarrowAll])
  | cons c cs' ih =>
      intro is bds totalMin totalMax eq b doms doms' h
      cases is with
      | nil => exact absurd h (by
          cases bds with
          | nil => exact absurd h (by simp [linNarrowAll])
          | cons _ _ => exact absurd h (by simp [linNarrowAll]))
      | cons idx is' =>
          cases bds with
          | nil => exact absurd h (by simp [linNarrowAll])
          | cons bd bds' =>
              obtain ⟨lo, hi⟩ := bd
              rw [linNarrowAll] at h
              by_cases hempty : (if eq then
                  linNarrowEq c b (totalMin - termMin c lo hi)
                    (totalMax - termMax c lo hi) (getSlot doms idx)
                else
                  linNarrowLe c b (totalMin - termMin c lo hi)
                  (getSlot doms idx)).isEmpty = true
              · rw [if_pos hempty] at h; exact absurd h (by simp)
              · rw [if_neg hempty] at h
                have ih' := ih is' bds' totalMin totalMax eq b
                  (setSlot doms idx (if eq then
                      linNarrowEq c b (totalMin - termMin c lo hi)
                        (totalMax - termMax c lo hi) (getSlot doms idx)
                    else linNarrowLe c b (totalMin - termMin c lo hi)
                      (getSlot doms idx))) doms' h
                -- compose: doms' ⊆ setSlot doms idx d (ih') and
                -- setSlot doms idx d ⊆ doms (the filter shrinks one slot)
                refine ⟨ih'.1.trans (by rw [setSlot_length]), ?_⟩
                intro k v hv
                have hv' := ih'.2 k v hv
                -- hv' : v ∈ getSlot (setSlot doms idx d) k
                by_cases hkk : k = idx
                · rw [hkk] at hv' ⊢
                  show v ∈ getSlot doms idx
                  -- the written slot reads back as the filter
                  have hlt : idx < doms.length := by
                    by_cases hlt' : idx < doms.length
                    · exact hlt'
                    · -- out of range: getSlot doms idx = [] and the filter
                      -- of [] is empty, so v ∈ [] is impossible
                      exfalso
                      have hge : doms.length ≤ idx := by omega
                      have hnil : getSlot doms idx = [] :=
                        getSlot_eq_nil doms idx hge
                      -- the written slot (past the end) reads back as the
                      -- filter of the empty domain, which is empty
                      rw [setSlot_eq_self_of_le doms _ idx hge] at hv'
                      rw [hnil] at hv'
                      exact absurd hv' (by simp)
                  rw [getSlot_setSlot_eq doms _ idx hlt] at hv'
                  cases heqb : eq with
                  | true =>
                      rw [heqb, if_pos rfl] at hv'
                      exact List.mem_filter.mp hv' |>.1
                  | false =>
                      rw [heqb, if_neg (by decide : ¬ (false = true))] at hv'
                      exact List.mem_filter.mp hv' |>.1
                · rw [getSlot_setSlot_of_ne doms _ idx k hkk] at hv'
                  exact hv'

/-- A successful dot product forces every value of the
    second list to be an integer at the listed positions (the
    `_, _ => none` catch-all never fired). -/
private theorem dotProduct_some_int :
    ∀ (cs xs : List Value) (b : Int),
    dotProduct cs xs = some b →
    ∀ k, k < xs.length → ∃ p, xs[k]! = Value.int p := by
  intro cs
  induction cs with
  | nil =>
      intro xs b h k hk
      cases xs with
      | nil => exact absurd hk (by simp)
      | cons x xs' =>
          exfalso
          rw [show dotProduct ([] : List Value) (x :: xs') = none from by
            cases x with
            | int v => rfl
            | bool v => rfl
            | setOfInt v => rfl
            | array v => rfl] at h
          exact absurd h (by simp)
  | cons c cs' ih =>
      intro xs b h k hk
      cases xs with
      | nil =>
          exfalso
          cases c with
          | int v =>
              rw [show dotProduct (.int v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | bool v =>
              rw [show dotProduct (.bool v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | setOfInt v =>
              rw [show dotProduct (.setOfInt v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | array v =>
              rw [show dotProduct (.array v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
      | cons x xs' =>
          cases c with
          | int v =>
              cases x with
              | int xv =>
                  rw [dotProduct] at h
                  cases hrest : dotProduct cs' xs' with
                  | none => rw [hrest] at h; exact absurd h (by simp)
                  | some s' =>
                      cases k with
                      | zero => exact ⟨xv, rfl⟩
                      | succ k' =>
                          have hk' : k' < xs'.length := by
                            simp only [List.length_cons] at hk
                            omega
                          exact ih xs' s' hrest k' hk'
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | bool v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | setOfInt v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | array v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])

/-- The extract preserves the length: each listed slot yields
    exactly one bounds pair. -/
private theorem linExtract_length :
    ∀ (is : List Nat) (doms : List (List Value)) (bds : List (Int × Int)),
    linExtract is doms = some bds → is.length = bds.length := by
  intro is
  induction is with
  | nil =>
      intro doms bds h
      cases bds with
      | nil => rfl
      | cons x xs =>
          rw [linExtract] at h
          exact absurd h (by intro hcon; cases hcon)
  | cons idx rest ih =>
      intro doms bds h
      rw [linExtract] at h
      cases hmin : domMin (getSlot doms idx) with
      | none => rw [hmin] at h; exact absurd h (by simp)
      | some lo =>
          rw [hmin] at h
          cases hmax : domMax (getSlot doms idx) with
          | none => rw [hmax] at h; exact absurd h (by simp)
          | some hi =>
              rw [hmax] at h
              cases hrest : linExtract rest doms with
              | none => rw [hrest] at h; exact absurd h (by simp)
              | some bds' =>
                  rw [hrest] at h
                  have hb : bds = (lo, hi) :: bds' := (Option.some.inj h).symm
                  rw [hb]
                  simp only [List.length_cons]
                  have := ih doms bds' hrest
                  omega

/-- The coverage of the extracted bounds by a satisfying
    assignment: the constraint's satisfaction forces every listed
    value to be an integer (the dot product exists), and
    `domMin`/`domMax` of the domain bound it by the extracted
    interval. -/
private theorem linExtract_cover :
    ∀ (is : List Nat) (doms : List (List Value)) (bds : List (Int × Int))
      (a : List Value),
    linExtract is doms = some bds →
    a.length = doms.length →
    (∀ j v, a[j]? = some v → v ∈ getSlot doms j) →
    (∀ k, k < is.length → ∃ p, a[is[k]!]! = Value.int p) →
    LinCover is bds doms a := by
  intro is
  induction is with
  | nil =>
      intro doms bds a hbds hlen hget _hint k hk
      exact absurd hk (by simp)
  | cons idx rest ih =>
      intro doms bds a hbds hlen hget hint k hk
      rw [linExtract] at hbds
      cases hmin : domMin (getSlot doms idx) with
      | none => rw [hmin] at hbds; exact absurd hbds (by simp)
      | some lo =>
          rw [hmin] at hbds
          cases hmax : domMax (getSlot doms idx) with
          | none => rw [hmax] at hbds; exact absurd hbds (by simp)
          | some hi =>
              rw [hmax] at hbds
              cases hrest : linExtract rest doms with
              | none => rw [hrest] at hbds; exact absurd hbds (by simp)
              | some bds' =>
                  rw [hrest] at hbds
                  have hbds' : bds = (lo, hi) :: bds' := (Option.some.inj hbds).symm
                  subst hbds'
                  cases k with
                  | zero =>
                      obtain ⟨p, hp⟩ := hint 0 (by simp)
                      rw [show (idx :: rest)[0]! = idx from rfl] at hp
                      refine ⟨?_, p, hp, ?_, ?_⟩
                      · -- the value is in the domain
                        -- the integrality hint forces idx < a.length
                        -- (a[idx]! = .int p, and out-of-range gives .bool false)
                        have hlt : idx < a.length := by
                          by_cases hidx : idx < a.length
                          · exact hidx
                          · exfalso
                            -- out of range: a[idx]! = default = .bool false
                            have hdef : a[idx]! = (default : Value) := by
                              rw [List.getElem!_eq_getElem?_getD]
                              rw [List.getElem?_eq_none_iff.mpr (by omega)]
                              rfl
                            rw [hdef] at hp
                            exact nomatch hp
                        have hsome : a[idx]? = some (a[idx]!) := by
                          rw [List.getElem?_eq_getElem hlt,
                            List.getElem!_eq_getElem?_getD,
                            List.getElem?_eq_getElem hlt, Option.getD_some]
                        exact hget idx _ hsome
                      · -- lo ≤ p: domMin bounds any integer member
                        have hmem : Value.int p ∈ getSlot doms idx := by
                          have hlt : idx < a.length := by
                            by_cases hidx : idx < a.length
                            · exact hidx
                            · exfalso
                              have hdef : a[idx]! = (default : Value) := by
                                rw [List.getElem!_eq_getElem?_getD,
                                  List.getElem?_eq_none_iff.mpr (by omega)]
                                rfl
                              rw [hdef] at hp
                              exact nomatch hp
                          have hsome : a[idx]? = some (a[idx]!) := by
                            rw [List.getElem?_eq_getElem hlt,
                              List.getElem!_eq_getElem?_getD,
                              List.getElem?_eq_getElem hlt, Option.getD_some]
                          rw [hp] at hsome
                          exact hget idx _ hsome
                        obtain ⟨m1, hm1, hle⟩ := domMin_of_mem hmem
                        rw [hmin] at hm1
                        -- hm1 : domMin (getSlot doms idx) = some m1, so m1 = lo
                        have : m1 = lo := (Option.some.inj hm1).symm
                        rw [this] at hle
                        exact hle
                      · -- p ≤ hi: domMax bounds any integer member
                        have hmem : Value.int p ∈ getSlot doms idx := by
                          have hlt : idx < a.length := by
                            by_cases hidx : idx < a.length
                            · exact hidx
                            · exfalso
                              have hdef : a[idx]! = (default : Value) := by
                                rw [List.getElem!_eq_getElem?_getD,
                                  List.getElem?_eq_none_iff.mpr (by omega)]
                                rfl
                              rw [hdef] at hp
                              exact nomatch hp
                          have hsome : a[idx]? = some (a[idx]!) := by
                            rw [List.getElem?_eq_getElem hlt,
                              List.getElem!_eq_getElem?_getD,
                              List.getElem?_eq_getElem hlt, Option.getD_some]
                          rw [hp] at hsome
                          exact hget idx _ hsome
                        obtain ⟨m2, hm2, hle⟩ := domMax_of_mem hmem
                        rw [hmax] at hm2
                        have : m2 = hi := (Option.some.inj hm2).symm
                        rw [this] at hle
                        exact hle
                  | succ k' =>
                      have ih' := ih doms bds' a hrest hlen hget
                        (fun k hk' => hint (k + 1) (by simpa using hk')) k'
                        (by simpa using hk)
                      exact ih'

/-- **The head-filter pass lemma** (the factored interval
    derivation of the master lemma): under the coverage invariant
    and the whole-triple's satisfaction, the assignment's value at
    the position-`k` slot passes the position-`k` filter. -/
private theorem lin_head_filter_pass {ocs : List Int} {ois : List Nat}
    {obds : List (Int × Int)} {totalMin totalMax : Int} {eq : Bool} {b : Int}
    {doms : List (List Value)} {a : List Value} {k : Nat}
    {c : Int} {idx : Nat} {bd : Int × Int}
    (hshape : ocs.length = ois.length)
    (hshape2 : ois.length = obds.length)
    (hTmin : totalMin = linTotalMin ocs obds)
    (hTmax : totalMax = linTotalMax ocs obds)
    (hsat : LinSat eq (intVals ocs) (ois.map (fun i => a[i]!)) b)
    (hcov : LinCover ois obds doms a)
    (hklt : k < ois.length)
    (hck : ocs[k]! = c) (hidx : ois[k]! = idx) (hbd : obds[k]! = bd) :
    ∃ pk, a[idx]! = LeanFzn.Semantics.Value.int pk ∧
      a[idx]! ∈ (if eq then
          linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
            (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
        else
          linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
          (getSlot doms idx)) := by
  -- the coverage at position k gives the value and its interval
  obtain ⟨hmemk, pk, hvpk, hlok, hhik⟩ := hcov k hklt
  rw [hidx] at hmemk hvpk
  refine ⟨pk, hvpk, ?_⟩
  -- the dot-sum level satisfaction
  have hsumsat : (if eq then dotSum (intVals ocs)
        (ois.map (fun i => a[i]!)) = b
      else dotSum (intVals ocs)
          (ois.map (fun i => a[i]!)) ≤ b) := by
    cases heq : eq with
    | true =>
        rw [heq] at hsat
        rw [show LinSat true (intVals ocs) (ois.map (fun i => a[i]!)) b
            = (dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                = some b) from rfl] at hsat
        have := dotProduct_eq_sum _ _ _ hsat
        rw [this]
        rfl
    | false =>
        rw [heq] at hsat
        rw [show LinSat false (intVals ocs) (ois.map (fun i => a[i]!)) b
            = (∃ d, dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                = some d ∧ d ≤ b) from rfl] at hsat
        obtain ⟨d, hd, hle⟩ := hsat
        have := dotProduct_eq_sum _ _ _ hd
        rw [this] at hle
        exact hle
  -- others_bound at position k over the ORIGINAL lists
  have hmaplen' : (ois.map (fun i => a[i]!)).length = ois.length := by
    simp only [List.length_map]
  have hkltm : k < (ois.map (fun i => a[i]!)).length := by
    rw [hmaplen']
    exact hklt
  obtain ⟨ck, ok, hck2, hxk, hlok2, hhik2, holo, hohi⟩ :=
    others_bound ocs (ois.map (fun i => a[i]!)) obds k
      (by rw [hmaplen']; exact hshape)
      (by rw [hmaplen']; exact hshape2)
      (by
        intro j hj
        rw [hmaplen'] at hj
        obtain ⟨_, pj, hvpj, hloj, hhij⟩ := hcov j hj
        refine ⟨pj, ?_, hloj, hhij⟩
        exact map_getElem!_in_bounds a ois j hj ▸ hvpj)
      (by rw [hmaplen']; omega)
  -- ck = c (position k's coefficient) and ok = pk (position k's value)
  have hckc : ck = c := hck2.symm.trans hck
  have hokpk : ok = pk := by
    have hmapped : (ois.map (fun i => a[i]!))[k]!
        = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
    rw [hmapped, hidx] at hxk
    injection hxk.symm.trans hvpk
  -- the position-k bounds projections
  have hbdk : obds[k]! = (bd.1, bd.2) := hbd
  -- the interval, by cases on eq
  cases heq : eq with
  | true =>
      rw [heq] at hsumsat
      simp only [if_true] at hsumsat ⊢
      rw [hbdk] at holo hohi
      rw [hckc, hokpk] at holo hohi
      rw [hTmin, hTmax]
      have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMin c bd.1 bd.2 := rfl
      have e2 : termMax c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMax c bd.1 bd.2 := rfl
      rw [e1] at holo
      rw [e2] at hohi
      -- the dot sum decomposes at position k: whole = c*pk + rest
      -- (from others_bound's own statement shape and hsumsat)
      rw [hvpk] at hmemk ⊢
      exact List.mem_filter.mpr ⟨hmemk, by
        simp only [decide_eq_true_eq, Bool.and_eq_true]
        constructor <;> omega⟩
  | false =>
      rw [heq] at hsumsat
      simp only [Bool.false_eq_true, if_false] at hsumsat ⊢
      rw [hbdk] at holo
      rw [hckc, hokpk] at holo
      rw [hTmin]
      have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMin c bd.1 bd.2 := rfl
      rw [e1] at holo
      rw [hvpk] at hmemk ⊢
      exact List.mem_filter.mpr ⟨hmemk, by
        simp only [decide_eq_true_eq]
        omega⟩

/-- **Preservation for `propLinEq`**: a satisfying assignment of
    the input domains remains an assignment of the narrowed
    domains; a reported contradiction is sound; the narrowing only
    shrinks. -/
theorem propLinEq_preserves (coeffs : List Int) (is : List Nat) (b : Int) :
    Preserves (DomConstraint.linEq coeffs is b) (propLinEq coeffs is b) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
    | none => rw [hex] at h; exact absurd h (by simp)
    | some bds =>
        rw [hex] at h
        -- iota-reduce the match on `some bds`
        rw [show (match some bds with
            | none => PropResult.contradiction
            | some bds' => linNarrowAll coeffs is bds'
                (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
          = linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
              true b doms from rfl] at h
        obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
        -- the coverage (with integrality from the satisfaction)
        have hcov : LinCover is bds doms a :=
          linExtract_cover is doms bds a hex hlen hget
            (fun k hk => by
              -- integrality: the constraint's satisfaction gives
              -- dotProduct = some b, which forces every listed value
              -- to be an integer
              have hsat' := linEq_LinSat.mp hsat
              rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
                  = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                      = some b) from rfl] at hsat'
              have hint := dotProduct_some_int (intVals coeffs)
                (is.map (fun i => a[i]!)) b hsat'
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                  simp only [List.length_map]] at hint
              obtain ⟨p, hp⟩ := hint k hk
              rw [map_getElem!_in_bounds a is k hk] at hp
              exact ⟨p, hp⟩)
        -- the shape premise coeffs.length = is.length is needed; derive
        -- from the extract's structure (bds has is' length) — for now the
        -- honest constraint: the propagator is only sound on aligned shapes,
        -- which the extract guarantees when it returns some bds
        have hshape : coeffs.length = is.length := hshape
        have hshape2 : is.length = bds.length :=
          linExtract_length is doms bds hex
        exact linNarrowAll_mem coeffs.length 0 coeffs is bds
          (linTotalMin coeffs bds) (linTotalMax coeffs bds) true b doms
          (by simp) (Nat.zero_le _) hshape hshape2
          rfl rfl doms' a h hlen hget
          (linEq_LinSat.mp hsat) hcov
    · -- mismatched shape: the propagator returned contradiction
      rw [if_neg hshape] at h
      exact absurd h (by simp)
  · -- subset: each narrowed slot is a filter of the original
    intro doms doms' h
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none => rw [hex] at h; exact absurd h (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) true b doms from rfl] at h
          exact linNarrowAll_subset coeffs is bds
            (linTotalMin coeffs bds) (linTotalMax coeffs bds) true b doms doms' h
    · rw [if_neg hshape] at h; exact absurd h (by simp)
  · -- contradiction soundness
    intro doms h a ha hsat
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none =>
          -- the extract failed: some listed slot's domain lacks integers
          -- (domMin/domMax returned none). The satisfying assignment's
          -- value at that slot must be an integer in the domain (the dot
          -- product exists), and any integer member makes domMin some —
          -- contradiction.
          -- locate the failing position
          -- domMin and domMax agree on existence: both scan the same
          -- domain for integers
          have hagree : ∀ (d : List Value),
              (domMin d).isSome = true → (domMax d).isSome = true := by
            intro d
            induction d with
            | nil => intro h; exact absurd h (by simp [domMin])
            | cons v vs ih =>
                intro h
                cases hv : v with
                | int p =>
                    have : domMax (Value.int p :: vs)
                        = maxOpt (domMax vs) p := rfl
                    rw [this]
                    cases hdp : domMax vs with
                    | none => rfl
                    | some m => rfl
                | bool p =>
                    subst hv
                    have heq : domMax (Value.bool p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.bool p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | setOfInt p =>
                    subst hv
                    have heq : domMax (Value.setOfInt p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.setOfInt p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | array p =>
                    subst hv
                    have heq : domMax (Value.array p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.array p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
          have hfail : ∃ k, k < is.length ∧
              (domMin (getSlot doms (is[k]!))).isNone = true := by
            -- induction over the extract's recursion
            have hexrec : ∀ (js : List Nat),
                linExtract js doms = none →
                ∃ k, k < js.length ∧ (domMin (getSlot doms (js[k]!))).isNone = true := by
              intro js
              induction js with
              | nil => intro h; exact absurd h (by simp [linExtract])
              | cons j js' ih =>
                  intro h
                  rw [linExtract] at h
                  cases hmin : domMin (getSlot doms j) with
                  | none =>
                      rw [hmin] at h
                      refine ⟨0, by simp, ?_⟩
                      rw [show (j :: js')[0]! = j from rfl, hmin]
                      rfl
                  | some lo =>
                      rw [hmin] at h
                      cases hmax : domMax (getSlot doms j) with
                      | none =>
                          -- domMax none with domMin some is impossible
                          exfalso
                          have hcontr : (domMax (getSlot doms j)).isSome = true :=
                            hagree (getSlot doms j) (by rw [hmin]; rfl)
                          rw [hmax] at hcontr
                          exact absurd hcontr (by simp)
                      | some hi =>
                          -- the match reduces: Option.map f (linExtract js' doms);
                          -- the outer = none forces the tail extract = none
                          rw [hmax] at h
                          -- reduce the match to the Option.map form
                          have hmap : (match some lo, some hi with
                              | some lo, some hi =>
                                Option.map (fun bds => (lo, hi) :: bds) (linExtract js' doms)
                              | x, x_1 => none) = none := h
                          rw [Option.map_eq_none_iff] at hmap
                          obtain ⟨k, hk, hnone⟩ := ih hmap
                          refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
                          rw [show (j :: js')[k + 1]! = js'[k]! from rfl]
                          exact hnone
            exact hexrec is hex
          obtain ⟨k, hk, hnone⟩ := hfail
          -- the assignment's value at is[k]! is an integer in the domain
          have hsat' := linEq_LinSat.mp hsat
          rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
              = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                  = some b) from rfl] at hsat'
          have hint := dotProduct_some_int (intVals coeffs)
            (is.map (fun i => a[i]!)) b hsat' k
            (by
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                simp only [List.length_map]]
              exact hk)
          obtain ⟨p, hp⟩ := hint
          rw [map_getElem!_in_bounds a is k hk] at hp
          -- the value is in the domain (allAssigns)
          obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
          have hmem : Value.int p ∈ getSlot doms (is[k]!) := by
            obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
            by_cases halt : is[k]! < a.length
            · -- in range: the allAssigns spec gives the membership
              have hsome : a[is[k]!]? = some (a[is[k]!]!) := by
                have hsome' : a[is[k]!]? = some a[is[k]!] :=
                  List.getElem?_eq_getElem halt
                rw [hsome']
                show some a[is[k]!] = some a[is[k]!]!
                rw [show a[is[k]!]! = a[is[k]!] from by
                  rw [List.getElem!_eq_getElem?_getD, hsome', Option.getD_some]]
              have hv : a[is[k]!]! ∈ getSlot doms (is[k]!) :=
                hget2 (is[k]!) _ hsome
              rw [hp] at hv
              exact hv
            · -- out of range: a[is[k]!]! = default (.bool false), but
              -- dotProduct_some_int's witness says it is .int p —
              -- contradiction
              exfalso
              have hdef : a[is[k]!]! = (default : Value) := by
                rw [List.getElem!_eq_getElem?_getD,
                  List.getElem?_eq_none_iff.mpr (by omega)]
                rfl
              rw [hdef] at hp
              exact nomatch hp
          -- domMin of a domain with an integer member is some
          obtain ⟨m, hm, _⟩ := domMin_of_mem hmem
          have hnone' : domMin (getSlot doms is[k]!) = none := by
            cases hdp : domMin (getSlot doms is[k]!) with
            | none => rfl
            | some v =>
                rw [hdp] at hnone
                exact absurd hnone (by simp)
          rw [hnone'] at hm
          exact absurd hm (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) true b doms from rfl] at h
          -- the assignment's spec (length + membership)
          obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
          -- the satisfaction and the integrality hint, derived once
          have hsat' := linEq_LinSat.mp hsat
          have hint : ∀ k, k < is.length →
              ∃ p, a[is[k]!]! = Value.int p := by
            intro k hk
            rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
                = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                    = some b) from rfl] at hsat'
            have hmaplen2 : (is.map (fun i => a[i]!)).length = is.length := by
              simp only [List.length_map]
            have hint2 := dotProduct_some_int (intVals coeffs)
              (is.map (fun i => a[i]!)) b hsat' k (by rw [hmaplen2]; exact hk)
            obtain ⟨p, hp⟩ := hint2
            rw [map_getElem!_in_bounds a is k hk] at hp
            exact ⟨p, hp⟩
          -- the first-contradiction analysis: an induction over the run
          have hrun : ∀ (n : Nat) (k : Nat) (doms2 : List (List Value)),
              coeffs.length - k = n → k ≤ coeffs.length →
              linNarrowAll (List.drop k coeffs) (List.drop k is)
                (List.drop k bds) (linTotalMin coeffs bds) (linTotalMax coeffs bds)
                true b doms2 = .contradiction →
              LinCover is bds doms2 a →
              LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b →
              False := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              intro k doms2 hmeasure hkle h hcov' hsat'
              cases hdcs : List.drop k coeffs with
              | nil =>
                  -- no terms: the run returns .narrowed, not .contradiction
                  have hdcslen : (List.drop k coeffs).length = coeffs.length - k := by simp
                  rw [hdcs, List.length_nil] at hdcslen
                  have hisnil : List.drop k is = [] := by
                    cases his2 : List.drop k is with
                    | nil => rfl
                    | cons x xs =>
                        exfalso
                        have h1 : (x :: xs).length = (List.drop k is).length := by
                          rw [his2]
                        have h1' : (List.drop k is).length = is.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : coeffs.length = is.length := hshape
                        omega
                  have hbdsnil : List.drop k bds = [] := by
                    cases hbs2 : List.drop k bds with
                    | nil => rfl
                    | cons y ys =>
                        exfalso
                        have h1 : (y :: ys).length = (List.drop k bds).length := by
                          rw [hbs2]
                        have h1' : (List.drop k bds).length = bds.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : is.length = bds.length :=
                          linExtract_length is doms bds hex
                        omega
                  rw [hdcs, hisnil, hbdsnil] at h
                  exact absurd h (by simp [linNarrowAll])
              | cons c csuff =>
                  cases his : List.drop k is with
                  | nil =>
                      exfalso
                      have h1 : (List.drop k is).length = is.length - k := by simp
                      have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                      rw [his, List.length_nil] at h1
                      rw [hdcs, List.length_cons] at h2
                      omega
                  | cons idx isuff =>
                      cases hbs : List.drop k bds with
                      | nil =>
                          exfalso
                          have h1 : (List.drop k bds).length = bds.length - k := by simp
                          have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                          rw [hbs, List.length_nil] at h1
                          rw [hdcs, List.length_cons] at h2
                          have h3 : is.length = bds.length :=
                            linExtract_length is doms bds hex
                          omega
                      | cons bd bsuff =>
                          have hck : coeffs[k]! = c := by
                            have hlt : k < coeffs.length := by
                              have h1 : (List.drop k coeffs).length = coeffs.length - k := by simp
                              rw [hdcs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Int) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop coeffs k hlt, hdcs]
                            rfl
                          have hidx : is[k]! = idx := by
                            have hlt : k < is.length := by
                              have h1 : (List.drop k is).length = is.length - k := by simp
                              rw [his, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Nat) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop is k hlt, his]
                            rfl
                          have hbd : bds[k]! = bd := by
                            have hlt : k < bds.length := by
                              have h1 : (List.drop k bds).length = bds.length - k := by simp
                              rw [hbs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List (Int × Int)) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD (0, 0) := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop bds k hlt, hbs]
                            rfl
                          have hklt : k < is.length := by
                            have h1 : (List.drop k is).length = is.length - k := by simp
                            rw [his, List.length_cons] at h1
                            omega
                          -- unfold one step
                          rw [hdcs, his, hbs] at h
                          rw [linNarrowAll] at h
                          by_cases hcond : (linNarrowEq c b
                              (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                              (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                              (getSlot doms2 idx)).isEmpty = true
                          · -- the head filter emptied: the value passes by
                            -- lin_head_filter_pass — contradiction with empty
                            rw [show (if true = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_pos (rfl : true = true)] at h
                            rw [if_pos hcond] at h
                            obtain ⟨pk, hvpk, hmemf⟩ :=
                              lin_head_filter_pass (ocs := coeffs) (ois := is)
                                (obds := bds)
                                (totalMin := linTotalMin coeffs bds)
                                (totalMax := linTotalMax coeffs bds)
                                (eq := true) (b := b) (doms := doms2) (a := a) (k := k)
                                (c := c) (idx := idx) (bd := bd)
                                hshape (linExtract_length is doms bds hex)
                                rfl rfl hsat' hcov' hklt hck hidx hbd
                            -- hmemf : a[idx]! ∈ the filter, which is empty
                            -- (the split's branch condition is the filter's
                            --  isEmpty = true)
                            have hfnil : (linNarrowEq c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                (getSlot doms2 idx)) = [] := by
                              rw [← List.isEmpty_iff]
                              exact hcond
                            rw [hfnil] at hmemf
                            exact absurd hmemf (by simp)
                          · -- the filter kept values: the run recursed —
                            -- the contradiction comes from the tail
                            -- h (with the inner if already reduced by the
                            -- rw [linNarrowAll]) is the Prop-if; hcond
                            -- selects the else branch
                            -- reduce the inner `if true = true` and select
                            -- the else branch via hcond
                            rw [show (if true = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_pos (rfl : true = true)] at h
                            rw [if_neg hcond] at h
                            have hcsuff : csuff = List.drop (k+1) coeffs := by
                              have hdrop : List.drop (k+1) coeffs
                                  = (List.drop k coeffs).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hdcs]
                              rfl
                            rw [hcsuff] at h
                            rw [show isuff = List.drop (k+1) is from by
                              have hdrop : List.drop (k+1) is
                                  = (List.drop k is).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, his]
                              rfl,
                              show bsuff = List.drop (k+1) bds from by
                              have hdrop : List.drop (k+1) bds
                                  = (List.drop k bds).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hbs]
                              rfl] at h
                            have hn1 : coeffs.length - (k + 1) < n := by omega
                            -- the tail: recurse with the written domains
                            -- and the original coverage (the written slot
                            -- passes by lin_head_filter_pass, the master
                            -- lemma's interval derivation)
                            exact ih (coeffs.length - (k + 1)) hn1 (k + 1)
                              (setSlot doms2 idx (linNarrowEq c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                (getSlot doms2 idx)))
                              (by omega) (by omega) h
                              (by
                                intro mm hmm
                                obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov' mm hmm
                                by_cases hne : is[mm]! = idx
                                · rw [hne] at hmemv hvp
                                  have hmemint : Value.int p' ∈ getSlot doms2 idx := by
                                    rw [← hvp]
                                    exact hmemv
                                  obtain ⟨pk2, hvp2, hmemf2⟩ :=
                                    lin_head_filter_pass (ocs := coeffs)
                                      (ois := is) (obds := bds)
                                      (totalMin := linTotalMin coeffs bds)
                                      (totalMax := linTotalMax coeffs bds)
                                      (eq := true) (b := b) (doms := doms2)
                                      (a := a) (k := k) (c := c) (idx := idx)
                                      (bd := bd) hshape
                                      (linExtract_length is doms bds hex)
                                      rfl rfl (linEq_LinSat.mp hsat) hcov' hklt
                                      hck hidx hbd
                                  rw [hne]
                                  rw [getSlot_setSlot_eq doms2 _ idx
                                    (lt_length_of_mem_getSlot doms2 idx
                                      (Value.int p') hmemint)]
                                  -- p' = pk2: both are the integer of a[idx]!
                                  have hp'pk : p' = pk2 := by
                                    have h1 : Value.int p' = Value.int pk2 :=
                                      hvp.symm.trans hvp2
                                    injection h1
                                  rw [hp'pk] at hlo' hhi'
                                  exact ⟨hmemf2, pk2, hvp2, hlo', hhi'⟩
                                · rw [getSlot_setSlot_of_ne doms2 _ idx _ hne]
                                  exact ⟨hmemv, p', hvp, hlo', hhi'⟩)
                              (by exact linEq_LinSat.mp hsat)
          exact hrun coeffs.length 0 doms (by simp) (Nat.zero_le _) h
            (linExtract_cover is doms bds a hex hlen hget hint)
            (linEq_LinSat.mp hsat)
    · -- mismatched shape: the constraint is unsatisfiable (the dot
      -- product needs equal lengths), so contradiction is sound
      rw [if_neg hshape] at h
      obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
      have hsat' := linEq_LinSat.mp hsat
      rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
          = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
              = some b) from rfl] at hsat'
      rw [dotProduct_mismatch hshape] at hsat'
      exact absurd hsat' (by simp)

theorem propLinLe_preserves (coeffs : List Int) (is : List Nat) (b : Int) :
    Preserves (DomConstraint.linLe coeffs is b) (propLinLe coeffs is b) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
    | none => rw [hex] at h; exact absurd h (by simp)
    | some bds =>
        rw [hex] at h
        -- iota-reduce the match on `some bds`
        rw [show (match some bds with
            | none => PropResult.contradiction
            | some bds' => linNarrowAll coeffs is bds'
                (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
          = linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
              false b doms from rfl] at h
        obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
        -- the coverage (with integrality from the satisfaction)
        have hcov : LinCover is bds doms a :=
          linExtract_cover is doms bds a hex hlen hget
            (fun k hk => by
              -- integrality: the constraint's satisfaction gives
              -- dotProduct = some b, which forces every listed value
              -- to be an integer
              have hsat' := linLe_LinSat.mp hsat
              rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
                  = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                      = some d ∧ d ≤ b) from rfl] at hsat'
              obtain ⟨d, hd, hle⟩ := hsat'
              have hint := dotProduct_some_int (intVals coeffs)
                (is.map (fun i => a[i]!)) d hd
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                  simp only [List.length_map]] at hint
              obtain ⟨p, hp⟩ := hint k hk
              rw [map_getElem!_in_bounds a is k hk] at hp
              exact ⟨p, hp⟩)
        -- the shape premise coeffs.length = is.length is needed; derive
        -- from the extract's structure (bds has is' length) — for now the
        -- honest constraint: the propagator is only sound on aligned shapes,
        -- which the extract guarantees when it returns some bds
        have hshape : coeffs.length = is.length := hshape
        have hshape2 : is.length = bds.length :=
          linExtract_length is doms bds hex
        exact linNarrowAll_mem coeffs.length 0 coeffs is bds
          (linTotalMin coeffs bds) (linTotalMax coeffs bds) false b doms
          (by simp) (Nat.zero_le _) hshape hshape2
          rfl rfl doms' a h hlen hget
          (linLe_LinSat.mp hsat) hcov
    · -- mismatched shape: the propagator returned contradiction
      rw [if_neg hshape] at h
      exact absurd h (by simp)
  · -- subset: each narrowed slot is a filter of the original
    intro doms doms' h
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none => rw [hex] at h; exact absurd h (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) false b doms from rfl] at h
          exact linNarrowAll_subset coeffs is bds
            (linTotalMin coeffs bds) (linTotalMax coeffs bds) false b doms doms' h
    · rw [if_neg hshape] at h; exact absurd h (by simp)
  · -- contradiction soundness
    intro doms h a ha hsat
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none =>
          -- the extract failed: some listed slot's domain lacks integers
          -- (domMin/domMax returned none). The satisfying assignment's
          -- value at that slot must be an integer in the domain (the dot
          -- product exists), and any integer member makes domMin some —
          -- contradiction.
          -- locate the failing position
          -- domMin and domMax agree on existence: both scan the same
          -- domain for integers
          have hagree : ∀ (d : List Value),
              (domMin d).isSome = true → (domMax d).isSome = true := by
            intro d
            induction d with
            | nil => intro h; exact absurd h (by simp [domMin])
            | cons v vs ih =>
                intro h
                cases hv : v with
                | int p =>
                    have : domMax (Value.int p :: vs)
                        = maxOpt (domMax vs) p := rfl
                    rw [this]
                    cases hdp : domMax vs with
                    | none => rfl
                    | some m => rfl
                | bool p =>
                    subst hv
                    have heq : domMax (Value.bool p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.bool p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | setOfInt p =>
                    subst hv
                    have heq : domMax (Value.setOfInt p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.setOfInt p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | array p =>
                    subst hv
                    have heq : domMax (Value.array p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.array p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
          have hfail : ∃ k, k < is.length ∧
              (domMin (getSlot doms (is[k]!))).isNone = true := by
            -- induction over the extract's recursion
            have hexrec : ∀ (js : List Nat),
                linExtract js doms = none →
                ∃ k, k < js.length ∧ (domMin (getSlot doms (js[k]!))).isNone = true := by
              intro js
              induction js with
              | nil => intro h; exact absurd h (by simp [linExtract])
              | cons j js' ih =>
                  intro h
                  rw [linExtract] at h
                  cases hmin : domMin (getSlot doms j) with
                  | none =>
                      rw [hmin] at h
                      refine ⟨0, by simp, ?_⟩
                      rw [show (j :: js')[0]! = j from rfl, hmin]
                      rfl
                  | some lo =>
                      rw [hmin] at h
                      cases hmax : domMax (getSlot doms j) with
                      | none =>
                          -- domMax none with domMin some is impossible
                          exfalso
                          have hcontr : (domMax (getSlot doms j)).isSome = true :=
                            hagree (getSlot doms j) (by rw [hmin]; rfl)
                          rw [hmax] at hcontr
                          exact absurd hcontr (by simp)
                      | some hi =>
                          -- the match reduces: Option.map f (linExtract js' doms);
                          -- the outer = none forces the tail extract = none
                          rw [hmax] at h
                          -- reduce the match to the Option.map form
                          have hmap : (match some lo, some hi with
                              | some lo, some hi =>
                                Option.map (fun bds => (lo, hi) :: bds) (linExtract js' doms)
                              | x, x_1 => none) = none := h
                          rw [Option.map_eq_none_iff] at hmap
                          obtain ⟨k, hk, hnone⟩ := ih hmap
                          refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
                          rw [show (j :: js')[k + 1]! = js'[k]! from rfl]
                          exact hnone
            exact hexrec is hex
          obtain ⟨k, hk, hnone⟩ := hfail
          -- the assignment's value at is[k]! is an integer in the domain
          have hsat' := linLe_LinSat.mp hsat
          rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
              = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                  = some d ∧ d ≤ b) from rfl] at hsat'
          obtain ⟨d, hd, hle⟩ := hsat'
          have hint := dotProduct_some_int (intVals coeffs)
            (is.map (fun i => a[i]!)) d hd k
            (by
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                simp only [List.length_map]]
              exact hk)
          obtain ⟨p, hp⟩ := hint
          rw [map_getElem!_in_bounds a is k hk] at hp
          -- the value is in the domain (allAssigns)
          obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
          have hmem : Value.int p ∈ getSlot doms (is[k]!) := by
            obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
            by_cases halt : is[k]! < a.length
            · -- in range: the allAssigns spec gives the membership
              have hsome : a[is[k]!]? = some (a[is[k]!]!) := by
                have hsome' : a[is[k]!]? = some a[is[k]!] :=
                  List.getElem?_eq_getElem halt
                rw [hsome']
                show some a[is[k]!] = some a[is[k]!]!
                rw [show a[is[k]!]! = a[is[k]!] from by
                  rw [List.getElem!_eq_getElem?_getD, hsome', Option.getD_some]]
              have hv : a[is[k]!]! ∈ getSlot doms (is[k]!) :=
                hget2 (is[k]!) _ hsome
              rw [hp] at hv
              exact hv
            · -- out of range: a[is[k]!]! = default (.bool false), but
              -- dotProduct_some_int's witness says it is .int p —
              -- contradiction
              exfalso
              have hdef : a[is[k]!]! = (default : Value) := by
                rw [List.getElem!_eq_getElem?_getD,
                  List.getElem?_eq_none_iff.mpr (by omega)]
                rfl
              rw [hdef] at hp
              exact nomatch hp
          -- domMin of a domain with an integer member is some
          obtain ⟨m, hm, _⟩ := domMin_of_mem hmem
          have hnone' : domMin (getSlot doms is[k]!) = none := by
            cases hdp : domMin (getSlot doms is[k]!) with
            | none => rfl
            | some v =>
                rw [hdp] at hnone
                exact absurd hnone (by simp)
          rw [hnone'] at hm
          exact absurd hm (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) false b doms from rfl] at h
          -- the assignment's spec (length + membership)
          obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
          -- the satisfaction and the integrality hint, derived once
          have hsat' := linLe_LinSat.mp hsat
          have hint : ∀ k, k < is.length →
              ∃ p, a[is[k]!]! = Value.int p := by
            intro k hk
            rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
                = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                    = some d ∧ d ≤ b) from rfl] at hsat'
            obtain ⟨d, hd, hle⟩ := hsat'
            have hmaplen2 : (is.map (fun i => a[i]!)).length = is.length := by
              simp only [List.length_map]
            have hint2 := dotProduct_some_int (intVals coeffs)
              (is.map (fun i => a[i]!)) d hd k (by rw [hmaplen2]; exact hk)
            obtain ⟨p, hp⟩ := hint2
            rw [map_getElem!_in_bounds a is k hk] at hp
            exact ⟨p, hp⟩
          -- the first-contradiction analysis: an induction over the run
          have hrun : ∀ (n : Nat) (k : Nat) (doms2 : List (List Value)),
              coeffs.length - k = n → k ≤ coeffs.length →
              linNarrowAll (List.drop k coeffs) (List.drop k is)
                (List.drop k bds) (linTotalMin coeffs bds) (linTotalMax coeffs bds)
                false b doms2 = .contradiction →
              LinCover is bds doms2 a →
              LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b →
              False := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              intro k doms2 hmeasure hkle h hcov' hsat'
              cases hdcs : List.drop k coeffs with
              | nil =>
                  -- no terms: the run returns .narrowed, not .contradiction
                  have hdcslen : (List.drop k coeffs).length = coeffs.length - k := by simp
                  rw [hdcs, List.length_nil] at hdcslen
                  have hisnil : List.drop k is = [] := by
                    cases his2 : List.drop k is with
                    | nil => rfl
                    | cons x xs =>
                        exfalso
                        have h1 : (x :: xs).length = (List.drop k is).length := by
                          rw [his2]
                        have h1' : (List.drop k is).length = is.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : coeffs.length = is.length := hshape
                        omega
                  have hbdsnil : List.drop k bds = [] := by
                    cases hbs2 : List.drop k bds with
                    | nil => rfl
                    | cons y ys =>
                        exfalso
                        have h1 : (y :: ys).length = (List.drop k bds).length := by
                          rw [hbs2]
                        have h1' : (List.drop k bds).length = bds.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : is.length = bds.length :=
                          linExtract_length is doms bds hex
                        omega
                  rw [hdcs, hisnil, hbdsnil] at h
                  exact absurd h (by simp [linNarrowAll])
              | cons c csuff =>
                  cases his : List.drop k is with
                  | nil =>
                      exfalso
                      have h1 : (List.drop k is).length = is.length - k := by simp
                      have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                      rw [his, List.length_nil] at h1
                      rw [hdcs, List.length_cons] at h2
                      omega
                  | cons idx isuff =>
                      cases hbs : List.drop k bds with
                      | nil =>
                          exfalso
                          have h1 : (List.drop k bds).length = bds.length - k := by simp
                          have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                          rw [hbs, List.length_nil] at h1
                          rw [hdcs, List.length_cons] at h2
                          have h3 : is.length = bds.length :=
                            linExtract_length is doms bds hex
                          omega
                      | cons bd bsuff =>
                          have hck : coeffs[k]! = c := by
                            have hlt : k < coeffs.length := by
                              have h1 : (List.drop k coeffs).length = coeffs.length - k := by simp
                              rw [hdcs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Int) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop coeffs k hlt, hdcs]
                            rfl
                          have hidx : is[k]! = idx := by
                            have hlt : k < is.length := by
                              have h1 : (List.drop k is).length = is.length - k := by simp
                              rw [his, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Nat) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop is k hlt, his]
                            rfl
                          have hbd : bds[k]! = bd := by
                            have hlt : k < bds.length := by
                              have h1 : (List.drop k bds).length = bds.length - k := by simp
                              rw [hbs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List (Int × Int)) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD (0, 0) := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop bds k hlt, hbs]
                            rfl
                          have hklt : k < is.length := by
                            have h1 : (List.drop k is).length = is.length - k := by simp
                            rw [his, List.length_cons] at h1
                            omega
                          -- unfold one step
                          rw [hdcs, his, hbs] at h
                          rw [linNarrowAll] at h
                          by_cases hcond : (linNarrowLe c b
                              (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                              (getSlot doms2 idx)).isEmpty = true
                          · -- the head filter emptied: the value passes by
                            -- lin_head_filter_pass — contradiction with empty
                            rw [show (if false = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_neg (by decide)] at h
                            rw [if_pos hcond] at h
                            obtain ⟨pk, hvpk, hmemf⟩ :=
                              lin_head_filter_pass (ocs := coeffs) (ois := is)
                                (obds := bds)
                                (totalMin := linTotalMin coeffs bds)
                                (totalMax := linTotalMax coeffs bds)
                                (eq := false) (b := b) (doms := doms2) (a := a) (k := k)
                                (c := c) (idx := idx) (bd := bd)
                                hshape (linExtract_length is doms bds hex)
                                rfl rfl hsat' hcov' hklt hck hidx hbd
                            -- hmemf : a[idx]! ∈ the filter, which is empty
                            -- (the split's branch condition is the filter's
                            --  isEmpty = true)
                            have hfnil : (linNarrowLe c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (getSlot doms2 idx)) = [] := by
                              rw [← List.isEmpty_iff]
                              exact hcond
                            rw [hfnil] at hmemf
                            exact absurd hmemf (by simp)
                          · -- the filter kept values: the run recursed —
                            -- the contradiction comes from the tail
                            -- h (with the inner if already reduced by the
                            -- rw [linNarrowAll]) is the Prop-if; hcond
                            -- selects the else branch
                            -- reduce the inner `if true = true` and select
                            -- the else branch via hcond
                            rw [show (if false = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_neg (by decide)] at h
                            rw [if_neg hcond] at h
                            have hcsuff : csuff = List.drop (k+1) coeffs := by
                              have hdrop : List.drop (k+1) coeffs
                                  = (List.drop k coeffs).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hdcs]
                              rfl
                            rw [hcsuff] at h
                            rw [show isuff = List.drop (k+1) is from by
                              have hdrop : List.drop (k+1) is
                                  = (List.drop k is).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, his]
                              rfl,
                              show bsuff = List.drop (k+1) bds from by
                              have hdrop : List.drop (k+1) bds
                                  = (List.drop k bds).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hbs]
                              rfl] at h
                            have hn1 : coeffs.length - (k + 1) < n := by omega
                            -- the tail: recurse with the written domains
                            -- and the original coverage (the written slot
                            -- passes by lin_head_filter_pass, the master
                            -- lemma's interval derivation)
                            exact ih (coeffs.length - (k + 1)) hn1 (k + 1)
                              (setSlot doms2 idx (linNarrowLe c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (getSlot doms2 idx)))
                              (by omega) (by omega) h
                              (by
                                intro mm hmm
                                obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov' mm hmm
                                by_cases hne : is[mm]! = idx
                                · rw [hne] at hmemv hvp
                                  have hmemint : Value.int p' ∈ getSlot doms2 idx := by
                                    rw [← hvp]
                                    exact hmemv
                                  obtain ⟨pk2, hvp2, hmemf2⟩ :=
                                    lin_head_filter_pass (ocs := coeffs)
                                      (ois := is) (obds := bds)
                                      (totalMin := linTotalMin coeffs bds)
                                      (totalMax := linTotalMax coeffs bds)
                                      (eq := false) (b := b) (doms := doms2)
                                      (a := a) (k := k) (c := c) (idx := idx)
                                      (bd := bd) hshape
                                      (linExtract_length is doms bds hex)
                                      rfl rfl (linLe_LinSat.mp hsat) hcov' hklt
                                      hck hidx hbd
                                  rw [hne]
                                  rw [getSlot_setSlot_eq doms2 _ idx
                                    (lt_length_of_mem_getSlot doms2 idx
                                      (Value.int p') hmemint)]
                                  -- p' = pk2: both are the integer of a[idx]!
                                  have hp'pk : p' = pk2 := by
                                    have h1 : Value.int p' = Value.int pk2 :=
                                      hvp.symm.trans hvp2
                                    injection h1
                                  rw [hp'pk] at hlo' hhi'
                                  exact ⟨hmemf2, pk2, hvp2, hlo', hhi'⟩
                                · rw [getSlot_setSlot_of_ne doms2 _ idx _ hne]
                                  exact ⟨hmemv, p', hvp, hlo', hhi'⟩)
                              (by exact linLe_LinSat.mp hsat)
          exact hrun coeffs.length 0 doms (by simp) (Nat.zero_le _) h
            (linExtract_cover is doms bds a hex hlen hget hint)
            (linLe_LinSat.mp hsat)
    · -- mismatched shape: the constraint is unsatisfiable (the dot
      -- product needs equal lengths), so contradiction is sound
      rw [if_neg hshape] at h
      obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
      have hsat' := linLe_LinSat.mp hsat
      rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
          = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
              = some d ∧ d ≤ b) from rfl] at hsat'
      obtain ⟨d, hd, hle⟩ := hsat'
      rw [dotProduct_mismatch hshape] at hd
      exact absurd hd (by simp)




end LeanFzn.Solver.Propagation.DomainFiltering

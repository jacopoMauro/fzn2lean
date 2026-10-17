/-
File: LeanFzn/Solver/Propagation/Propagate.lean

Purpose:
  Integer/CP propagation with explanations (PLAN.md L0.3). Every deduction
  is a signed order literal (`s ≤ k` or `s > k`) together with a *nogood*:
  a clause `[D, ¬C₁, …, ¬Cₙ]` where `D` is the implied literal and the
  `Cᵢ` are bound facts that the current trail already asserts. The clause
  is valid whenever `constraint ∧ C₁ ∧ … ∧ Cₙ → D` holds over the integers
  — no domains involved — so the same clause later serves as a sound reason
  on the trail and as a learnable clause after backjumping.

  Example (`x + y = z`, slots `i j k`, deduction `x ≥ lo := minZ − maxY`):
  the clause is `[x > lo−1, z ≤ minZ−1, y > maxY]`. Under `x + y = z`,
  `z ≥ minZ` and `y ≤ maxY` force `x = z − y ≥ minZ − maxY = lo`, so a
  point falsifying every literal would violate the constraint: the clause
  is integer-valid. On the current trail `z ≥ minZ` and `y ≤ maxY` are
  facts, so the two cause literals are trail-false and the clause is unit
  in `x > lo−1`.

  Bound-cause hygiene: the engine keeps the invariant that every domain
  bound of a slot equals the tightest trail-implied bound (root facts pin
  the initial integer-view extrema of every int/bool slot, and domains
  change only through enqueued order literals — see
  `LeanFzn.Solver.UIP.Engine.enqueueNorm`). Hence a cause literal built from a domain
  extremum always has its exact witnessing entry on the trail, which is
  what conflict analysis resolves against.

Dependencies:
  - LeanFzn.Solver.Propagation.Operations: the `PropagationResult` interface.

DAG:
  LeanFzn.Solver.Propagation.Operations -> LeanFzn.Solver.Propagation.Propagate -> LeanFzn.Solver.Reference.Engine
-/

import LeanFzn.Solver.Propagation.Operations
import LeanFzn.Solver.Propagation.DomainConstraints
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation

/-! ## Domain views

Propagators operate on the integer view of slot domains. Booleans count
as 0/1 so one bound recipe serves both sorts. -/

/-- The integer values of a slot domain (Booleans count as 0/1). -/
def domInts (d : List Value) : List Int :=
  d.filterMap fun v => match v with
    | .int i => some i
    | .bool b => some (if b then 1 else 0)
    | _ => none

/-- Minimum integer of a domain, if any. -/
def domMinI (d : List Value) : Option Int :=
  domInts d |>.foldl (fun acc i => match acc with
    | none => some i
    | some c => some (minI c i)) none

/-- Maximum integer of a domain, if any. -/
def domMaxI (d : List Value) : Option Int :=
  domInts d |>.foldl (fun acc i => match acc with
    | none => some i
    | some c => some (maxI c i)) none

/-! ## Bound narrowing with explanations -/

/-- Attempt to raise slot `s`'s lower bound to `lo`. `ng` is the
    constraint-valid nogood whose head literal is `s > lo−1`. Reports a
    conflict when the current domain lies entirely below `lo` (the nogood
    is then falsified by the trail), the implied literal `s > lo − 1` when
    the bound actually tightens, and `.stable` otherwise. -/
def narrowLo (st : State) (s : Nat) (lo : Int) (ng : Clause) :
    PropagationResult :=
  match domMinI (st.domains.getD s []), domMaxI (st.domains.getD s []) with
  | some mn, some mx =>
      if mx < lo then .conflict ng
      else if decide (mn < lo) then
        .implied (negLe s (lo - 1)) { clause := ng }
      else .stable
  | _, _ => .stable

/-- Attempt to lower slot `s`'s upper bound to `hi`, with the
    constraint-valid nogood `ng` whose head literal is `s ≤ hi`. -/
def narrowHi (st : State) (s : Nat) (hi : Int) (ng : Clause) :
    PropagationResult :=
  match domMinI (st.domains.getD s []), domMaxI (st.domains.getD s []) with
  | some mn, some mx =>
      if mn > hi then .conflict ng
      else if decide (hi < mx) then
        .implied (posLe s hi) { clause := ng }
      else .stable
  | _, _ => .stable

/-- First non-`stable` result of a list (left-biased). -/
def firstEvent : List PropagationResult → PropagationResult
  | [] => .stable
  | .stable :: rs => firstEvent rs
  | r :: _ => r

/-! ## Constraint propagators

Each propagator narrows one slot's bounds using the other slots' domain
extrema and attaches its nogood. The validity obligation per family
(the heart of the future `enqueue_implied_preserves` proof) is recorded
with each definition. -/

/-- `int_plus`-style: `x + y = z` over slots `i j k`; bounds used:
    `x ∈ [xi',xi]`, `y ∈ [yj',yj]`, `z ∈ [zk',zk]`.

    Nogoods (each integer-valid under `x + y = z`, causes in brackets):
    * `x ≥ zk'−yj` (causes `z ≥ zk'`, `y ≤ yj`);
    * `x ≤ zk−yj'` (causes `z ≤ zk`, `y ≥ yj'`);
    * `y ≥ zk'−xi` (causes `z ≥ zk'`, `x ≤ xi`);
    * `y ≤ zk−xi'` (causes `z ≤ zk`, `x ≥ xi'`);
    * `z ≥ xi'+yj'` (causes `x ≥ xi'`, `y ≥ yj'`);
    * `z ≤ xi+yj` (causes `x ≤ xi`, `y ≤ yj`). -/
def propPlus (st : State) (i j k : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMinI (st.domains.getD j []), domMaxI (st.domains.getD j []),
        domMinI (st.domains.getD k []), domMaxI (st.domains.getD k []) with
  | some xi', some xi, some yj', some yj, some zk', some zk =>
      firstEvent
        [ -- x ≥ zk' − yj  (causes: z ≥ zk', y ≤ yj)
          narrowLo st i (zk' - yj)
            [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj]
        , -- x ≤ zk − yj'  (causes: z ≤ zk, y ≥ yj')
          narrowHi st i (zk - yj')
            [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)]
        , -- y ≥ zk' − xi  (causes: z ≥ zk', x ≤ xi)
          narrowLo st j (zk' - xi)
            [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi]
        , -- y ≤ zk − xi'  (causes: z ≤ zk, x ≥ xi')
          narrowHi st j (zk - xi')
            [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)]
        , -- z ≥ xi' + yj'  (causes: x ≥ xi', y ≥ yj')
          narrowLo st k (xi' + yj')
            [negLe k (xi' + yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)]
        , -- z ≤ xi + yj  (causes: x ≤ xi, y ≤ yj)
          narrowHi st k (xi + yj)
            [posLe k (xi + yj), negLe i xi, negLe j yj]
        ]
  | _, _, _, _, _, _ => .stable

/-- `int_le`-style: `x ≤ y` over slots `i j`.

    Nogoods: `x ≤ yj` (cause `y ≤ yj`); `y ≥ xi'` (cause `x ≥ xi'`). -/
def propLe (st : State) (i j : Nat) : PropagationResult :=
  match domMaxI (st.domains.getD j []), domMinI (st.domains.getD i []) with
  | some yj, some xi' =>
      firstEvent
        [ narrowHi st i yj [posLe i yj, negLe j yj]
        , narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]
        ]
  | _, _ => .stable

/-- `int_lt`-style: `x < y` over slots `i j` (equivalent to
    `x ≤ y − 1`).

    Nogoods: `x ≤ yj−1` (cause `y ≤ yj`); `y ≥ xi'+1` (cause `x ≥ xi'`). -/
def propLt (st : State) (i j : Nat) : PropagationResult :=
  match domMaxI (st.domains.getD j []), domMinI (st.domains.getD i []) with
  | some yj, some xi' =>
      firstEvent
        [ narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj]
        , narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]
        ]
  | _, _ => .stable

/-- `int_eq`-style: `x = y` over slots `i j`; bounds
    `x ∈ [mi,Mi]`, `y ∈ [mj,Mj]`.

    Nogoods: `x ≥ mj` (cause `y ≥ mj`); `x ≤ Mj` (cause `y ≤ Mj`); and
    the two symmetric deductions on `y` (causes `x ≥ mi`, `x ≤ Mi`). -/
def propEq (st : State) (i j : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMinI (st.domains.getD j []), domMaxI (st.domains.getD j []) with
  | some mi, some Mi, some mj, some Mj =>
      firstEvent
        [ narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)]
        , narrowHi st i Mj [posLe i Mj, negLe j Mj]
        , narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)]
        , narrowHi st j Mi [posLe j Mi, negLe i Mi]
        ]
  | _, _, _, _ => .stable

/-- The single integer of a singleton domain, if it is one. -/
def domSingletonI (d : List Value) : Option Int :=
  match d with
  | [.int c] => some c
  | [.bool b] => some (if b then 1 else 0)
  | _ => none

/-- Keep only domain values whose integer view is `≤ k`. -/
def domFilterToMax (k : Int) (d : List Value) : List Value :=
  d.filter fun v =>
    match v with
    | .int p => decide (p ≤ k)
    | .bool b => decide ((if b then 1 else 0) ≤ k)
    | _ => true

/-- Keep only domain values whose integer view is `≥ k`. -/
def domFilterToMin (k : Int) (d : List Value) : List Value :=
  d.filter fun v =>
    match v with
    | .int p => decide (k ≤ p)
    | .bool b => decide (k ≤ (if b then 1 else 0))
    | _ => true

/-- Does the domain contain a value whose integer view is exactly `k`?
    (Sets/arrays have no view, so they never contain `k`.) -/
def domContainsI (k : Int) (d : List Value) : Bool :=
  d.any fun v =>
    match v with
    | .int p => decide (p = k)
    | .bool b => decide ((if b then 1 else 0) = k)
    | _ => false

/-- The value-removal gate: every value of `d` whose integer view is
    `c` is RAW-equal to `x`. When the singleton `x` itself views to
    `c`, removing `c` from `d` is sound at every fitting solution of
    the raw disequality: a diverging read at `d`'s slot would view to
    `c`, hence BE `x` raw — the pinned value — contradicting the
    raw-`neSlot` disequality. -/
def domNeGate (x : Value) (c : Int) (d : List Value) : Bool :=
  d.all fun v =>
    match Value.intView v with
    | some p => if p = c then Value.eqB v x else true
    | none => true

/-- The explained conflict clause of a raw `x ≠ y` whose two sides are both
    pinned to the same value `x`: the integer shape reports `[x ≠ c, y ≠ c]`,
    the Boolean shape `[x = ¬b, y = ¬b]` (both literals are in normal form and
    both are falsified by the pins). Any other shape reports no clause. -/
def neConflictClause (i j : Nat) (x : Value) : Clause :=
  match x with
  | .int c => [posNe i c, posNe j c]
  | .bool b => [posBool i (!b), posBool j (!b)]
  | _ => []

/-- Two values of the same sort (both integer or both Boolean): on such a
    pair the integer view is injective, so view equality is raw equality. -/
def SortAgree (x y : Value) : Prop :=
  ((∃ k : Int, x = .int k) ∧ (∃ k : Int, y = .int k)) ∨
  ((∃ b : Bool, x = .bool b) ∧ (∃ b : Bool, y = .bool b))

/-- The assignment `a` is FAITHFUL to the domain list `doms`: at every slot of
    `doms` it reads a value that has an integer view and that agrees in sort
    with every value of the slot's domain. This is the shape premise under
    which the explained `propNe`/`propAllDiffLCG` conflict clauses are
    entailed (a mixed-sort raw/view collision is the only way a raw
    disequality can hold while both view-literals of the clause are false). -/
def FrameFaithful (doms : List Domain) (a : Assignment) : Prop :=
  ∀ i, i < doms.length → ∃ y, a[i]? = some y ∧ y.intView ≠ none ∧
    ∀ x ∈ doms.getD i [], SortAgree x y

/-- Pointwise sub-domains: same slot count, every value of a slot of `d'` is a
value of the same slot of `d`. -/
def DomSub (d' d : List (List Value)) : Prop :=
  d'.length = d.length ∧ ∀ i v, v ∈ d'.getD i [] → v ∈ d.getD i []

theorem DomSub.trans {d₁ d₂ d₃ : List (List Value)}
    (h12 : DomSub d₁ d₂) (h23 : DomSub d₂ d₃) : DomSub d₁ d₃ :=
  ⟨h12.1.trans h23.1, fun i v hv => h23.2 i v (h12.2 i v hv)⟩

theorem DomSub.refl (d : List (List Value)) : DomSub d d := ⟨rfl, fun _ _ h => h⟩

/-- Every domain of the box is int-shaped or bool-shaped throughout. -/
def DomsShapeTyped (pd : List (List Value)) : Prop :=
  ∀ d ∈ pd, (∀ v ∈ d, ∃ k : Int, v = .int k) ∨ (∀ v ∈ d, ∃ b : Bool, v = .bool b)

theorem getD_mem_of_lt {l : List (List Value)} {i : Nat} (h : i < l.length) :
    l.getD i [] ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- **Faithfulness from the problem's shape**: a solution of an int-viewed,
shape-typed box is faithful to every pointwise sub-domain list. -/
theorem frameFaithful_of_domSub {pd doms : List (List Value)} {a : Assignment}
    (hview : ∀ d ∈ pd, ∀ v ∈ d, Value.intView v ≠ none)
    (hshape : DomsShapeTyped pd) (hfit : a.Fits pd) (hsub : DomSub doms pd) :
    FrameFaithful doms a := by
  intro i hi
  have hipd : i < pd.length := by rw [← hsub.1]; exact hi
  have hia : i < a.length := by rw [hfit.1]; exact hipd
  have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hia
  have hymem : a[i] ∈ pd.getD i [] := hfit.2 i _ hread
  refine ⟨a[i], hread, hview _ (getD_mem_of_lt hipd) _ hymem, ?_⟩
  intro x hx
  have hxpd := hsub.2 i x hx
  rcases hshape _ (getD_mem_of_lt hipd) with hint | hbool
  · obtain ⟨k1, hk1⟩ := hint x hxpd
    obtain ⟨k2, hk2⟩ := hint _ hymem
    exact Or.inl ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
  · obtain ⟨k1, hk1⟩ := hbool x hxpd
    obtain ⟨k2, hk2⟩ := hbool _ hymem
    exact Or.inr ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩

/-- The Boolean-pin disjunct of a `propNe` reason on slot `s` for the integer
    `c`: `s = B` when a Boolean `B` views to `c` (`c ∈ {0,1}`), else a harmless
    duplicate of the pivot slot `p`'s bound cause `p > c` (no Boolean views to `c`). -/
def neBoolLit (p s : Nat) (c : Int) : Literal :=
  if c = 0 ∨ c = 1 then posBool s (decide (c = 1)) else negLe p c

/-- Integer-shaped raw values. The value-removal arm of `propNe` fires only on
    an integer pin: a Boolean pin `x = B` would put the frame-TRUE literal
    `x = B` into the reason clause, so Boolean pins propagate only through
    the (frame-false) conflict clause once both sides are pinned. -/
def isIntValue : Value → Bool
  | .int _ => true
  | _ => false

/-- `int_ne`-style: `x ≠ y` over slots `i j` (the RAW disequality).
    Sound behaviours:

    * when BOTH sides are singletons, a direct conflict is reported
      if the values are raw-equal (the constraint is violated), else
      nothing to do; the reported clause is the EXPLAINED
      `neConflictClause` (`[x ≠ c, y ≠ c]`, Boolean shape
      `[x = ¬b, y = ¬b]`);
    * when exactly one side is a singleton `x` with integer view
      `c` and the other side's domain still CONTAINS `x` (multi-value)
      while every value of it that views to `c` IS `x` raw (the
      `domNeGate`), the value-removal literal `posNe` is implied
      with the nogood `[y ≠ c, x ≤ c−1, x > c, x = B, y = B]` (B
      the Boolean viewing to `c`).

    The nogood is valid under the raw `x ≠ y` at every assignment
    whose two reads have integer views: if `x`'s view is `c` (the two
    adjacent-bound causes false), then `x`'s raw value is `.int c`
    or `.bool B`; in the Boolean case the `x = B` disjunct is true;
    in the integer case a `y` reading view `c` is `.int c` (raw
    equal — the disequality excludes it, so `y ≠ c` is true) or
      `.bool B` (the `y = B` disjunct is true).

    The conflict compares the RAW singleton values (`Value.eqB`):
    `int_ne` means raw inequality. The VALUE-REMOVAL deduction is
    view-based but gated on the raw correspondence (`domNeGate`), so
    it never fires across a raw/view shape mismatch. -/
def propNe (st : State) (i j : Nat) : PropagationResult :=
  match st.domains.getD i [], st.domains.getD j [] with
  | [x], [y] => if x.eqB y then .conflict (neConflictClause i j x) else .stable
  | [x], dy =>
      match domSingletonI [x] with
      | some c =>
          if valueMemB x dy && domNeGate x c dy && isIntValue x then
            .implied (posNe j c) { clause :=
              [posNe j c, posLe i (c - 1), negLe i c,
                neBoolLit i i c, neBoolLit i j c] }
          else .stable
      | none => .stable
  | dx, [y] =>
      match domSingletonI [y] with
      | some c =>
          if valueMemB y dx && domNeGate y c dx && isIntValue y then
            .implied (posNe i c) { clause :=
              [posNe i c, posLe j (c - 1), negLe j c,
                neBoolLit j j c, neBoolLit j i c] }
          else .stable
      | none => .stable
  | _, _ => .stable

/-- `int_lin_le`-style: `Σ cₜ·xₜ ≤ b`. For each slot `m` with a `±1`
    coefficient, the classic bound deduction over ALL the other terms:

    * `+1` on `x_m`: `x_m ≤ b − min Σ_{t≠m} cₜ·xₜ`, causes are the
      min-contribution events of the other terms;
    * `−1` on `x_m`: `x_m ≥ min Σ_{t≠m} cₜ·xₜ − b`, dually (the MIN
      sum of the rest, not the max: from `−x_m ≤ b − Σ_{t≠m} cₜxₜ`,
      the tightest valid lower bound on `x_m` takes the rest's min).

    The first tightening across all `±1` slots is reported. The cause
    literals are the falsified bound events of the other terms at
    their extreme contributions: a term contributing its min `l`
    (reached at `xₜ`'s min when `cₜ = 1`, at `xₜ`'s max when
    `cₜ = −1`, so the falsified event is `xₜ < l` resp. `xₜ > −l`);
    a term contributing its max `h` dually. -/
def propLinLe (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    PropagationResult :=
  let deduce (m : Nat) (c : Int) (rest : List (Int × Nat)) :
      PropagationResult :=
    -- the MIN-contribution of each other term: `ct·mn` for positive
    -- coefficients, `ct·mx` for negative ones (ct < 0: smallest at max)
    let terms : List (Nat × Int × Int) := rest.filterMap fun p =>
      match p with
      | (ct, t) =>
          match domMinI (st.domains.getD t []), domMaxI (st.domains.getD t []) with
          | some mn, some mx =>
              if ct ≥ 0 then some (t, ct, ct * mn) else some (t, ct, ct * mx)
          | _, _ => none
    -- the MAX-contribution of each other term: dually
    let termsH : List (Nat × Int × Int) := rest.filterMap fun p =>
      match p with
      | (ct, t) =>
          match domMinI (st.domains.getD t []), domMaxI (st.domains.getD t []) with
          | some mn, some mx =>
              if ct ≥ 0 then some (t, ct, ct * mx) else some (t, ct, ct * mn)
          | _, _ => none
    let loRest := terms.foldl (fun acc t => match acc, t with
      | none, (_, _, l) => some l
      | some a, (_, _, l) => some (a + l)) none
    let hiRest := termsH.foldl (fun acc t => match acc, t with
      | none, (_, _, h) => some h
      | some a, (_, _, h) => some (a + h)) none
    -- cause literals: the falsified bound events of the other terms.
    -- min contribution l: cₜ=1 → reached at xₜ's min (event xₜ < l,
    -- clause carries xₜ ≥ l, i.e. negation xₜ ≤ l−1); cₜ=−1 →
    -- l = −mxₜ reached at xₜ's max (event xₜ > mxₜ, clause carries
    -- xₜ ≤ mxₜ = −l).
    let causeOfMin (t : Nat × Int × Int) : Option Literal :=
      match t with
      | (slot, ct, l) =>
          if ct == 1 then some (posLe slot (l - 1))
          else if ct == -1 then some (negLe slot (-l))
          else none
    let causeOfMax (t : Nat × Int × Int) : Option Literal :=
      match t with
      | (slot, ct, h) =>
          if ct == 1 then some (negLe slot h)
          else if ct == -1 then some (posLe slot (-h - 1))
          else none
    match loRest, hiRest, c with
    | some lr, _, 1 =>
        let hi := b - lr
        narrowHi st m hi ([posLe m hi] ++ terms.filterMap causeOfMin)
    | _, _, -1 =>
        -- the valid lower bound on xₘ: ≥ (min of the rest) − b
        let lo := loRest.getD 0 - b
        match loRest with
        | some _ => narrowLo st m lo ([negLe m (lo - 1)] ++ terms.filterMap causeOfMin)
        | none => .stable
    | _, _, _ => .stable
  let rec sweep (ps : List ((Int × Nat) × Nat)) (idx : Nat) :
      PropagationResult :=
    match ps with
    | [] => .stable
    | ((c, m), i) :: rest =>
        -- deduce over ALL other entries, not just the suffix: drop
        -- exactly the CURRENT pair (by position), keeping same-slot
        -- entries (a duplicated slot's other coefficients belong to
        -- "the rest" — filtering by slot value would wrongly remove
        -- them and produce false conflicts on `x − x + y ≤ b` shapes)
        let others := ((coeffs.zip is).zipIdx.filter
          (fun p => p.2 != i)).map (·.1)
        match deduce m c others with
        | .stable => sweep rest (idx + 1)
        | r => r
  -- a length mismatch would silently truncate the pairing; the
  -- compiled shape (linLe coeffs is b from extractConstraint) always
  -- has equal lengths (the `coeffs.length == is.length` gate)
  match coeffs.zip is with
  | [] => .stable
  | ps => sweep (ps.zipIdx) 0

/-- `int_le(x, c)` style: slot `i` must be `≤ c`. Conflict when the
    domain's minimum already exceeds `c` (the unit nogood `x ≤ c` is
    then violated by every domain value); implied literal `posLe i c`
    (narrow the upper bound to `c`) when only the maximum exceeds it;
    `.stable` when the bound is already tight. The reason clause is
    the unit nogood `[posLe i c]`, entailed by the constraint
    `.leConstHi i c` alone. -/
def propLeConstHi (st : State) (i : Nat) (c : Int) : PropagationResult :=
  narrowHi st i c [posLe i c]

/-- `int_le(c, x)` style: slot `i` must be `≥ c`. Conflict when the
    domain's maximum is already below `c`; implied literal `negLe i
    (c−1)` (i.e. `x > c−1`, narrowing the lower bound to `c`) when
    only the minimum is below it. The reason clause is the unit nogood
    `[negLe i (c−1)]`, entailed by the constraint `.leConstLo i c`
    alone. -/
def propLeConstLo (st : State) (i : Nat) (c : Int) : PropagationResult :=
  narrowLo st i c [negLe i (c - 1)]

/-- `int_lt(x, c)` style: slot `i` must be `< c`, i.e. `≤ c − 1`.
    Conflict when the domain's minimum is already `≥ c` (the unit
    nogood `x ≤ c − 1` is then violated by every domain value);
    implied literal `posLe i (c − 1)` (narrow the upper bound to
    `c − 1`) when only the maximum exceeds it; `.stable` when the
    bound is already tight. The reason clause is the unit nogood
    `[posLe i (c − 1)]`, entailed by the constraint
    `.ltConstHi i c` alone. -/
def propLtConstHi (st : State) (i : Nat) (c : Int) : PropagationResult :=
  narrowHi st i (c - 1) [posLe i (c - 1)]

/-- `int_lt(c, x)` / `int_gt` style: slot `i` must be `> c`, i.e.
    `≥ c + 1`. Conflict when the domain's maximum is already `≤ c`;
    implied literal `negLe i c` (i.e. `x > c`, narrowing the lower
    bound to `c + 1`) when only the minimum is below it. The reason
    clause is the unit nogood `[negLe i c]`, entailed by the
    constraint `.ltConstLo i c` alone. (narrowLo's implied head at
    `lo = c + 1` is `negLe s (lo − 1) = negLe i (c + 1 − 1)`, the
    same literal up to integer arithmetic; the pivot-membership
    proofs discharge `c + 1 − 1 = c` by `omega`.) -/
def propLtConstLo (st : State) (i : Nat) (c : Int) : PropagationResult :=
  narrowLo st i (c + 1) [negLe i c]

/-- `int_eq(x, c)` style: slot `i` must carry exactly the value
    `v`.

    * Integer constant `k`: equality decomposes into the two bound
      facts `x ≤ k` and `x ≥ k`, each with its constraint-valid
      unit nogood — `narrowHi` conflicts when `mn > k` (all domain
      values above `k`) and implies `posLe i k`; `narrowLo`
      conflicts when `mx < k` and implies `negLe i (k − 1)`;
      `firstEvent` reports the first non-stable event. `x = k`
      entails BOTH `x ≤ k` and `x ≥ k`, so each conflict clause is
      entitled.
    * Boolean constant `b`: the `boolEq` atom at its normalized
      positive literal `posBool i b` — implied (with the unit nogood
      `[posBool i b]`) whenever the domain still contains `.bool b`
      alongside something else, conflict (same unit clause, then
      entitled but falsified by the domain) when it contains no
      `.bool b` at all, stable when the domain is exactly the
      singleton `[.bool b]`.
    * Set/array constants: `.stable` (the extractor never emits
      them; sound, merely incomplete). -/
def propConstEq (st : State) (i : Nat) (v : Value) : PropagationResult :=
  match v with
  | .int k =>
      firstEvent
        [ narrowHi st i k [posLe i k]
        , narrowLo st i k [negLe i (k - 1)] ]
  | .bool b =>
      if valueMemB (.bool b) (st.domains.getD i []) then
        if valuesEqB (st.domains.getD i []) [.bool b] then .stable
        else .implied (posBool i b) { clause := [posBool i b] }
      else .conflict [posBool i b]
  | _ => .stable

/-- Register the standard propagator for a `DomConstraint` (via its
    executable semantics twin `satisfiedB` for leaf checks; the bound
    propagators above carry the explanations). Returns `none` for
    constraint kinds whose explanation theorem is future work (L0.3
    sequencing). -/
def propagatorOf (dom : DomConstraint) : Option Propagator :=
  match dom with
  | .plusSlot i j k =>
      some { watches := [], run := fun st => propPlus st i j k }
  | .leSlot i j =>
      some { watches := [], run := fun st => propLe st i j }
  | .ltSlot i j =>
      some { watches := [], run := fun st => propLt st i j }
  | .eqSlot i j =>
      some { watches := [], run := fun st => propEq st i j }
  | .neSlot i j =>
      some { watches := [], run := fun st => propNe st i j }
  | .linLe coeffs is b =>
      some { watches := [], run := fun st => propLinLe st coeffs is b }
  | .leConstHi i c =>
      some { watches := [], run := fun st => propLeConstHi st i c }
  | .leConstLo i c =>
      some { watches := [], run := fun st => propLeConstLo st i c }
  | _ => none

/-- All available propagators of a constraint list. -/
def propagatorsOf (doms : List DomConstraint) : List Propagator :=
  doms.filterMap propagatorOf

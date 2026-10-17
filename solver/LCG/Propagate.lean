/-
File: solver/LCG/Propagate.lean

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
  `LCG.Engine.enqueueNorm`). Hence a cause literal built from a domain
  extremum always has its exact witnessing entry on the trail, which is
  what conflict analysis resolves against.

Dependencies:
  - solver.LCG.Operations: the `PropagationResult` interface.

DAG:
  solver.LCG.Operations -> solver.LCG.Propagate -> solver.LCG.Engine
-/

import solver.LCG.Operations
import solver.Propagators

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint setSlot)

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

/-- `int_ne`-style: `x ≠ y` over slots `i j`. Two sound behaviours:

    * when BOTH sides are singletons, a direct conflict is reported
      if the values are equal (the constraint is violated), else
      nothing to do;
    * when one side is a singleton `c` and the other domain lies
      entirely on one side of `c`, the separation is already pinned by
      the root facts (the domain bounds), so no deduction is needed —
      the propagator stays stable.

    The earlier design emitted nogoods like `[y > c, x ≤ c]` for the
    strictly-separated case, but such a clause is NOT integer-valid
    under `x ≠ y` alone (it depends on domain facts), violating this
    module's discipline that reason clauses be constraint-valid.
    Value removal (excluding exactly `c` from the other side) needs
    value-removal literals (L0.6), so until then the propagator only
    reports the both-singleton conflict.

    The conflict compares the RAW singleton values (`Value.eqB`),
    not their integer views: `int_ne` means raw inequality, and an
    `int 1` vs `bool true` pair views equal but differs raw, so a
    view-based comparison would report a false conflict. -/
def propNe (st : State) (i j : Nat) : PropagationResult :=
  match st.domains.getD i [], st.domains.getD j [] with
  | [x], [y] => if x.eqB y then .conflict [] else .stable
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
  | _ => none

/-- All available propagators of a constraint list. -/
def propagatorsOf (doms : List DomConstraint) : List Propagator :=
  doms.filterMap propagatorOf

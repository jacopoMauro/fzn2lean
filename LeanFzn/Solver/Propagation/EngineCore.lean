/- Shared propagation engine and leaf semantics. -/
import LeanFzn.Solver.Propagation.Propagate
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation

/-! ## Boolean clause scanning -/

/-- All active clauses: original and learned. -/
def State.allClauses (st : State) : List Clause := st.clauses ++ st.learned

/-- Scan one clause under the current state: `some (.inl c)` — every
    literal is trail-false (conflict clause `c`); `some (.inr (l, r))` —
    exactly one non-false literal remains (unit: enqueue `l` with reason
    clause `r`); `none` — satisfied, or two-or-more open literals. -/
def scanClause (st : State) (c : Clause) :
    Option (Sum Clause (Literal × Reason)) :=
  if c.any fun l => st.litOnTrail l then none
  else
    match c.filter fun l => !st.negOnTrail l with
    | [] => some (.inl c)
    | [l] => some (.inr (l, { clause := c }))
    | _ => none

/-- One pass over every active clause: first conflict, else first unit. -/
def scanAll (st : State) : Option (Sum Clause (Literal × Reason)) :=
  let rec go (cs : List Clause) : Option (Sum Clause (Literal × Reason)) :=
    match cs with
    | [] => none
    | c :: rest =>
        match scanClause st c with
        | none => go rest
        | some r => some r
  go st.allClauses

/-! ## Enqueue and domain maintenance -/

/-- The keep test of the integer filter on one value. -/
def domFilterIntKeep (keep : Int → Bool) : Value → Bool
  | .int i => keep i
  | .bool b => keep (if b then 1 else 0)
  | _ => true

/-- Keep only domain values whose integer view passes `keep`.  When the
    filter removes nothing the original domain is returned unchanged
    (the denotation is the same, but the identity is definitional and
    keeps the root-fact fold proofs free of canonicality premises). -/
def domFilterInt (keep : Int → Bool) (d : Domain) : Domain :=
  let vs := Dom.enum d
  let kept := vs.filter (domFilterIntKeep keep)
  if kept.length = vs.length then d else Dom.ofList kept

/-- Replace slot `s`'s domain by `f` applied to its current value
    (identity past the end of the slot list). -/
def updateSlot (doms : List Domain) (s : Nat)
    (f : Domain → Domain) : List Domain :=
  doms.set s (f (doms.getD s Dom.empty))

/-- Apply the domain filter implied by literal `l`: Boolean atoms fix the
    slot to the forced value; positive order literals keep `≤ k`;
    negative ones keep `> k`; positive value-removal literals remove
    exactly `k` (keeping every other value, sets/arrays included);
    negative ones pin to the singleton `k`. -/
def domOfLit (doms : List Domain) (l : Literal) : List Domain :=
  match l.atom with
  | .intLe s k =>
      if l.positive then
        updateSlot doms s (fun d => domFilterInt (fun p => p ≤ k) d)
      else
        updateSlot doms s (fun d => domFilterInt (fun p => p > k) d)
  | .boolEq s b =>
      updateSlot doms s (fun d => d.filter (fun v =>
        v.eqB (.bool (if l.positive then b else !b))))
  | .intNe s k =>
      if l.positive then
        updateSlot doms s (fun d => domFilterInt (fun p => p ≠ k) d)
      else
        updateSlot doms s (fun d => domFilterInt (fun p => p = k) d)

/-- Normalize and enqueue a literal with its reason, skipping
    re-assertions of trail facts. Opposite-fact enqueues (asserting the
    negation of a trail fact) set the two-literal conflict `[l, ¬l]`. -/
def enqueueNorm (st : State) (l0 : Literal) (reason : Option Reason) : State :=
  let l := l0.norm
  if st.litOnTrail l then st
  else if st.negOnTrail l then
    { st with conflict := some [l, l.negate] }
  else
    let st' := enqueue st l reason
    { st' with domains := domOfLit st'.domains l }

/-- Run every propagator, applying implied literals immediately and
    recording the first reported conflict. -/
def runPropagators (props : List Propagator) (st : State) : State :=
  let rec go (ps : List Propagator) (acc : State) : State :=
    match ps with
    | [] => acc
    | p :: rest =>
        if acc.conflict.isSome then acc
        else
          match p.run acc with
          | .stable => go rest acc
          | .conflict c => { acc with conflict := some c }
          | .implied l r => go rest (enqueueNorm acc l (some r))
  go props st

/-- Propagation to fixpoint: unit clause enqueue, then propagator sweep.
    A propagator trail extension restarts the scan; a quiescent state is
    returned unchanged. Fuel bounds the loop (each continuing iteration
    strictly extends the trail). -/
def propagateLoop (fuel : Nat) (props : List Propagator) (st : State) : State :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
      if st.conflict.isSome then st
      else
        match scanAll st with
        | some (.inl c) => { st with conflict := some c }
        | some (.inr (l, r)) => propagateLoop fuel props (enqueueNorm st l (some r))
        | none =>
            let st' := runPropagators props st
            if st'.trail.length == st.trail.length then st'
            else propagateLoop fuel props st'

/-- Rebuild the state after a backjump: drop entries above `level`,
    recompute the domains from the kept trail order, and clear the
    conflict. -/
def repairAfterBackjump (problem : Problem Constraint Objective)
    (level : Nat) (st : State) : State :=
  let kept := st.trail.filter fun e => e.level ≤ level
  let doms := kept.foldl (fun acc e => domOfLit acc e.literal) problem.domains
  { st with trail := kept, domains := doms, decisionLevel := level, conflict := none }

/-- Decide assignment fit: right length and every value in its original
    problem domain. -/
def fitsB (problem : Problem Constraint Objective)
    (a : Assignment) : Bool :=
  a.length == problem.domains.length &&
    (List.range a.length).all fun s =>
      match a[s]? with
      | some v => valueMemB v (Dom.enum (problem.domains.getD s Dom.empty))
      | none => true

/-- Runtime twin of `fitsB` that tests membership on the compact domain
    representation instead of materialising `Dom.enum` for every slot, and
    reads both the assignment and the domain list through arrays so the leaf
    check is linear rather than a quadratic `List.get?` walk. -/
def fitsBFast (problem : Problem Constraint Objective)
    (a : Assignment) : Bool :=
  let arr := a.toArray
  let doms := problem.domains.toArray
  arr.size == doms.size &&
    (List.range arr.size).all fun s =>
      match arr[s]? with
      | some v => (doms.getD s Dom.empty).memBool v
      | none => true

/-- The leaf membership twin agrees with `fitsB`. -/
theorem fitsBFast_eq (problem : Problem Constraint Objective) (a : Assignment) :
    fitsBFast problem a = fitsB problem a := by
  unfold fitsBFast fitsB
  dsimp only
  rw [List.size_toArray, List.size_toArray]
  congr 1
  apply List.all_congr rfl
  intro s
  cases h : a[s]? with
  | none =>
      have h' : a.toArray[s]? = none := by simpa using h
      simp [h']
  | some v =>
      have h' : a.toArray[s]? = some v := by simpa using h
      rw [h']
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
      rw [Bool.eq_iff_iff, Dom.memBool_iff, valueMemB_iff]
      simp

/-- Compile `fitsB` as the compact-membership twin; proofs keep the
reference definition. -/
@[csimp] theorem fitsB_eq_fast : @fitsB = @fitsBFast := by
  funext Constraint Objective problem a
  exact (fitsBFast_eq (Constraint := Constraint) (Objective := Objective)
    problem a).symm

/-- `fitsB` decides `Fits`. -/
theorem fitsB_iff {problem : Problem Constraint Objective} {a : Assignment} :
    fitsB problem a = true ↔ a.Fits problem.domains := by
  constructor
  · intro h
    simp only [fitsB, beq_iff_eq, Bool.and_eq_true] at h
    obtain ⟨hlen, hall⟩ := h
    refine ⟨hlen, ?_⟩
    intro slot value hval
    have hlt : slot < a.length := by
      rw [List.getElem?_eq_some_iff] at hval
      exact hval.1
    have hmemr : slot ∈ List.range a.length := List.mem_range.mpr hlt
    have hall' := List.all_eq_true.mp hall slot hmemr
    cases hget : a[slot]? with
    | none => rw [hget] at hval; exact absurd hval (by simp)
    | some v =>
      rw [hget] at hall'
      rw [hget] at hval
      injection hval with hval
      subst hval
      exact (DomainLike.mem_iff _ _).mpr
        (by simpa [domElems_eq_enum] using valueMemB_iff.mp hall')
  · intro h
    obtain ⟨hlen, hmem⟩ := h
    simp only [fitsB, beq_iff_eq, Bool.and_eq_true]
    refine ⟨hlen, ?_⟩
    rw [List.all_eq_true]
    intro slot hslot
    rw [List.mem_range] at hslot
    cases hget : a[slot]? with
    | none => simp only [hget]
    | some v =>
      simp only [hget]
      exact valueMemB_iff.mpr (by
        have hv := (DomainLike.mem_iff
          (problem.domains.getD slot DomainLike.empty) v).mp (hmem slot v hget)
        simpa [domElems_eq_enum] using hv)

/-! ## The search loop -/

/-- Root facts of the initial domains: for every slot with at least one
    integer value, the two order literals pinning its initial
    integer-view bounds (`¬(s ≤ min−1)` and `s ≤ max`). Enqueued at
    level 0, they witness every cause literal built from initial domain
    extrema, so conflict analysis can resolve domain-derived causes, and
    `trailLo`/`trailHi` reproduce the initial bounds before any
    decision. -/
def rootFacts (doms : List Domain) : List Literal :=
  let rec go (s : Nat) (ds : List Domain) : List Literal :=
    match ds with
    | [] => []
    | d :: rest =>
        match domMinI d, domMaxI d with
        | some mn, some mx => negLe s (mn - 1) :: posLe s mx :: go (s + 1) rest
        | _, _ => go (s + 1) rest
  go 0 doms

/-- The initial state with root facts enqueued (level 0, no reasons). -/
def initialStateWithRoots (problem : Problem Constraint Objective) : State :=
  let st0 := initialState problem
  rootFacts problem.domains |>.foldl (fun st l =>
    if st.litOnTrail l then st else enqueue st l none) st0


/-- Pick a branching literal: `¬(s ≤ mid)` bisection on the first slot
    whose domain still has at least two integer values. -/
def decideLiteral (st : State) : Option Literal :=
  let rec go (s : Nat) (doms : List Domain) : Option Literal :=
    match doms with
    | [] => none
    | d :: rest =>
        match domMinI d, domMaxI d with
        | some mn, some mx =>
            if mn < mx then some (negLe s ((mn + mx) / 2))
            else go (s + 1) rest
        | _, _ => go (s + 1) rest
  go 0 st.domains

/-- Is every slot domain a singleton (a complete assignment)? -/
def allSingleton (st : State) : Bool :=
  st.domains.all fun d => d.length == 1

/-- The executable `TrailBoolPins` gate: every Boolean-pin trail
    entry sits on a slot whose PROBLEM domain is all-Bool. Vacuously
    true for trails without Boolean pins (compiled models' order-
    literal trails and the constEq-Bool family's domain-gated
    pins). -/
def trailBoolPinsOk (problem : Problem Constraint Objective)
    (trail : List TrailEntry) : Bool :=
  trail.all fun e =>
    match e.literal.atom with
    | .boolEq s _ =>
        Dom.enum (problem.domains.getD s Dom.empty) |>.all fun v =>
          match v with
          | .bool _ => true
          | _ => false
    | _ => true

/-- The complete assignment under all-singleton domains. -/
def singletonAssignment (st : State) : Option Assignment :=
  st.domains.mapM fun d =>
    match Dom.enum d with
    | [v] => some v
    | _ => none

/-- The leaf predicate of the chronological traversal: original-domain
    fit, every compiled constraint, and every original clause. -/
def chronologicalLeaf (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) :
    Assignment → Bool :=
  fun a => fitsB problem a &&
    (problem.constraints.all (fun c => constraintHoldsB c a) &&
      problem.clauses.all (fun c => c.any (fun l => decide (l.eval a = some true))))


end LeanFzn.Solver.Propagation

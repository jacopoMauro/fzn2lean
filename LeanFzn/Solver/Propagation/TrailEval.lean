/-
File: LeanFzn/Solver/Propagation/TrailEval.lean

Purpose:
  Trail-derived literal evaluation and the executable first-UIP conflict
  analysis for the LCG LeanFzn.Solver. Everything here is a pure computation on
  the trail: no clause database and no propagators are consulted.

  Literal hygiene: the engine enqueues only normalized literals — Boolean
  facts are always stored positively (`¬(b = false)` is stored as
  `b = true`) — and every cause literal constructed by the propagation
  layer is the exact negation of a normalized fact. Hence exact matching
  (`findEntryOf`, `litOnTrail`, `negOnTrail`) is a complete account of
  truth and falsity for the literals that appear in reason and conflict
  clauses.


Dependencies:
  - LeanFzn.Solver.Propagation.Types: trail entries, literals, conflict analyses.

DAG:
  LeanFzn.Solver.Propagation.Types -> LeanFzn.Solver.Propagation.TrailEval -> LeanFzn.Solver.Propagation.Operations
-/

import LeanFzn.Solver.Propagation.Types
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Literal hygiene -/

/-- Negate a signed literal. -/
def Literal.negate (l : Literal) : Literal :=
  { l with positive := !l.positive }

/-- Canonical literal form: Boolean facts are always stored positively —
    `¬(b = false)` is rewritten to `b = true` — so that exact trail
    matching sees one representation per semantic Boolean fact. -/
def Literal.norm (l : Literal) : Literal :=
  match l.atom with
  | .boolEq s b => if l.positive then l else { atom := .boolEq s (!b), positive := true }
  | _ => l

/-- Structural literal equality. -/
def litEqB (a b : Literal) : Bool := decide (a = b)

/-- Positive order literal `s ≤ k`. -/
def posLe (s : Nat) (k : Int) : Literal := ⟨.intLe s k, true⟩

/-- Negative order literal `¬(s ≤ k)` (i.e. `s > k`). -/
def negLe (s : Nat) (k : Int) : Literal := ⟨.intLe s k, false⟩

/-- Positive value-removal literal `s ≠ k` (the value `k` is removed
    from the slot's domain when asserted). -/
def posNe (s : Nat) (k : Int) : Literal := ⟨.intNe s k, true⟩

/-- Negative value-removal literal `¬(s ≠ k)` (i.e. the slot's integer
    view equals `k`). -/
def negNe (s : Nat) (k : Int) : Literal := ⟨.intNe s k, false⟩

/-- Positive Boolean literal `s = b` (in normalized position). -/
def posBool (s : Nat) (b : Bool) : Literal := ⟨.boolEq s b, true⟩

/-- Integer minimum (kept local: no Mathlib). -/
def minI (a b : Int) : Int := if a ≤ b then a else b

/-- Integer maximum (kept local: no Mathlib). -/
def maxI (a b : Int) : Int := if a ≤ b then b else a

/-! ## Trail queries -/

/-- Find the latest trail entry carrying exactly `l` (up to literal
    normalization, so the negation of a Boolean fact matches the trail's
    canonical positive form). -/
def findEntryOf (trail : List TrailEntry) (l : Literal) : Option TrailEntry :=
  trail.reverse.find? fun e => litEqB e.literal l.norm

/-- Is `l` itself (up to normalization) on the trail? -/
def State.litOnTrail (st : State) (l : Literal) : Bool :=
  st.trail.any fun e => litEqB e.literal l.norm

/-- Is the (canonical) negation of `l` on the trail? -/
def State.negOnTrail (st : State) (l : Literal) : Bool :=
  st.trail.any fun e => litEqB e.literal l.negate.norm

/-- Tightest upper bound of slot `s` implied by the trail: the minimum
    `k` over positive `intLe s k` entries. -/
def trailHiOf (trail : List TrailEntry) (s : Nat) : Option Int :=
  trail.foldl (fun acc e =>
    match e.literal.atom with
    | .intLe s' k =>
        if s' == s && e.literal.positive then
          match acc with
          | none => some k
          | some c => some (minI c k)
        else acc
    | _ => acc) none

def State.trailHi (st : State) (s : Nat) : Option Int :=
  trailHiOf st.trail s

/-- Tightest lower bound of slot `s` implied by the trail: one above the
    maximum `k` over negative `intLe s k` entries. -/
def trailLoOf (trail : List TrailEntry) (s : Nat) : Option Int :=
  trail.foldl (fun acc e =>
    match e.literal.atom with
    | .intLe s' k =>
        if s' == s && !e.literal.positive then
          match acc with
          | none => some (k + 1)
          | some c => some (maxI c (k + 1))
        else acc
    | _ => acc) none

def State.trailLo (st : State) (s : Nat) : Option Int :=
  trailLoOf st.trail s

/-- The latest Boolean entry for slot `s`, if the trail mentions one. -/
def State.boolEntry (st : State) (s : Nat) : Option TrailEntry :=
  st.trail.reverse.find? fun e =>
    match e.literal.atom with
    | .boolEq s' _ => decide (s' = s)
    | _ => false

/-- The Boolean value forced for slot `s` by the trail, if any. -/
def State.boolValue (st : State) (s : Nat) : Option Bool :=
  (st.boolEntry s).map fun e =>
    match e.literal.atom, e.literal.positive with
    | .boolEq _ b, true => b
    | .boolEq _ b, false => !b
    | _, _ => false

/-- The trail entry establishing the current lower bound of slot `s`
    (a `¬(s ≤ lo-1)` entry), if any. Used to witness the opposing bound
    when an enqueued literal wipes a slot's domain. -/
def loWitness (st : State) (s : Nat) : Option TrailEntry :=
  match st.trailLo s with
  | none => none
  | some lo => st.trail.find? fun e =>
      match e.literal.atom with
      | .intLe s' k => decide (s' = s) && !e.literal.positive && decide (k + 1 = lo)
      | _ => false

/-- The trail entry establishing the current upper bound of slot `s` (an
    `s ≤ hi` entry), if any. -/
def hiWitness (st : State) (s : Nat) : Option TrailEntry :=
  match st.trailHi s with
  | none => none
  | some hi => st.trail.find? fun e =>
      match e.literal.atom with
      | .intLe s' k => decide (s' = s) && e.literal.positive && decide (k = hi)
      | _ => false

/-! ## First-UIP conflict analysis

The executable twin of the `analyzeConflict_correct` obligation in
`LeanFzn/Solver/UIP/Proofs/Transitions.lean`. Mirroring the classic CDCL loop:
the working clause (starting from the conflict clause) is scanned, its
falsified literals are marked with the trail entries that falsify them,
and the latest marked entry is resolved against its reason clause
(skipping its own implied literal) until only one entry of the current
decision level remains — the first unique implication point (UIP). The
learned clause is then the negated UIP together with every lower-level
falsified literal. -/

/-- Weaken a trail-falsified order literal to one whose exact negation
    is on the trail: `x ≤ k` falsified by the trail lower bound `lo > k`
    weakens to `x ≤ lo−1` (implied, since `k ≤ lo−1`), whose negation
    `x > lo−1` is the witnessing trail entry; `x > k` falsified by the
    trail upper bound `hi ≤ k` weakens to `x > hi` dually. Boolean
    literals are bridged through the 0/1 integer view: `s = true` is
    the order literal `s > 0`, so a trail upper bound `hi ≤ 0` that
    falsifies it weakens to `s > hi` (implied, since `hi ≤ 0` makes
    "s > 0 ⇒ s > hi"); `s = false` is `s ≤ 0`, so a trail lower bound
    `lo ≥ 1` weakens to `s ≤ lo−1` dually. Without the bridge, any
    conflict clause that mixes Boolean nogoods with order-encoded
    decisions (the bool families' nogoods speak `posBool`; bisection
    decisions speak `negLe`/`posLe`) cannot resolve — markLit finds
    no falsifier and the analysis aborts to the plain retreat. -/
def orderUpgrade (trail : List TrailEntry) (l : Literal) : Literal :=
  match l.atom with
  | .intLe s k =>
      if l.positive then
        match trailLoOf trail s with
        | some lo => if lo > k then posLe s (lo - 1) else l
        | none => l
      else
        match trailHiOf trail s with
        | some hi => if hi ≤ k then negLe s hi else l
        | none => l
  | .boolEq s b =>
      if l.positive then
        if b then
          -- "s = true" is "s > 0": falsified by a trail bound hi ≤ 0,
          -- weakened to the trail's own "s > hi" entry
          match trailHiOf trail s with
          | some hi => if hi ≤ 0 then negLe s hi else l
          | none => l
        else
          -- "s = false" is "s ≤ 0": falsified by a trail bound lo ≥ 1,
          -- weakened to the trail's own "s ≤ lo−1" entry
          match trailLoOf trail s with
          | some lo => if 1 ≤ lo then posLe s (lo - 1) else l
          | none => l
      else l
  | .intNe s k => l

/-- Mark the consequences of working-clause literal `q`: the entry that
    falsifies it — by exact negation matching, or through the order
    upgrade when the trail fact is tighter than the literal — is either
    at the root level (dropped: root facts never change), at the current
    level (marked for resolution), or below it (recorded in the learned
    clause with its level). Public for the L0.4 resolution-soundness
    proof. -/
def markLit (trail : List TrailEntry) (lvl : Nat)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (q0 : Literal) : Option (List TrailEntry × List (Literal × Nat)) :=
  let q := q0.norm
  if marks.any fun m => litEqB m.literal q.negate.norm then some (marks, learnt)
  else if learnt.any fun p => litEqB p.1 q then some (marks, learnt)
  else
    -- the falsifier: exact match first, order upgrade otherwise
    let q' : Literal :=
      match findEntryOf trail q.negate with
      | some _ => q
      | none => orderUpgrade trail q
    match findEntryOf trail q'.negate with
    | none => none
    | some e =>
        if e.level == 0 then some (marks, learnt)
        else if e.level == lvl then some (e :: marks, learnt)
        else some (marks, (q', e.level) :: learnt)

/-- The latest trail entry whose literal is still marked. Public for the
    L0.4 proof. -/
def nextPivot (trail : List TrailEntry) (marks : List TrailEntry) :
    Option TrailEntry :=
  trail.reverse.find? fun e => marks.any fun m => litEqB m.literal e.literal

/-- Public for the L0.4 proof. -/
def skipEq (skip : Option Literal) (q : Literal) : Bool :=
  match skip with
  | some sl => litEqB q sl
  | none => false

/-- The analysis worklist loop: while clauses remain to scan, mark their
    literals; when the worklist is empty, pop the latest marked entry,
    finish if it was the last current-level mark (it is the UIP), or
    resolve against its reason clause. -/
def analyzeStep (trail : List TrailEntry) (lvl : Nat) :
    Nat → List Clause → Option Literal → List TrailEntry →
    List (Literal × Nat) → Option (List (Literal × Nat) × Literal)
  | 0, _, _, _, _ => none
  | Nat.succ fuel, [], _, marks, learnt =>
      match nextPivot trail marks with
      | none => none
      | some e =>
          let marks' := marks.filter fun m => !litEqB m.literal e.literal
          if marks'.isEmpty then some (learnt, e.literal)
          else
            match e.reason with
            | none => none
            | some r =>
                analyzeStep trail lvl fuel [r.clause] (some e.literal) marks' learnt
  | Nat.succ fuel, c :: cs, skip, marks, learnt =>
      match c with
      | [] => analyzeStep trail lvl fuel cs skip marks learnt
      | q0 :: qs =>
          let q := q0.norm
          if skipEq skip q then
            analyzeStep trail lvl fuel (qs :: cs) skip marks learnt
          else
            match markLit trail lvl marks learnt q with
            | none => none
            | some (marks', learnt') =>
                analyzeStep trail lvl fuel (qs :: cs) skip marks' learnt'

/-- Analyze a falsified conflict clause over the trail. Returns the
    below-level falsified literals with their levels and the first-UIP
    trail literal. Returns `none` when the clause does not resolve to a
    unique current-level literal (treated by the engine as a request for
    chronological backtracking). -/
def analyzeTrail (trail : List TrailEntry) (lvl : Nat) (conflict : Clause) :
    Option (List (Literal × Nat) × Literal) :=
  analyzeStep trail lvl (4 * trail.length * trail.length + 256)
    [conflict] none [] []

end LeanFzn.Solver.Propagation

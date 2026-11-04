/-
File: LeanFzn/Engine/Search.lean

N9: the Core search loop.  Entry gate + domain conversion (with the
in-range/converted-domain guard that makes every propagator's initial
`hinit` obligation realisable), seed clauses, root propagation, CDCL
decisions, first-UIP conflicts, learned clauses and backjumping, and a
final `fitsB`/`accepts` check.  The loop is fuel-bounded and total; every
internal doubt returns `.gaveUp`, never a claim.

Soundness is proved here without state invariants: the only `.unsat`
leaf is an entailed empty clause produced by N8 `analyze`, and the only
`.sat` leaf re-checks `fitsB`/`accepts`.  N7's `Good`/`InitInv` are used
to justify the entry state and are available to callers, but the search
soundness argument itself needs no invariant threading.
-/
import LeanFzn.Engine.Queue
import LeanFzn.Engine.Analyze
import LeanFzn.Engine.Reduce
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Linear
import LeanFzn.Engine.Props.Arith
import LeanFzn.Engine.Props.Order
import LeanFzn.Engine.Props.LinearExt
import LeanFzn.Engine.Props.BoolExt
import LeanFzn.Engine.Props.Element
import LeanFzn.Compiler.SeedClauses
import LeanFzn.Solver.Propagation.EngineCore
import LeanFzn.Solver.Propagation.Gates
import LeanFzn.Integration.Config.Parse
import LeanFzn.Integration.Config.Annotations

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

namespace LeanFzn.Engine

/-! ## Domain conversion and the entry guard -/

/-- Convert a list of compiled domains, appending one converted domain at a
time.  The accumulator is the converted prefix; a `none` anywhere is the
only entry give-up beyond the executable gate. -/
def convertDomainsAux (ds : List Dom) (acc : Array DomC) : Option (Array DomC) :=
  match ds with
  | [] => some acc
  | d :: ds =>
      match DomC.ofDom? d with
      | none => none
      | some c => convertDomainsAux ds (acc.push c)

/-- Convert every compiled domain. -/
def convertDomains (ds : List Dom) : Option (Array DomC) :=
  convertDomainsAux ds #[]

/-- The conversion spec: the accumulator's entries are preserved and each
source domain is converted to the corresponding appended entry. -/
theorem convertDomainsAux_spec (ds : List Dom) :
    ∀ (acc : Array DomC) (cs : Array DomC), convertDomainsAux ds acc = some cs →
      cs.size = acc.size + ds.length ∧
      (∀ s, s < acc.size → cs.getD s DomC.empty = acc.getD s DomC.empty) ∧
      (∀ s, s < ds.length →
        DomC.ofDom? (ds.getD s Dom.empty) = some (cs.getD (acc.size + s) DomC.empty)) := by
  induction ds with
  | nil =>
      intro acc cs h
      simp only [convertDomainsAux, Option.some.injEq] at h
      subst h
      refine ⟨by simp, ?_, ?_⟩
      · intro s _; rfl
      · intro s hs; exact absurd hs (Nat.not_lt_zero s)
  | cons d ds ih =>
      intro acc cs h
      simp only [convertDomainsAux] at h
      split at h
      · simp at h
      · rename_i c hc
        obtain ⟨hsize, hpre, hpost⟩ := ih (acc.push c) cs h
        refine ⟨?_, ?_, ?_⟩
        · rw [hsize, Array.size_push, List.length_cons]
          omega
        · intro s hs
          have hs' : s < (acc.push c).size := by rw [Array.size_push]; omega
          rw [hpre s hs']
          rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
          rw [if_neg (by omega)]
        · intro s hs
          cases s with
          | zero =>
              have h0 : cs.getD acc.size DomC.empty = c := by
                have h1 := hpre acc.size (by simp)
                rw [h1]
                simp
              simpa [List.getD_cons_zero, Nat.add_zero, h0] using hc
          | succ k =>
              have hk : k < ds.length := by simpa using hs
              have hk' := hpost k hk
              have hsize' : (acc.push c).size + k = acc.size + (k + 1) := by
                rw [Array.size_push]; omega
              rw [← hsize']
              simpa [List.getD_cons_succ] using hk'

/-- From a successful conversion, every in-range compiled domain is the
converted one.  This is the `hinit` source used by `initState`. -/
theorem convertDomains_spec {ds : List Dom} {cs : Array DomC}
    (h : convertDomains ds = some cs) :
    cs.size = ds.length ∧
    (∀ s, s < ds.length →
      DomC.ofDom? (ds.getD s Dom.empty) = some (cs.getD s DomC.empty)) := by
  obtain ⟨hsize, -, hpost⟩ :=
    convertDomainsAux_spec ds #[] cs (by simpa [convertDomains] using h)
  refine ⟨by simpa using hsize, ?_⟩
  intro s hs
  simpa using hpost s hs

/-- Total per-slot readiness test: the compiled domain at `s` converts to
exactly the converted initial domain at `s`.  Out-of-range or malformed
slots fail this equality (`DomC.ofDom? Dom.empty = none`). -/
def slotReadyB (p : CompiledProblem DomConstraint) (init : Array DomC) (s : Nat) : Bool :=
  decide (DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))

/-- Bool-to-Prop spec of `slotReadyB`. -/
theorem slotReadyB_spec {p : CompiledProblem DomConstraint} {init : Array DomC} {s : Nat}
    (h : slotReadyB p init s = true) :
    DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) :=
  of_decide_eq_true h

/-- Total initial-state readiness test: every slot read by every constraint
is in range and its converted domain matches `init`.  This is the entry
gate that makes `hinit` realisable for every propagator. -/
def initReady (p : CompiledProblem DomConstraint) (init : Array DomC) : Bool :=
  p.constraints.toArray.all fun dc =>
    (dcSlotsFull dc).toArray.all fun s => slotReadyB p init s

/-- Bool-to-Prop spec of `initReady`: it yields the per-constraint `hinit`
obligation of N6/N6b. -/
theorem initReady_spec {p : CompiledProblem DomConstraint} {init : Array DomC}
    (h : initReady p init = true) :
    ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) := by
  intro dc hdc s hs
  have h1 : (p.constraints.toArray.all fun dc =>
      (dcSlotsFull dc).toArray.all fun s => slotReadyB p init s) = true := h
  have h2 := (Array.all_eq_true'.mp h1) dc (List.mem_toArray.mpr hdc)
  exact slotReadyB_spec ((Array.all_eq_true'.mp h2) s (List.mem_toArray.mpr hs))

/-- N7's total `InitInv` follows from the conversion and the guard.  (The
guard is not needed: conversion alone yields the in-range equality, and
out-of-range slots are empty on both sides.) -/
theorem initInv_of_convertDomains {p : CompiledProblem DomConstraint} {init : Array DomC}
    (hconv : convertDomains p.domains = some init) : InitInv p init := by
  intro s
  by_cases hs : s < p.domains.length
  · have hspec := (convertDomains_spec hconv).2 s hs
    rw [hspec]
    simp
  · have hge : p.domains.length ≤ s := Nat.le_of_not_lt hs
    have hpd : p.domains.getD s Dom.empty = Dom.empty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    have hsize : init.size = p.domains.length := (convertDomains_spec hconv).1
    have hid : init.getD s DomC.empty = DomC.empty := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [hpd, DomC.ofDom?_empty, hid]
    rfl

/-! ## The propagator table -/

/-- The dedicated sound propagators: the `Ne`, Boolean, bounded-linear and
arithmetic families, and the generic `propCheckV2With` for every other
family.  Each carries the explicit constraint-membership proof, and every
domain-reading propagator also carries the initial-domain `hinit` obtained
from `initReady`.  `boolClauseSlot` is additionally seeded as an ordinary
clause, so it has both a clause and a dedicated event-driven propagator. -/
def propsOf (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .neSlot i j =>
        nePropWith p T init i j
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolClauseSlot ps ns =>
        boolClausePropWith p T ps ns
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLe cs is b =>
        linLePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .plusSlot i j k =>
        plusPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .timesSlot i j k =>
        timesPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minSlot i j k =>
        minPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxSlot i j k =>
        maxPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .absSlot i k =>
        absPropWith p T i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minPair o0 o1 r =>
        minPairPropWith p T o0 o1 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxPair o0 o1 r =>
        maxPairPropWith p T o0 o1 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minGen os r =>
        minGenPropWith p T os r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxGen os r =>
        maxGenPropWith p T os r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .divGen o1 o2 r =>
        divPropWith p T o1 o2 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .modGen o1 o2 r =>
        modPropWith p T o1 o2 r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .eqSlot i j =>
        eqPropWith p T init i j
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leSlot i j =>
        lePropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltSlot i j =>
        ltPropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstHi i c =>
        leConstHiPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstLo i c =>
        leConstLoPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstHi i c =>
        ltConstHiPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstLo i c =>
        ltConstLoPropWith p T i c
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .bool2intSlot i k =>
        bool2intPropWith p T i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .eqReifSlot i j r =>
        eqReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leReifSlot i j r =>
        leReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .neReifSlot i j r =>
        neReifPropWith p T i j r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linEq cs is b =>
        linEqPropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNe cs is b =>
        linNePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linEqReif cs is b r =>
        linEqReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLeReif cs is b r =>
        linLeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNeReif cs is b r =>
        linNeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolNotSlot i j =>
        boolNotPropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolAndSlot i j k =>
        boolAndPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolOrSlot i j k =>
        boolOrPropWith p T i j k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolEqSlot i j =>
        boolEqPropWith p T i j
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayBoolAndSlot is k =>
        arrayBoolAndPropWith p T is k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayIntElementSlot xs i k =>
        arrayIntElementPropWith p T xs i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarIntElementSlot is i k =>
        arrayVarIntElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarBoolElementSlot is i k =>
        arrayVarBoolElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- Intern a denotation-level clause and add it to the database. -/
def addClauseDen (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (ls : List Literal) (h : Entailed p ls) :
    EngineState p T × EClause p T × Nat :=
  let res := st.table.internArray ls.toArray
  let e := EClause.ofLits p T res.1 (by
    have h' := LitTable.decodeClause_internArray_snd (T := st.table) (ls := ls.toArray)
    have hdec : T.decodeClause res.1 = ls := by
      change res.2.decodeClause res.1 = ls
      simpa using h'
    rw [hdec]
    exact h)
  let (db, id) := st.db.add e
  ({ st with table := res.2, db := db }, e, id)

/-- Entailment of a seed clause from its membership in `seedClauses`. -/
theorem seedEntailed (p : CompiledProblem DomConstraint) {c : Clause}
    (hc : c ∈ seedClauses p.constraints) : Entailed p c :=
  fun _a _ha hacc =>
    seedClauses_entailed (fun dc hdc => List.all_eq_true.mp hacc dc hdc) c hc

/-- Add every seed clause to the database. -/
def addSeedClausesFrom (p : CompiledProblem DomConstraint) (T : LitTable)
    (cs : List {c : Clause // c ∈ seedClauses p.constraints})
    (st : EngineState p T) : EngineState p T :=
  cs.foldl (fun st x => (addClauseDen p T st x.1 (seedEntailed p x.2)).1) st

/-- Add all `bool_clause` seeds, then report the first live empty clause.
Adding all seeds (rather than stopping at the first empty one) keeps the
entry simple; `ClauseDB.emptyConflict?_spec` supplies the soundness
content of the returned clause. -/
def addSeedClauses (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) : EngineState p T × Option (EClause p T) :=
  let st' := addSeedClausesFrom p T (seedClauses p.constraints).attach st
  (st', st'.db.emptyConflict?)

/-- The problem seen by entry/root propagation: the same box and
constraints, with the seed clauses as its clause list. -/
def propagationProblem (p : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := p.names
    domains := p.domains
    constraints := p.constraints
    objective := ()
    clauses := seedClauses p.constraints }

/-- Build the initial state, or `none` when the entry fragment rejects the
problem (gate failure, failed conversion, or the `initReady` guard). -/
def initState (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  if !gateOkFast (propagationProblem p) then none
  else
    match convertDomains p.domains with
    | none => none
    | some doms =>
        if hready : initReady p doms = true then
          let hinitAll := initReady_spec hready
          let props := propsOf p T doms hinitAll
          let st : EngineState p T :=
            { table := T
              doms := doms
              trail := #[]
              levelStart := #[0]
              level := 0
              changeIndex := Array.replicate doms.size (#[] : Array Nat)
              db := {}
              reasons := #[]
              props := props
              subs := #[]
              queueHigh := #[]
              queueLow := #[]
              inQueue := ByteArray.empty
              activity := Array.replicate doms.size (0.0 : Float)
              activityHeap := #[]
              phases := #[]
              restarts := 0
              stats := {} }
          let st := registerProps st
          let st := (List.range props.size).foldl (fun st i => enqueueProp st i) st
          some st
        else none

/-! ## Decisions -/

/-- Annotation priority vector as an array; unannotated slots score 0. -/
def annotPrioArray (p : CompiledProblem DomConstraint) : Array Nat :=
  (annotPrio p.source p.names).toArray

/-! ## Conflict activity (N12)

`activity` is a pure policy score: it is read by `selectSlot` under
`--var=act|domwdeg` and never feeds a verdict.  The array is decayed on every
analysed conflict, bumped on the learned clause's slots, and rescaled when a
score would leave the finite `Float` range.  A linear scan over `activity` is
used for selection; `activityHeap` is left untouched (see the N12 report). -/

/-- Per-conflict multiplicative activity decay. -/
def activityDecay : Float := 0.95

/-- The bump contributed by one occurrence of slot `s`: `1` under `act` and
`1 / |dom(s)|` under `domwdeg`. -/
def activityBump (st : EngineState p T) (o : SearchConfig) (s : Nat) : Float :=
  match o.var with
  | .domwdeg =>
      let n := (st.doms.getD s DomC.empty).size
      if n == 0 then 1.0 else 1.0 / n.toFloat
  | _ => 1.0

/-- Decay every activity, bump the slots of the learned clause, and rescale
    all scores by `1e-100` when the maximum exceeds `1e100`.  Deterministic:
    `Array.foldl` visits the literals in learned-clause order. -/
def bumpActivity (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : EngineState p T :=
  let decayed := st.activity.map fun a => a * activityDecay
  let bumped := lits.foldl (fun (a : Array Float) (l : PLit) =>
    let s := atomSlot l.lit.atom
    a.setGrow s (a.getD s 0.0 + activityBump st o s) 0.0) decayed
  if bumped.any fun a => a > 1.0e100 then
    { st with activity := bumped.map fun a => a * 1.0e-100 }
  else { st with activity := bumped }

/-- Conflict-driven bumping is active only for the two activity
strategies; every other `--var` route leaves `activity` untouched. -/
def bumpActivityIf (st : EngineState p T) (o : SearchConfig)
    (lits : Array PLit) : EngineState p T :=
  match o.var with
  | .act | .domwdeg => bumpActivity st o lits
  | _ => st

/-- Select the next unfixed slot.  `minc` is the default; `annot` uses the
priority vector and falls back to `minc` inside a band; `act` and `domwdeg`
take the highest activity and break ties by `minc` (smallest domain, then
lowest index).  The scan only ever considers unfixed, nonempty slots. -/
def selectSlot (p : CompiledProblem DomConstraint) (st : EngineState p T)
    (o : SearchConfig) (prio : Array Nat) : Option Nat :=
  let rec go (i : Nat) (best : Option Nat) (bestSize : Nat) (bestAct : Float)
      (bestPrio : Nat) : Option Nat :=
    if h : i < st.doms.size then
      let d := st.doms[i]
      let sz := d.size
      if sz != 1 && !d.isEmpty then
        let better : Bool :=
          match best with
          | none => true
          | some _ =>
              if o.var == .act || o.var == .domwdeg then
                let ai := st.activity.getD i 0.0
                if ai != bestAct then decide (ai > bestAct)
                else decide (sz < bestSize)
              else if o.var == .annot then
                let pi := prio.getD i 0
                if pi != bestPrio then decide (pi > bestPrio)
                else decide (sz < bestSize)
              else decide (sz < bestSize)
        if better then
          go (i + 1) (some i) sz (st.activity.getD i 0.0) (prio.getD i 0)
        else go (i + 1) best bestSize bestAct bestPrio
      else go (i + 1) best bestSize bestAct bestPrio
    else best
  termination_by st.doms.size - i
  go 0 none 0 0.0 0

/-- Descending search for a member at or below `v`, at most `k` steps. -/
def findMemberDown (d : DomC) (v : Int) : Nat → Option Int
  | 0 => none
  | k + 1 => if d.memIntView v then some v else findMemberDown d (v - 1) k

/-- Ascending search for a member at or above `v`, at most `k` steps. -/
def findMemberUp (d : DomC) (v : Int) : Nat → Option Int
  | 0 => none
  | k + 1 => if d.memIntView v then some v else findMemberUp d (v + 1) k

/-- The value pinned by a value-presentation literal: `s ≤ lo` fixes the
    domain minimum, `¬(s ≤ hi-1)` fixes its maximum, `¬(s ≠ v)` fixes `v`,
    and `s = b` fixes the Boolean. -/
def decidedValue? (l : Literal) : Option Value :=
  match l.atom, l.positive with
  | .boolEq _ b, true => some (.bool b)
  | .intLe _ k, true => some (.int k)
  | .intLe _ k, false => some (.int (k + 1))
  | .intNe _ v, false => some (.int v)
  | _, _ => none

/-- The saved-phase literal of a value that is still in the domain, or
    `none` when the saved value has been removed (or has the wrong type).
    The returned literal pins the slot to that value and uses the same
    presentation form as `selectValue` would: the domain minimum is a
    `posLe`, the maximum a `negLe`, and an interior value a `negNe`.
    Hence re-deciding the phase that an ascending strategy would choose is
    observationally inert. -/
def phaseLiteral (s : Nat) (d : DomC) (v : Value) : Option Literal :=
  match d, v with
  | .bool _, .bool b =>
      if d.mem (.bool b) then some (posBool s b) else none
  | .bool _, _ => none
  | _, .int i =>
      if d.memIntView i then
        match d.lo?, d.hi? with
        | some lo, some hi =>
            if i == lo then some (posLe s lo)
            else if i == hi then some (negLe s (hi - 1))
            else some (negNe s i)
        | _, _ => some (negNe s i)
      else none
  | _, _ => none

/-- Value presentation.  `min`/`act`/`annot`/`incumbent` take the low end,
`max` the high end, `median` fixes a central member.  Boolean domains use
their two-valued order.  Under `act` the saved phase is tried first when it
is still a domain member, but only under the dynamic variable strategies
(`act`/`domwdeg`); the static `minc`/`annot` paths keep their pre-N12
behaviour (phase saving measurably regresses `minc/act`, see the N12
record).  Under `incumbent` the saved phase is the previous round's
incumbent, it is tried first for every variable strategy, and the decision
loop does not overwrite it, so it stays a fixed per-round guide rather than
accumulating phase saving.  Every other value strategy is unchanged. -/
def selectValue (s : Nat) (d : DomC) (o : SearchConfig) (ord : AnnValOrder)
    (saved : Option Value) : Option Literal :=
  let phase : Option Literal :=
    if o.val == .incumbent ||
        (o.val == .act && (o.var == .act || o.var == .domwdeg)) then
      match saved with
      | some v => phaseLiteral s d v
      | none => none
    else none
  match phase with
  | some l => some l
  | none =>
    match d with
    | .bool bits =>
        let canFalse := (bits &&& 1) != 0
        let canTrue := (bits &&& 2) != 0
        if o.val == .max then
          if canTrue then some (posBool s true)
          else if canFalse then some (posBool s false) else none
        else
          if canFalse then some (posBool s false)
          else if canTrue then some (posBool s true) else none
    | _ =>
        match d.lo?, d.hi? with
        | some lo, some hi =>
            if lo == hi then none
            else
              let useMax := o.val == .max || ord == .max || ord == .reverseSplit
              let useMedian := o.val == .median || ord == .median
              if useMax then some (negLe s (hi - 1))
              else if useMedian then
                let m := lo + (hi - lo) / 2
                match findMemberDown d m 64 with
                | some v => some (negNe s v)
                | none =>
                    match findMemberUp d (m + 1) 64 with
                    | some v => some (negNe s v)
                    | none => some (posLe s lo)
              else some (posLe s lo)
        | _, _ => none

/-- Choose a decision literal together with the value it pins, or `none`
    when all slots are fixed.  The value is stored as the slot's saved phase
    by the caller. -/
def selectDecision (p : CompiledProblem DomConstraint) (st : EngineState p T)
    (o : SearchConfig) (prio : Array Nat) (orders : List AnnValOrder) :
    Option (PLit × Value) :=
  match selectSlot p st o prio with
  | none => none
  | some s =>
      let d := st.doms.getD s DomC.empty
      match selectValue s d o (orders.getD s .none) st.phases[s]? with
      | none => none
      | some l => (decidedValue? l).map fun v => (pLit l, v)

/-- The fixed assignment in slot order, or `none` if a slot is not fixed. -/
def fixedAssignment (st : EngineState p T) : Option (List Value) :=
  let rec go (i : Nat) (acc : List Value) : Option (List Value) :=
    if h : i < st.doms.size then
      match st.doms[i].fixedValue with
      | some v => go (i + 1) (v :: acc)
      | none => none
    else some acc.reverse
  termination_by st.doms.size - i
  go 0 []

/-! ## Restart schedules (N12)

Restarts are a policy step: they backjump to level 0, keep the learned
clause database, activity and saved phases, and continue the same `search`
recursion.  They never produce a verdict: every leaf is the same
`search_sat`/`search_unsat` leaf as before. -/

/-- Bounded power-of-two block search for the Luby sequence. -/
def lubyPow (fuel i p : Nat) : Nat :=
  match fuel with
  | 0 => p
  | f + 1 => if i < 2 * p then p else lubyPow f i (2 * p)

/-- Fuel-bounded Luby value at the 1-indexed position `i`:
`1, 1, 2, 1, 1, 2, 4, ...`.  `64` block steps cover every position below
`2^64`, far beyond any restart count reachable under `coreFuel`. -/
def lubyAux : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, i =>
      let p := lubyPow f i 1
      let j := i - p
      if j + 1 = p then p else lubyAux f (j + 1)

/-- The Luby restart unit sequence value at `i` (1-indexed). -/
def luby (i : Nat) : Nat := lubyAux 64 i

/-- The conflict threshold of the next restart. -/
def restartThreshold (o : SearchConfig) (restarts : Nat) : Nat :=
  match o.restart with
  | .luby => o.restartBase * luby (restarts + 1)
  | .geom => o.restartBase * 2 ^ restarts
  | .none => 0

/-- Is a restart due after the conflict just recorded?  `none` never
restarts; `luby` uses `restartBase * luby (restarts + 1)`; `geom` uses
`restartBase * 2^restarts`. -/
def restartDue (o : SearchConfig) (st : EngineState p T) : Bool :=
  o.restart != .none && o.restartBase > 0 &&
    st.stats.conflicts >= restartThreshold o st.restarts

/-! ## The CDCL loop -/

/-- Search with an explicit fuel.  Each recursive call is structurally on a
smaller `Nat`, so the loop is total without `partial`.  The analysis is
computed before the conflict counter is bumped (the analysis reads only
the domains/table/level, never the stats), which keeps the soundness
proof's hypotheses syntactically simple. -/
def search (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) (st : EngineState p T)
    (pending : Array Pending) : Nat → CoreResult × EngineState p T
  | 0 => (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
  | f + 1 =>
      let res := drain p T st pending (f + 1)
      let st := res.st
      if res.failed then
        (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
      else
        match res.conflict with
        | some c =>
            let a := analyze p T init st c res.fuel
            let st := { st with stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
            if !a.ok then
              (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
            else
              match a.learned with
              | none =>
                  (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
              | some lc =>
                  if lc.lits.isEmpty then
                    if st.level == 0 then (.unsat, st)
                    else (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
                  else
                    let st := bumpActivityIf st o lc.lits
                    let (lc, st) := canonClause st lc
                    let (db, id) := st.db.add lc
                    let db := db.setLbd id a.lbd
                    let st := { st with
                      db := db
                      stats := { st.stats with learned := st.stats.learned + 1 } }
                    if a.backjump >= st.level then
                      (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
                    else
                      let st := backjump st a.backjump
                      match a.asserting with
                      | some l => search p T init o prio orders st
                          #[{ lit := l, reason := .learned id, count := true }] f
                      | none =>
                          -- No current-level literal: the learned clause is
                          -- falsified at the backjump level; Core makes no
                          -- claim here (give up).
                          (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
        | none =>
            -- Selection first: when a slot is selectable its decision is
            -- exactly the old `maybeReduce`/restart/`selectDecision` path,
            -- while the full `fixedAssignment` list is built only when no
            -- slot can be selected (every slot fixed, or an empty domain).
            match selectDecision p st o prio orders with
            | some (l, v) =>
                let st := maybeReduce st
                if restartDue o st && st.level > 0 then
                  -- Restart at a decision boundary: every learned clause from
                  -- the preceding conflict has already been asserted and
                  -- drained, so this only discards the current decision stack.
                  let st := { st with restarts := st.restarts + 1 }
                  search p T init o prio orders (backjump st 0) #[] f
                else
                  let s := atomSlot l.lit.atom
                  -- Under `incumbent` the phase array is the round's
                  -- fixed seed, so a decision must not overwrite it with
                  -- the value chosen this round.  The other strategies
                  -- keep ordinary phase saving.
                  let phases :=
                    if o.val == .incumbent then st.phases
                    else st.phases.setGrow s v default
                  let st := { st with
                    phases := phases
                    stats := { st.stats with decisions := st.stats.decisions + 1 } }
                  let st := newLevel st
                  search p T init o prio orders st
                    #[{ lit := l, reason := .decision, count := false }] f
            | none =>
                match fixedAssignment st with
                | some a =>
                    if fitsB (propagationProblem p) a && accepts p a then (.sat a, st)
                    else (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
                | none =>
                    -- No selectable slot but some slot is not fixed (an empty
                    -- domain): keep the old reduce/restart-then-give-up path.
                    let st := maybeReduce st
                    if restartDue o st && st.level > 0 then
                      let st := { st with restarts := st.restarts + 1 }
                      search p T init o prio orders (backjump st 0) #[] f
                    else (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })

/-! ## Search soundness -/

/-- Every `.sat` result of the loop is a box member accepted by the
problem. -/
theorem search_sat (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) :
    ∀ (fuel : Nat) (st : EngineState p T) (pending : Array Pending) (a : List Value),
      (search p T init o prio orders st pending fuel).1 = .sat a →
      a ∈ allAssigns p.domains ∧ accepts p a = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pending a h
      simp [search] at h
  | succ f ih =>
      intro st pending a h
      rw [search.eq_2] at h
      generalize hd : drain p T st pending (f + 1) = res at h
      cases res with
      | mk st1 conf fuel' failed =>
        dsimp only at h
        split at h
        · simp at h
        · split at h
          · -- conflict: analysis
            split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · split at h
                  · simp at h
                  · simp at h
                · split at h
                  · simp at h
                  · split at h
                    · exact ih _ _ _ h
                    · simp at h
          · -- no conflict: decision first, then the fixed-assignment leaf
            split at h
            · -- a slot is selectable: restart or decision
              split at h
              · exact ih _ _ _ h
              · exact ih _ _ _ h
            · -- no selectable slot: fixed assignment / empty fallback
              split at h
              · -- fixed
                split at h
                · -- final check succeeds
                  rename_i hfit
                  simp only [CoreResult.sat.injEq] at h
                  rw [h] at hfit
                  simp only [Bool.and_eq_true] at hfit
                  exact ⟨(fitsB_iff_mem_allAssigns_problem (propagationProblem p) a).mp hfit.1,
                    hfit.2⟩
                · simp at h
              · -- empty-domain fallback: restart or give up
                split at h
                · exact ih _ _ _ h
                · simp at h

/-- Every `.unsat` result of the loop excludes every accepted assignment:
the only `.unsat` leaf is an entailed empty learned clause. -/
theorem search_unsat (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (o : SearchConfig) (prio : Array Nat)
    (orders : List AnnValOrder) :
    ∀ (fuel : Nat) (st : EngineState p T) (pending : Array Pending),
      (search p T init o prio orders st pending fuel).1 = .unsat →
      ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pending h
      simp [search] at h
  | succ f ih =>
      intro st pending h
      rw [search.eq_2] at h
      generalize hd : drain p T st pending (f + 1) = res at h
      cases res with
      | mk st1 conf fuel' failed =>
        dsimp only at h
        split at h
        · simp at h
        · split at h
          · -- conflict: analysis
            split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · split at h
                  · -- entailed empty clause at level 0
                    rename_i hok x lc hlearned hemp hlev
                    exact entailed_nil_unsat
                      (analyze_empty_unsat (by simpa using hok) hlearned
                        (by simpa using hemp))
                  · simp at h
                · split at h
                  · simp at h
                  · split at h
                    · exact ih _ _ h
                    · simp at h
          · -- no conflict: decision first, then the fixed-assignment leaf
            split at h
            · -- a slot is selectable: restart or decision
              split at h
              · exact ih _ _ h
              · exact ih _ _ h
            · -- no selectable slot: fixed assignment / empty fallback
              split at h
              · split at h
                · simp at h
                · simp at h
              · split at h
                · exact ih _ _ h
                · simp at h

/-! ## Entry and the Frozen Public Seam -/

/-- An empty stored-clause lookup yields an entailed empty clause. -/
theorem emptyConflict_entailed {p : CompiledProblem DomConstraint} {T : LitTable}
    {db : ClauseDB p T} {c : EClause p T}
    (h : db.emptyConflict? = some c) : Entailed p [] := by
  obtain ⟨id, sc, hsc, hdel, hsize, he⟩ := ClauseDB.emptyConflict?_spec db h
  subst he
  have hto : sc.e.lits.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hsize
  have hdec : T.decodeClause sc.e.lits = [] := by
    simp [LitTable.decodeClause, hto]
  simpa [hdec] using sc.e.ent

/-- The seed-clause entry's returned empty clause is entailed. -/
theorem addSeedClauses_empty_entailed {p : CompiledProblem DomConstraint} {T : LitTable}
    {st st' : EngineState p T} {e : EClause p T}
    (h : addSeedClauses p T st = (st', some e)) : Entailed p [] := by
  have hconf :
      (addSeedClausesFrom p T (seedClauses p.constraints).attach st).db.emptyConflict?
        = some e := by
    simpa [addSeedClauses] using congrArg Prod.snd h
  exact emptyConflict_entailed hconf

/-- Annotation orders used by `annot` value selection (a plain `def` so
the entry proof does not have to split the configuration test). -/
def configOrders (p : CompiledProblem DomConstraint) (o : SearchConfig) :
    List AnnValOrder :=
  if o.val == .annot then annotOrders p.source p.names else []

/-- Seed the saved-phase array from a previous round's incumbent.  The array
is indexed by slot, like `fixedAssignment`; a value that is absent from the
(possibly tightened) current domain is ignored by `phaseLiteral`, and a
short list simply leaves the remaining slots without a saved phase. -/
def seedPhases (st : EngineState p T) (prev : Option (List Value)) :
    EngineState p T :=
  match prev with
  | none => st
  | some a => { st with phases := a.toArray }

@[simp] theorem seedPhases_none (st : EngineState p T) :
    seedPhases st none = st := rfl

@[simp] theorem seedPhases_some (st : EngineState p T) (a : List Value) :
    seedPhases st (some a) = { st with phases := a.toArray } := rfl

/-- Entry plus the CDCL loop with the saved phases seeded from a previous
incumbent, returning the terminal stats as well. -/
def coreSolveFullWith (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) : CoreResult × EngineStats :=
  let T : LitTable := {}
  match initState p T with
  | none => (.gaveUp, { gaveUp := 1 })
  | some st0 =>
      let st0 := seedPhases st0 prev
      let prio := annotPrioArray p
      let orders := configOrders p o
      match addSeedClauses p T st0 with
      | (st, some _) =>
          -- An entailed empty seed clause is a root refutation.
          let st := { st with stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
          (.unsat, st.stats)
      | (st, none) =>
          match st.db.emptyConflict? with
          | some _ => (.unsat, st.stats)
          | none =>
              let (db, out) := st.db.propagateUnits p T st.doms
              match out with
              | .none =>
                  let st := { st with db := db }
                  let (r, st) := search p T st.doms o prio orders st #[] fuel
                  (r, st.stats)
              | .prune ps =>
                  let st := { st with db := db }
                  let (r, st) := search p T st.doms o prio orders st
                    (pushClausePrunes #[] ps) fuel
                  (r, st.stats)
              | .conflict ec _ =>
                  let a := analyze p T st.doms st ec fuel
                  if !a.ok then (.gaveUp, { st.stats with gaveUp := 1 })
                  else
                    match a.learned with
                    | none => (.gaveUp, { st.stats with gaveUp := 1 })
                    | some lc =>
                        if lc.lits.isEmpty then (.unsat, st.stats)
                        else (.gaveUp, { st.stats with gaveUp := 1 })

/-- Entry plus the CDCL loop, returning the terminal stats as well. -/
def coreSolveFull (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveFullWith p o none fuel

/-- Core's fuel-bounded search. -/
def coreSolve (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult :=
  (coreSolveFull p o fuel).1

/-- Core's fuel-bounded search with the saved phases seeded from a previous
incumbent. -/
def coreSolveWith (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat) : CoreResult :=
  (coreSolveFullWith p o prev fuel).1

/-- The default Core fuel budget. -/
def coreFuel : Nat := 2 ^ 62

/-- The first component of `coreSolveFull` is `coreSolve`. -/
theorem coreSolveFull_fst (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : (coreSolveFull p o fuel).1 = coreSolve p o fuel := rfl

/-- Every `.sat` result of the seeded entry is a box member accepted by the
problem.  The seeded phases are policy metadata: the final `fitsB`/`accepts`
check is unchanged. -/
theorem coreSolveFullWith_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    {a : List Value}
    (h : (coreSolveFullWith p o prev fuel).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveFullWith at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · dsimp only at h
          exact search_sat p _ _ _ _ _ _ _ _ _ h
        · dsimp only at h
          exact search_sat p _ _ _ _ _ _ _ _ _ h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · simp at h

/-- Every `.sat` result of the entry is a box member accepted by the
problem. -/
theorem coreSolveFull_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : (coreSolveFull p o fuel).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFullWith_sat h

/-- Every `.unsat` result of the seeded entry excludes every accepted
assignment. -/
theorem coreSolveFullWith_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    (h : (coreSolveFullWith p o prev fuel).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveFullWith at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · rename_i hseed
      exact entailed_nil_unsat (addSeedClauses_empty_entailed hseed)
    · split at h
      · rename_i hempty
        exact entailed_nil_unsat (emptyConflict_entailed hempty)
      · split at h
        · dsimp only at h
          exact search_unsat p _ _ _ _ _ _ _ _ h
        · dsimp only at h
          exact search_unsat p _ _ _ _ _ _ _ _ h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · rename_i hok x lc hlearned hemp
                exact entailed_nil_unsat
                  (analyze_empty_unsat (by simpa using hok) hlearned
                    (by simpa using hemp))
              · simp at h

/-- Every `.unsat` result of the entry excludes every accepted
assignment. -/
theorem coreSolveFull_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat}
    (h : (coreSolveFull p o fuel).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFullWith_unsat h

/-- Core's SAT soundness. -/
theorem coreSolve_sat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : coreSolve p o fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFull_sat h

/-- Core's UNSAT soundness. -/
theorem coreSolve_unsat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {fuel : Nat}
    (h : coreSolve p o fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFull_unsat h

/-- Core's SAT soundness with incumbent-seeded phases. -/
theorem coreSolveWith_sat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    {a : List Value} (h : coreSolveWith p o prev fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true :=
  coreSolveFullWith_sat h

/-- Core's UNSAT soundness with incumbent-seeded phases. -/
theorem coreSolveWith_unsat {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    (h : coreSolveWith p o prev fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false :=
  coreSolveFullWith_unsat h

end LeanFzn.Engine

/-
N8 runtime test: first-UIP conflict analysis over concrete array-trail
states.  The checks cover

1. a level-0 conflict explained entirely by the initial domains
   (learned clause is empty, and the enumeration evaluator accepts it);
2. a resolution step through a stored reason clause, checked by enumerating
   `allAssigns p.domains`, with the level-zero literal erased from the learned
   clause;
3. the no-claim failure path for an unexplained conflict literal;
4. an asserting result whose asserting literal occurs in the learned clause
   and whose backjump is below the current level;
5. a chain-clause step over two successive bound entries on one slot,
   checking both entailment and the prefix negations;
6. the documented `subsumeItems` identity fallback.

Run with:
  lake env lean --run Tests/Engine/AnalyzeTest.lean
-/
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Analyze

/-! ## A small compiled-problem harness -/

def T : LitTable := {}

def mkP (ds : List Dom) (cs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := [], domains := ds, constraints := cs, objective := (), source := default,
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray
    toStore := fun _ _ => none }

def litLe (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := true }

/-- `x > k`, the negative `intLe` literal. -/
def litGt (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := false }

def litNe (s : Nat) (k : Int) : Literal :=
  { atom := .intNe s k, positive := true }

/-- `x = k`, the negative `intNe` literal. -/
def litEqV (s : Nat) (k : Int) : Literal :=
  { atom := .intNe s k, positive := false }

def pl (i : Nat) (l : Literal) : PLit := { idx := i, lit := l }

def mkEntry (l : PLit) (lev slot : Nat) (prev : DomC) (r : ReasonRef) : Entry :=
  { lit := l, level := lev, reason := r, slot := slot, prev := prev }

/-- Assemble a state with empty queues, no propagators and no stored clauses. -/
def mkState (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (trail : Array Entry) (levelStart : Array Nat)
    (level : Nat) (changeIndex : Array (Array Nat))
    (reasons : Array (EClause p T)) : EngineState p T :=
  { table := T
    doms := doms
    trail := trail
    levelStart := levelStart
    level := level
    changeIndex := changeIndex
    reasonCap := #[0]
    db := {}
    reasons := reasons
    props := #[]
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := ⟨Array.replicate doms.size (0.0 : Float)⟩
    activityHeap := #[]
    phases := #[]
    restarts := 0
    stats := {} }

/-- Boolean clause evaluator over one assignment. -/
def clauseEvalB (c : Clause) (a : Assignment) : Bool :=
  c.any fun l => l.eval a == some true

/-- Enumeration check: every accepted assignment satisfies `c`. -/
def entailedB (p : CompiledProblem DomConstraint) (c : Clause) : Bool :=
  (allAssigns p.domains).all fun a => !(accepts p a) || clauseEvalB c a

/-- Turn a successful enumeration check into the propositional contract. -/
theorem entailedB_sound {p : CompiledProblem DomConstraint} {c : Clause}
    (h : entailedB p c = true) : Entailed p c := by
  intro b hb hacc
  have hall := (List.all_eq_true.mp h) b hb
  rw [Bool.or_eq_true] at hall
  rcases hall with hrej | hsat
  · rw [hacc] at hrej
    simp at hrej
  · obtain ⟨l, hl, hev⟩ := List.any_eq_true.mp hsat
    exact ⟨l, hl, beq_iff_eq.mp hev⟩

/-- Build a proof-carrying clause from an enumeration check. -/
def ect (p : CompiledProblem DomConstraint) (ls : List Literal)
    (h : entailedB p ls = true) : EClause p T :=
  EClause.ofLiterals p T ls (entailedB_sound h)

/-- Decoded literals of the learned clause (empty when the analysis failed). -/
def learnedLits {p : CompiledProblem DomConstraint} (a : Analysis p T) : List Literal :=
  match a.learned with
  | none => []
  | some ec => ec.lits.toList.map PLit.decode

/-! ## Concrete domains -/

def d3 : Dom := ⟨.holes 0 3 []⟩
def d2 : Dom := ⟨.holes 0 2 []⟩

/-- Q4 converts these medium intervals to multi-word bitsets; the test
states spell out the conversion result so `decide` sees a constructor. -/
def i3 : DomC := .bitset 0 #[15]
def i2 : DomC := .bitset 0 #[7]
def iEmpty : DomC := .boundsHoles 1 0 #[]

/-! ## Case 1: level-0 conflict, all literals false initially -/

def p1 : CompiledProblem DomConstraint := mkP [⟨.holes 1 0 []⟩] []

def init1 : Array DomC := #[iEmpty]

def st1 : EngineState p1 T := mkState p1 T #[iEmpty] #[] #[0] 0 #[] #[]

/-- The negative `intNe` literal is false on the empty initial domain. -/
def c1 : EClause p1 T := ect p1 [litEqV 0 0] (by decide)

/-! ## Case 2: a resolution step through a stored reason clause -/

/-- `x < y`, both slots `0..3`. -/
def p2 : CompiledProblem DomConstraint :=
  mkP [d3, d3] [.ltSlot 0 1, .leConstHi 1 0]

def init2 : Array DomC := #[i3, i3]

/-- `y <= 0` at level 0 (slot 1). -/
def eY2 : Entry := mkEntry (pl 0 (litLe 1 0)) 0 1 i3 .decision

/-- `x <= 0` at level 1 (slot 0), justified by `x <= 0 or y > 0`. -/
def eX2 : Entry := mkEntry (pl 0 (litLe 0 0)) 1 0 i3 (.reason 0)

/-- The reason clause `x <= 0 or y > 0`, entailed because `x < y`. -/
def c2r : EClause p2 T := ect p2 [litLe 0 0, litGt 1 0] (by decide)

def st2 : EngineState p2 T :=
  { mkState p2 T #[i3.applyLit (litLe 0 0), i3.applyLit (litLe 1 0)]
      #[eY2, eX2] #[0, 1] 1 #[#[1], #[0]] #[c2r] with reasonCap := #[0, 1] }

/-- The conflict clause `x > 0 or y > 0`, false at `x = y = 0`.  The
`y > 0` literal is level 0 (`y <= 0` is forced by `p2`), so conflict analysis
erases it and learns only `x > 0`. -/
def c2 : EClause p2 T := ect p2 [litGt 0 0, litGt 1 0] (by decide)

/-! ## Case 3: unexplained literal, no claim -/

/-- `x >= 1`, so `x > 0` is entailed but not false initially. -/
def p3 : CompiledProblem DomConstraint := mkP [d3] [.leConstLo 0 1]

def init3 : Array DomC := #[i3]

def st3 : EngineState p3 T := mkState p3 T #[i3] #[] #[0] 0 #[] #[]

def c3 : EClause p3 T := ect p3 [litGt 0 0] (by decide)

/-! ## Case 4: asserting decision at level 1 -/

def p4 : CompiledProblem DomConstraint := p3

def init4 : Array DomC := #[i3]

def st4 : EngineState p4 T :=
  { mkState p4 T #[i3.applyLit (litLe 0 0)]
      #[mkEntry (pl 0 (litLe 0 0)) 1 0 i3 .decision] #[0, 0] 1 #[#[0]] #[]
    with reasonCap := #[0, 0] }

def c4 : EClause p4 T := ect p4 [litGt 0 0] (by decide)

/-! ## Case 5: chain clause over two bound entries on slot 0 -/

/-- `x < y`, both slots `0..2`. -/
def p5 : CompiledProblem DomConstraint :=
  mkP [d2, d2] [.ltSlot 0 1, .leConstHi 1 0]

def init5 : Array DomC := #[i2, i2]

/-- `y <= 0` at level 0 (slot 1). -/
def eY5 : Entry := mkEntry (pl 0 (litLe 1 0)) 0 1 i2 .decision

/-- First slot-0 change: `x <= 1` at level 0. -/
def e05 : Entry := mkEntry (pl 0 (litLe 0 1)) 0 0 i2 .decision

/-- Second slot-0 change: `x <= 0` at level 1, justified by `x <= 0 or y > 0`. -/
def e15 : Entry :=
  mkEntry (pl 0 (litLe 0 0)) 1 0 (i2.applyLit (litLe 0 1)) (.reason 0)

def c5r : EClause p5 T := ect p5 [litLe 0 0, litGt 1 0] (by decide)

def st5 : EngineState p5 T :=
  { mkState p5 T #[i2.applyLit (litLe 0 0), i2.applyLit (litLe 1 0)]
      #[eY5, e05, e15] #[0, 2] 1 #[#[1, 2], #[0]] #[c5r] with reasonCap := #[0, 1] }

/-- The conflict clause `x != 0 or y != 0`, false at `x = y = 0`.  The
`y != 0` literal is level 0 (`y <= 0` is forced by `p5`), so conflict analysis
erases it and learns only `x != 0`. -/
def c5 : EClause p5 T := ect p5 [litNe 0 0, litNe 1 0] (by decide)

/-! ## Case 6: the documented subsumption fallback -/

def itA : CItem := { lit := litLe 0 1, pos := 0, level := 0, cidx := 0 }
def itB : CItem := { lit := litLe 0 2, pos := 1, level := 0, cidx := 1 }

def items6 : Array CItem := #[itA, itB]

/-! ## History witnesses for the concrete states -/

theorem slotHistory_st1 : SlotHistory init1 st1 :=
  slotHistory_init init1 st1 rfl rfl
    (by intro s; simp [st1, mkState, EngineState.changeList])

theorem slotHistory_st2 : SlotHistory init2 st2 := by
  constructor
  · intro s
    match s with
    | 0 => decide
    | 1 => decide
    | n + 2 =>
        have h2 : ¬ n + 2 < 2 := Nat.not_lt.mpr (Nat.le_add_left 2 n)
        have h2' : ¬ n + 2 < init2.size := by simpa [init2] using h2
        have h2'' : ¬ n + 2 < st2.changeIndex.size := by simp [st2, mkState]
        simp [st2, mkState, EngineState.changeList, domAfter, Array.getD,
          h2, h2', h2'', init2]
  · intro s k hk
    match s with
    | 0 =>
        have hk1 : k < 1 := by
          simpa [st2, mkState, EngineState.changeList, Array.getD] using hk
        have hk0 : k = 0 := by omega
        subst hk0
        decide
    | 1 =>
        have hk1 : k < 1 := by
          simpa [st2, mkState, EngineState.changeList, Array.getD] using hk
        have hk0 : k = 0 := by omega
        subst hk0
        decide
    | n + 2 =>
        have h2 : ¬ n + 2 < 2 := Nat.not_lt.mpr (Nat.le_add_left 2 n)
        have h2'' : ¬ n + 2 < st2.changeIndex.size := by simp [st2, mkState]
        simp [st2, mkState, EngineState.changeList, Array.getD, h2, h2''] at hk

theorem slotHistory_st3 : SlotHistory init3 st3 :=
  slotHistory_init init3 st3 rfl rfl
    (by intro s; simp [st3, mkState, EngineState.changeList])

theorem slotHistory_st4 : SlotHistory init4 st4 := by
  constructor
  · intro s
    match s with
    | 0 => decide
    | n + 1 =>
        have h2 : ¬ n + 1 < 1 := Nat.not_lt.mpr (Nat.le_add_left 1 n)
        have h2' : ¬ n + 1 < init4.size := by simpa [init4] using h2
        have h2'' : ¬ n + 1 < st4.changeIndex.size := by simp [st4, mkState]
        simp [st4, mkState, EngineState.changeList, domAfter, Array.getD,
          h2, h2', h2'', init4]
  · intro s k hk
    match s with
    | 0 =>
        have hk1 : k < 1 := by
          simpa [st4, mkState, EngineState.changeList, Array.getD] using hk
        have hk0 : k = 0 := by omega
        subst hk0
        decide
    | n + 1 =>
        have h2 : ¬ n + 1 < 1 := Nat.not_lt.mpr (Nat.le_add_left 1 n)
        have h2'' : ¬ n + 1 < st4.changeIndex.size := by simp [st4, mkState]
        simp [st4, mkState, EngineState.changeList, Array.getD, h2, h2''] at hk

theorem slotHistory_st5 : SlotHistory init5 st5 := by
  constructor
  · intro s
    match s with
    | 0 => decide
    | 1 => decide
    | n + 2 =>
        have h2 : ¬ n + 2 < 2 := Nat.not_lt.mpr (Nat.le_add_left 2 n)
        have h2' : ¬ n + 2 < init5.size := by simpa [init5] using h2
        have h2'' : ¬ n + 2 < st5.changeIndex.size := by simp [st5, mkState]
        simp [st5, mkState, EngineState.changeList, domAfter, Array.getD,
          h2, h2', h2'', init5]
  · intro s k hk
    match s with
    | 0 =>
        have hk2 : k < 2 := by
          simpa [st5, mkState, EngineState.changeList, Array.getD] using hk
        match k with
        | 0 => decide
        | 1 => decide
        | m + 2 => omega
    | 1 =>
        have hk1 : k < 1 := by
          simpa [st5, mkState, EngineState.changeList, Array.getD] using hk
        have hk0 : k = 0 := by omega
        subst hk0
        decide
    | n + 2 =>
        have h2 : ¬ n + 2 < 2 := Nat.not_lt.mpr (Nat.le_add_left 2 n)
        have h2'' : ¬ n + 2 < st5.changeIndex.size := by simp [st5, mkState]
        simp [st5, mkState, EngineState.changeList, Array.getD, h2, h2''] at hk

/-! ## Conversion witnesses for the concrete problems -/

theorem initConv_st1 : InitConv p1 init1 := by
  constructor
  intro s hs
  match s with
  | 0 => decide +kernel
  | n + 1 => simp [p1, mkP] at hs

theorem initConv_st2 : InitConv p2 init2 := by
  constructor
  intro s hs
  match s with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | n + 2 => simp [p2, mkP] at hs; omega

theorem initConv_st3 : InitConv p3 init3 := by
  constructor
  intro s hs
  match s with
  | 0 => decide +kernel
  | n + 1 => simp [p3, mkP] at hs

theorem initConv_st4 : InitConv p4 init4 := initConv_st3

theorem initConv_st5 : InitConv p5 init5 := by
  constructor
  intro s hs
  match s with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | n + 2 => simp [p5, mkP] at hs; omega

/-! ## `InitInv` and root invariants for the concrete states -/

theorem initInv_st1 : InitInv p1 init1 :=
  initInv_of_convertDomains (by decide +kernel)

theorem initInv_st2 : InitInv p2 init2 :=
  initInv_of_convertDomains (by decide +kernel)

theorem initInv_st3 : InitInv p3 init3 :=
  initInv_of_convertDomains (by decide +kernel)

theorem initInv_st4 : InitInv p4 init4 := initInv_st3

theorem initInv_st5 : InitInv p5 init5 :=
  initInv_of_convertDomains (by decide +kernel)

/-- Transport `TrailInv` across states that agree on the fields it reads. -/
theorem TrailInv.of_eq_fields {p : CompiledProblem DomConstraint} {T : LitTable}
    {st st' : EngineState p T} (h : TrailInv st)
    (htr : st'.trail = st.trail) (hls : st'.levelStart = st.levelStart)
    (hl : st'.level = st.level)
    (hci : ∀ s, st'.changeList s = st.changeList s)
    (hrc : st'.reasonCap = st.reasonCap) : TrailInv st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hls]; exact h.levelStart_zero
  · rw [hls, hl]; exact h.levelStart_size
  · rw [hls]; exact h.levelStart_sorted
  · intro i hi
    rw [hls] at hi ⊢
    rw [htr]
    exact h.levelStart_le_trail i hi
  · intro i e he
    rw [htr] at he
    rw [hls]
    exact h.entry_level i e he
  · intro i e he
    rw [htr] at he
    rw [hls]
    exact h.entry_levelStart_le i e he
  · intro s
    rw [hci s]
    exact h.changeIndex_sorted s
  · intro s q
    rw [hci s, htr]
    exact h.changeIndex_mem s q
  · rw [hrc, hl]; exact h.reasonCap_size
  · intro k hk
    rw [hrc] at hk ⊢
    rw [htr, hls]
    exact h.reasonCap_exact k hk

/-- Trail-invariant witnesses for the empty states. -/
theorem trailInv_st1 : TrailInv st1 :=
  trailInv_init rfl rfl rfl
    (fun s => by simp [st1, mkState, EngineState.changeList]) rfl

theorem trailInv_st3 : TrailInv st3 :=
  trailInv_init rfl rfl rfl
    (fun s => by simp [st3, mkState, EngineState.changeList]) rfl

/-- The operational construction of `st2` starts from an empty level-0
state and pushes the same entries. -/
def st2base : EngineState p2 T := mkState p2 T #[i3, i3] #[] #[0] 0 #[] #[]

def st2c : EngineState p2 T :=
  trailPush (newLevel (trailPush st2base eY2)) eX2

theorem trailInv_st2c : TrailInv st2c := by
  apply trailPush_trailInv
  · apply newLevel_trailInv
    apply trailPush_trailInv
    exact trailInv_init rfl rfl rfl
      (fun s => by simp [st2base, mkState, EngineState.changeList]) rfl
    rfl
  rfl

theorem trailInv_st2 : TrailInv st2 :=
  TrailInv.of_eq_fields trailInv_st2c rfl rfl rfl (fun s => rfl) rfl

theorem levelMono_st2base : LevelMono st2base := by
  intro i j e1 e2 hi hj hij
  simp [st2base, mkState] at hi

theorem levelMono_st2c : LevelMono st2c := by
  have h1 : LevelMono (trailPush st2base eY2) :=
    levelMono_trailPush levelMono_st2base (e := eY2) rfl
      (by intro i e' hi; simp [st2base, mkState] at hi)
  have h2 : LevelMono (newLevel (trailPush st2base eY2)) :=
    levelMono_of_trail h1 rfl
  exact levelMono_trailPush h2 (e := eX2) rfl (by
    intro i e' hi
    match i with
    | 0 =>
        simp [newLevel, trailPush, st2base, mkState] at hi
        subst e'
        decide
    | n + 1 =>
        simp [newLevel, trailPush, st2base, mkState] at hi)

theorem levelMono_st2 : LevelMono st2 :=
  levelMono_of_trail levelMono_st2c rfl

theorem rootTrail_st2 : RootTrail p2 T st2 := by
  intro i e hi h0
  match i with
  | 0 =>
      simp [st2, mkState, eY2] at hi
      subst e
      refine ⟨?_, rfl⟩
      change Entailed p2 [litLe 1 0]
      simpa using entailedB_sound (p := p2) (c := [litLe 1 0]) (by decide)
  | 1 =>
      simp [st2, mkState, eX2] at hi
      subst e
      simp [eX2, mkEntry] at h0
  | n + 2 =>
      simp [st2, mkState] at hi

/-- Operational construction of `st4`. -/
def st4base : EngineState p4 T := mkState p4 T #[i3] #[] #[0] 0 #[] #[]

def st4entry : Entry := mkEntry (pl 0 (litLe 0 0)) 1 0 i3 .decision

def st4c : EngineState p4 T := trailPush (newLevel st4base) st4entry

theorem trailInv_st4c : TrailInv st4c := by
  apply trailPush_trailInv
  apply newLevel_trailInv
  exact trailInv_init rfl rfl rfl
    (fun s => by simp [st4base, mkState, EngineState.changeList]) rfl
  decide

theorem trailInv_st4 : TrailInv st4 :=
  TrailInv.of_eq_fields trailInv_st4c rfl rfl rfl (fun s => rfl) rfl

theorem levelMono_st4base : LevelMono st4base := by
  intro i j e1 e2 hi hj hij
  simp [st4base, mkState] at hi

theorem levelMono_st4c : LevelMono st4c := by
  have h1 : LevelMono (newLevel st4base) := levelMono_of_trail levelMono_st4base rfl
  exact levelMono_trailPush h1 (e := st4entry) rfl (by
    intro i e' hi
    simp [newLevel, st4base, mkState] at hi)

theorem levelMono_st4 : LevelMono st4 :=
  levelMono_of_trail levelMono_st4c rfl

theorem rootTrail_st4 : RootTrail p4 T st4 := by
  intro i e hi h0
  match i with
  | 0 =>
      simp [st4, mkState] at hi
      subst e
      simp [st4entry, mkEntry] at h0
  | n + 1 =>
      simp [st4, mkState] at hi

/-- Operational construction of `st5`. -/
def st5base : EngineState p5 T := mkState p5 T #[i2, i2] #[] #[0] 0 #[] #[]

def st5c : EngineState p5 T :=
  trailPush (newLevel (trailPush (trailPush st5base eY5) e05)) e15

theorem trailInv_st5c : TrailInv st5c := by
  have h0 : TrailInv st5base :=
    trailInv_init rfl rfl rfl
      (fun s => by simp [st5base, mkState, EngineState.changeList]) rfl
  have h1 : TrailInv (trailPush st5base eY5) :=
    trailPush_trailInv h0 (e := eY5) rfl
  have h2 : TrailInv (trailPush (trailPush st5base eY5) e05) :=
    trailPush_trailInv h1 (e := e05) rfl
  have h3 : TrailInv (newLevel (trailPush (trailPush st5base eY5) e05)) :=
    newLevel_trailInv h2
  exact trailPush_trailInv h3 (e := e15) rfl

theorem trailInv_st5 : TrailInv st5 :=
  TrailInv.of_eq_fields trailInv_st5c rfl rfl rfl (fun s => rfl) rfl

theorem levelMono_st5base : LevelMono st5base := by
  intro i j e1 e2 hi hj hij
  simp [st5base, mkState] at hi

theorem levelMono_st5c : LevelMono st5c := by
  have h1 : LevelMono (trailPush st5base eY5) :=
    levelMono_trailPush levelMono_st5base (e := eY5) rfl
      (by intro i e' hi; simp [st5base, mkState] at hi)
  have h2 : LevelMono (trailPush (trailPush st5base eY5) e05) :=
    levelMono_trailPush h1 (e := e05) rfl (by
      intro i e' hi
      match i with
      | 0 =>
          simp [trailPush, st5base, mkState] at hi
          subst e'
          decide
      | n + 1 =>
          simp [trailPush, st5base, mkState] at hi)
  have h3 : LevelMono (newLevel (trailPush (trailPush st5base eY5) e05)) :=
    levelMono_of_trail h2 rfl
  exact levelMono_trailPush h3 (e := e15) rfl (by
    intro i e' hi
    match i with
    | 0 =>
        simp [newLevel, trailPush, st5base, mkState] at hi
        subst e'
        decide
    | 1 =>
        simp [newLevel, trailPush, st5base, mkState] at hi
        subst e'
        decide
    | n + 2 =>
        simp [newLevel, trailPush, st5base, mkState] at hi)

theorem levelMono_st5 : LevelMono st5 :=
  levelMono_of_trail levelMono_st5c rfl

theorem rootTrail_st5 : RootTrail p5 T st5 := by
  intro i e hi h0
  match i with
  | 0 =>
      simp [st5, mkState, eY5] at hi
      subst e
      refine ⟨?_, rfl⟩
      change Entailed p5 [litLe 1 0]
      simpa using entailedB_sound (p := p5) (c := [litLe 1 0]) (by decide)
  | 1 =>
      simp [st5, mkState, e05] at hi
      subst e
      refine ⟨?_, rfl⟩
      change Entailed p5 [litLe 0 1]
      simpa using entailedB_sound (p := p5) (c := [litLe 0 1]) (by decide)
  | 2 =>
      simp [st5, mkState, e15] at hi
      subst e
      simp [e15, mkEntry] at h0
  | n + 3 =>
      simp [st5, mkState] at hi

/-! ## Root invariants for the concrete states -/

theorem rootInv_st1 : RootInv p1 T init1 st1 :=
  { hist := ⟨slotHistory_st1, trailInv_st1⟩
    init_inv := initInv_st1
    table_inv := LitTable.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [st1, mkState, ClauseDB.empty] at hget
    level_mono := by
      intro i j e1 e2 hi hj hij
      simp [st1, mkState] at hi
    root := by
      intro i e hi h0
      simp [st1, mkState] at hi
    conv := initConv_st1
    db_inv := ClauseDB.inv_empty }

theorem rootInv_st2 : RootInv p2 T init2 st2 :=
  { hist := ⟨slotHistory_st2, trailInv_st2⟩
    init_inv := initInv_st2
    table_inv := LitTable.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [st2, mkState, ClauseDB.empty] at hget
    level_mono := levelMono_st2
    root := rootTrail_st2
    conv := initConv_st2
    db_inv := ClauseDB.inv_empty }

theorem rootInv_st3 : RootInv p3 T init3 st3 :=
  { hist := ⟨slotHistory_st3, trailInv_st3⟩
    init_inv := initInv_st3
    table_inv := LitTable.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [st3, mkState, ClauseDB.empty] at hget
    level_mono := by
      intro i j e1 e2 hi hj hij
      simp [st3, mkState] at hi
    root := by
      intro i e hi h0
      simp [st3, mkState] at hi
    conv := initConv_st3
    db_inv := ClauseDB.inv_empty }

theorem rootInv_st4 : RootInv p4 T init4 st4 :=
  { hist := ⟨slotHistory_st4, trailInv_st4⟩
    init_inv := initInv_st4
    table_inv := LitTable.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [st4, mkState, ClauseDB.empty] at hget
    level_mono := levelMono_st4
    root := rootTrail_st4
    conv := initConv_st4
    db_inv := ClauseDB.inv_empty }

theorem rootInv_st5 : RootInv p5 T init5 st5 :=
  { hist := ⟨slotHistory_st5, trailInv_st5⟩
    init_inv := initInv_st5
    table_inv := LitTable.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [st5, mkState, ClauseDB.empty] at hget
    level_mono := levelMono_st5
    root := rootTrail_st5
    conv := initConv_st5
    db_inv := ClauseDB.inv_empty }

/-! ## Compile-time spot checks -/

example : (analyze p1 T init1 st1 initConv_st1 slotHistory_st1 rootInv_st1 c1 8).ok = true := by decide +kernel

example : ∃ ec, (analyze p2 T init2 st2 initConv_st2 slotHistory_st2 rootInv_st2 c2 8).learned = some ec ∧
    Entailed p2 (T.decodeClause ec.lits) := by
  refine analyze_sound (init := init2) (st := st2) (conflict := c2)
    (fuel := 8) initConv_st2 slotHistory_st2 rootInv_st2 ?_
  decide +kernel

example : (analyze p3 T init3 st3 initConv_st3 slotHistory_st3 rootInv_st3 c3 8).ok = false := by decide +kernel

example : ∀ ec l, (analyze p4 T init4 st4 initConv_st4 slotHistory_st4 rootInv_st4 c4 8).learned = some ec →
    (analyze p4 T init4 st4 initConv_st4 slotHistory_st4 rootInv_st4 c4 8).asserting = some l →
      l.lit ∈ ec.lits.toList.map PLit.decode := by
  intro ec l hlearned hassserting
  exact analyze_asserting_mem initConv_st4 slotHistory_st4 rootInv_st4 hlearned hassserting


/-! ## Runtime checks -/

def check (name : String) (cond : Bool) : IO Nat :=
  if cond then
    pure 0
  else do
    IO.eprintln s!"FAIL: {name}"
    pure 1

def main : IO Unit := do
  let mut fails := 0

  -- Case 1
  let a1 := analyze p1 T init1 st1 initConv_st1 slotHistory_st1 rootInv_st1 c1 8
  fails := fails + (← check "case1 ok" (a1.ok == true))
  fails := fails + (← check "case1 learned is some" a1.learned.isSome)
  fails := fails + (← check "case1 learned clause empty"
    (match a1.learned with
     | some ec => ec.lits.isEmpty
     | none => false))
  fails := fails + (← check "case1 decoded lits empty" (learnedLits a1 == []))
  fails := fails + (← check "case1 enumeration entailed"
    (entailedB p1 (learnedLits a1) == true))
  fails := fails + (← check "case1 backjump zero" (a1.backjump == 0))
  fails := fails + (← check "case1 no asserting" (a1.asserting == none))

  -- Case 2
  let a2 := analyze p2 T init2 st2 initConv_st2 slotHistory_st2 rootInv_st2 c2 8
  fails := fails + (← check "case2 ok" (a2.ok == true))
  fails := fails + (← check "case2 learned is some" a2.learned.isSome)
  fails := fails + (← check "case2 learned lits erase the level-zero literal"
    (learnedLits a2 == [litGt 0 0]))
  fails := fails + (← check "case2 level-zero literal is not learned"
    (!(learnedLits a2).contains (litGt 1 0)))
  fails := fails + (← check "case2 enumeration entailed"
    (entailedB p2 (learnedLits a2) == true))
  fails := fails + (← check "case2 backjump zero" (a2.backjump == 0))

  -- Case 3
  let a3 := analyze p3 T init3 st3 initConv_st3 slotHistory_st3 rootInv_st3 c3 8
  fails := fails + (← check "case3 fails" (a3.ok == false))
  fails := fails + (← check "case3 no learned clause" a3.learned.isNone)
  fails := fails + (← check "case3 has a reason" (!a3.why.isEmpty))

  -- Case 4
  let a4 := analyze p4 T init4 st4 initConv_st4 slotHistory_st4 rootInv_st4 c4 8
  fails := fails + (← check "case4 ok" (a4.ok == true))
  fails := fails + (← check "case4 asserting is x > 0"
    (a4.asserting == some (pl 0 (litGt 0 0))))
  fails := fails + (← check "case4 learned is x > 0"
    (learnedLits a4 == [litGt 0 0]))
  fails := fails + (← check "case4 asserting literal in learned clause"
    (match a4.asserting with
     | some l => (learnedLits a4).contains l.lit
     | none => false))
  fails := fails + (← check "case4 backjump below current level"
    (a4.backjump < st4.level))
  fails := fails + (← check "case4 enumeration entailed"
    (entailedB p4 (learnedLits a4) == true))

  -- Case 5
  let a5 := analyze p5 T init5 st5 initConv_st5 slotHistory_st5 rootInv_st5 c5 8
  fails := fails + (← check "case5 ok" (a5.ok == true))
  fails := fails + (← check "case5 learned lits erase the level-zero literal"
    (learnedLits a5 == [litNe 0 0]))
  fails := fails + (← check "case5 level-zero literal is not learned"
    (!(learnedLits a5).contains (litNe 1 0)))
  fails := fails + (← check "case5 first-UIP stops before the chain step"
    (!((learnedLits a5).contains (litGt 0 1))))
  fails := fails + (← check "case5 chain clause has both prefix negations"
    (let c := (chainReasonLits st5 0 2 (litNe 0 0)).toList
     c.contains (litGt 0 1) && c.contains (litGt 0 0)))
  fails := fails + (← check "case5 enumeration entailed"
    (entailedB p5 (learnedLits a5) == true))

  -- Case 6 (`subsumeItems` is the documented identity fallback)
  fails := fails + (← check "case6 subsumeItems keeps the item list"
    (subsumeItems items6 == items6))
  fails := fails + (← check "case6 subsumeItems keeps both literals"
    ((subsumeItems items6).toList.map (fun it => it.lit) ==
      [litLe 0 1, litLe 0 2]))

  if fails == 0 then
    IO.println "AnalyzeTest: all checks passed"
  else do
    IO.eprintln s!"AnalyzeTest: {fails} check(s) failed"
    IO.Process.exit 1

end Tests.Engine.Analyze

def main (_args : List String) : IO UInt32 := do
  Tests.Engine.Analyze.main
  pure 0

/-
File: LeanFzn/Engine/Props/Arith.lean

Dedicated arithmetic propagators for the Core engine: `int_plus`,
`int_min`, `int_max`, `int_abs`, the general two-operand `int_min` /
`int_max`, and the array forms `array_int_minimum` /
`array_int_maximum`.  The first stage implements interval propagation
over a small operand box; the semantic bridge of each constraint is
proved once and every emitted clause is derived from it.

A `GArg` is an operand (slot or integer literal) together with its
current interval and a proposed interval.  A propagation step narrows
the proposed intervals using only the current endpoints.  If some
proposed interval is empty the propagator reports a conflict consisting
of the negations of all current bound facts.  Otherwise each strictly
narrowed slot emits the implied bound literal; its reason is the
current bound facts plus the new literal.

Dependencies:
  - LeanFzn.Engine.Props.Linear: `ViewWF`, `linBoundAt`, bound helpers.
  - LeanFzn.Solver.Propagation.Proofs.Fam.Arith: the arithmetic corner
    facts reused by the later `times`/`div`/`mod` stages.

DAG: LeanFzn.Engine.Prop -> LeanFzn.Engine.Props.Linear ->
     LeanFzn.Engine.Props.Arith
-/
import LeanFzn.Engine.Props.Linear
import LeanFzn.Solver.Propagation.Proofs.Fam.Arith
import LeanFzn.Solver.Propagation.Proofs.Fam.Times

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Bound literals -/

/-- The literal "slot `s` is below `lo`": `s ≤ lo - 1`.  It is false on
a view whose lower bound is exactly `lo`. -/
def loLit (s : Nat) (lo : Int) : Literal := posLe s (lo - 1)

/-- The literal "slot `s` is above `hi`": `s > hi`.  It is false on a
view whose upper bound is exactly `hi`. -/
def hiLit (s : Nat) (hi : Int) : Literal := negLe s hi

/-- The literal "slot `s` is at least `v`": `s > v - 1`. -/
def geLit (s : Nat) (v : Int) : Literal := negLe s (v - 1)

/-- The literal "slot `s` is at most `v`": `s ≤ v`. -/
def leLit (s : Nat) (v : Int) : Literal := posLe s v

@[simp] theorem atomSlot_loLit (s : Nat) (lo : Int) :
    (loLit s lo).atom = .intLe s (lo - 1) := rfl

@[simp] theorem atomSlot_hiLit (s : Nat) (hi : Int) :
    (hiLit s hi).atom = .intLe s hi := rfl

@[simp] theorem atomSlot_geLit (s : Nat) (v : Int) :
    (geLit s v).atom = .intLe s (v - 1) := rfl

@[simp] theorem atomSlot_leLit (s : Nat) (v : Int) :
    (leLit s v).atom = .intLe s v := rfl

/-- A lower-bound literal is false on a well-formed domain with that
lower and a compatible upper bound. -/
theorem loLit_eval_false {d : DomC} (hWF : d.WF) {s : Nat} {lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) :
    d.evalLit (loLit s lo) = some false := by
  have hle := DomC.lo?_le_hi? d hWF hlo hhi
  simp only [DomC.evalLit, loLit, posLe, hlo, hhi, ↓reduceIte]
  rw [if_neg (by omega), if_pos (by omega)]

/-- An upper-bound literal is false on a well-formed domain with that
upper and a compatible lower bound. -/
theorem hiLit_eval_false {d : DomC} (hWF : d.WF) {s : Nat} {lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) :
    d.evalLit (hiLit s hi) = some false := by
  have hle := DomC.lo?_le_hi? d hWF hlo hhi
  simp only [DomC.evalLit, hiLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by omega), if_pos (by omega)]

/-- If a lower-bound literal is not true then the integer view is at
least the bound. -/
theorem le_of_loLit_not_true {a : Assignment} {s : Nat} {lo x : Int}
    (hx : slotInt a s = some x) (h : (loLit s lo).eval a ≠ some true) :
    lo ≤ x := by
  by_cases hle : lo ≤ x
  · exact hle
  · exact absurd (by
      rw [loLit, eval_posLe_iff]
      exact ⟨x, hx, by omega⟩) h

/-- If an upper-bound literal is not true then the integer view is at
most the bound. -/
theorem le_of_hiLit_not_true {a : Assignment} {s : Nat} {hi x : Int}
    (hx : slotInt a s = some x) (h : (hiLit s hi).eval a ≠ some true) :
    x ≤ hi := by
  by_cases hle : x ≤ hi
  · exact hle
  · exact absurd (by
      rw [hiLit, eval_negLe_iff]
      exact ⟨x, hx, by omega⟩) h

/-! ## A three-operand interval box -/

/-- One operand of a general arithmetic constraint with its current
interval `[lo, hi]` and the interval `[nlo, nhi]` proposed by the
propagator. -/
structure GArg where
  arg : DomIntArg
  lo : Int
  hi : Int
  nlo : Int
  nhi : Int
  deriving Repr, DecidableEq

/-- Current-interval membership. -/
def GArg.Cur (g : GArg) (x : Int) : Prop := g.lo ≤ x ∧ x ≤ g.hi

/-- Proposed-interval membership. -/
def GArg.New (g : GArg) (x : Int) : Prop := g.nlo ≤ x ∧ x ≤ g.nhi

/-- The proposed interval is contained in the current one. -/
def GArg.Sub (g : GArg) : Prop := g.lo ≤ g.nlo ∧ g.nhi ≤ g.hi

/-- For a literal operand the current interval is the singleton carrying
the literal; for a slot operand there is nothing to check because the
bound literals themselves describe the interval. -/
def GArg.CurSpec (g : GArg) : Prop :=
  match g.arg with
  | .lit k => g.lo = k ∧ g.hi = k
  | .slot _ => True

/-- The current bounds of a slot operand are the actual domain bounds,
and a literal operand carries its own value.  This is the link to the
view needed by the emitted-conflict-literal contracts. -/
def GArg.BoundSpec (doms : Array DomC) (g : GArg) : Prop :=
  match g.arg with
  | .lit k => g.lo = k ∧ g.hi = k
  | .slot s =>
      (doms.getD s DomC.empty).lo? = some g.lo ∧
        (doms.getD s DomC.empty).hi? = some g.hi

/-- Well-formedness of the domain behind a slot operand. -/
def GArg.WF (view : EngineView) (g : GArg) : Prop :=
  match g.arg with
  | .lit _ => True
  | .slot s => (view.doms.getD s DomC.empty).WF

/-- The two current-bound literals of a slot operand; a literal operand
contributes none because its value is known exactly. -/
def GArg.lits (g : GArg) : List Literal :=
  match g.arg with
  | .lit _ => []
  | .slot s => [loLit s g.lo, hiLit s g.hi]

/-- Intersection with a proposed interval. -/
def GArg.intersect (g : GArg) (lo hi : Int) : GArg :=
  { g with nlo := max g.lo lo, nhi := min g.hi hi }

/-- The prunes generated by a narrowing slot operand: a lower prune when
the proposed lower bound rises, an upper prune when the proposed upper
bound falls.  Each reason is all current bound literals plus the new
literal. -/
def GArg.prunes (g : GArg) (boxLits : List Literal) :
    List (Literal × List Literal) :=
  match g.arg with
  | .lit _ => []
  | .slot s =>
      (if g.lo < g.nlo then
        [(geLit s g.nlo, boxLits ++ [geLit s g.nlo])]
       else []) ++
      (if g.nhi < g.hi then
        [(leLit s g.nhi, boxLits ++ [leLit s g.nhi])]
       else [])

/-- A three-operand interval box. -/
structure GBox where
  g0 : GArg
  g1 : GArg
  g2 : GArg
  deriving Repr, DecidableEq

/-- Every current bound literal of the box. -/
def GBox.lits (b : GBox) : List Literal :=
  b.g0.lits ++ b.g1.lits ++ b.g2.lits

/-- The prunes generated by the three narrowed operands. -/
def GBox.prunes (b : GBox) : List (Literal × List Literal) :=
  b.g0.prunes b.lits ++ b.g1.prunes b.lits ++ b.g2.prunes b.lits

/-- The box has an empty proposed interval. -/
def GBox.emptyNew (b : GBox) : Bool :=
  (b.g0.nlo > b.g0.nhi) || (b.g1.nlo > b.g1.nhi) || (b.g2.nlo > b.g2.nhi)

/-- The computed output of a box: conflict, a batch of prunes, or no
change. -/
inductive GOut where
  | fix
  | conflict (lits : List Literal)
  | prune (items : List (Literal × List Literal))
  deriving Repr, DecidableEq

/-- Turn a propagated box into its output.  A conflict takes priority;
an empty prune batch is reported as `.fix`. -/
def GBox.out (b : GBox) : GOut :=
  if b.emptyNew then .conflict b.lits
  else
    let ps := b.prunes
    if ps.isEmpty then .fix else .prune ps

def GBox.CurSpec (b : GBox) : Prop :=
  b.g0.CurSpec ∧ b.g1.CurSpec ∧ b.g2.CurSpec

def GBox.BoundSpec (doms : Array DomC) (b : GBox) : Prop :=
  b.g0.BoundSpec doms ∧ b.g1.BoundSpec doms ∧ b.g2.BoundSpec doms

def GBox.WF (view : EngineView) (b : GBox) : Prop :=
  b.g0.WF view ∧ b.g1.WF view ∧ b.g2.WF view

/-- Soundness of one propagation step: every relation tuple inside the
current box stays inside the proposed box.  `Sub` records that the
proposed box is a genuine narrowing. -/
structure GSpec (R : Int → Int → Int → Prop) (b : GBox) : Prop where
  sub0 : b.g0.Sub
  sub1 : b.g1.Sub
  sub2 : b.g2.Sub
  sound : ∀ x y z, b.g0.Cur x → b.g1.Cur y → b.g2.Cur z → R x y z →
    b.g0.New x ∧ b.g1.New y ∧ b.g2.New z

/-! ## Reading the operand boxes from a view -/

/-- The current interval of an operand: a literal is its own singleton,
a slot is read through `linBoundAt`. -/
def argBounds? (doms : Array DomC) : DomIntArg → Option (Int × Int)
  | .lit k => some (k, k)
  | .slot s =>
      match doms.getD s DomC.empty with
      | .bool _ => none
      | _ => linBoundAt doms s

theorem argBounds?_lit {doms : Array DomC} {k lo hi : Int}
    (h : argBounds? doms (.lit k) = some (lo, hi)) : lo = k ∧ hi = k := by
  simp [argBounds?] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem argBounds?_slot {doms : Array DomC} {s : Nat} {lo hi : Int}
    (h : argBounds? doms (.slot s) = some (lo, hi)) :
    (doms.getD s DomC.empty).lo? = some lo ∧
      (doms.getD s DomC.empty).hi? = some hi := by
  unfold argBounds? at h
  cases hd : doms.getD s DomC.empty with
  | bool bits => simp [hd] at h
  | bounds lo' hi' =>
      simp [hd] at h
      simpa [hd] using linBoundAt_spec h
  | bitset lo' words =>
      simp [hd] at h
      simpa [hd] using linBoundAt_spec h
  | boundsHoles lo' hi' holes =>
      simp [hd] at h
      simpa [hd] using linBoundAt_spec h
  | sparse values =>
      simp [hd] at h
      simpa [hd] using linBoundAt_spec h

/-- Build the initial box of one operand. -/
def mkGArg? (doms : Array DomC) (a : DomIntArg) : Option GArg :=
  match argBounds? doms a with
  | none => none
  | some (lo, hi) => some ⟨a, lo, hi, lo, hi⟩

theorem mkGArg?_bounds {doms : Array DomC} {a : DomIntArg} {g : GArg}
    (h : mkGArg? doms a = some g) : g.BoundSpec doms := by
  unfold mkGArg? at h
  split at h
  · cases h
  · rename_i lo hi hb
    injection h with hg
    subst hg
    cases a with
    | lit k =>
        have hk := argBounds?_lit hb
        simp [GArg.BoundSpec, hk.1, hk.2]
    | slot s =>
        have hs := argBounds?_slot hb
        simpa [GArg.BoundSpec] using hs

theorem mkGArg?_curSpec {doms : Array DomC} {a : DomIntArg} {g : GArg}
    (h : mkGArg? doms a = some g) : g.CurSpec := by
  unfold mkGArg? at h
  split at h
  · cases h
  · rename_i lo hi hb
    injection h with hg
    subst hg
    cases a with
    | lit k =>
        have hk := argBounds?_lit hb
        simp [GArg.CurSpec, hk.1, hk.2]
    | slot s => simp [GArg.CurSpec]

theorem mkGArg?_arg {doms : Array DomC} {a : DomIntArg} {g : GArg}
    (h : mkGArg? doms a = some g) : g.arg = a := by
  unfold mkGArg? at h
  split at h
  · cases h
  · rename_i lo hi hb
    injection h with hg
    subst hg
    rfl

/-- The operand triple of a general constraint. -/
def mkGBox? (doms : Array DomC) (a0 a1 a2 : DomIntArg) : Option GBox :=
  match mkGArg? doms a0, mkGArg? doms a1, mkGArg? doms a2 with
  | some g0, some g1, some g2 => some ⟨g0, g1, g2⟩
  | _, _, _ => none

theorem mkGBox?_bounds {doms : Array DomC} {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? doms a0 a1 a2 = some b) : b.BoundSpec doms := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    exact ⟨mkGArg?_bounds h0, mkGArg?_bounds h1, mkGArg?_bounds h2⟩
  · cases h

theorem mkGBox?_curSpec {doms : Array DomC} {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? doms a0 a1 a2 = some b) : b.CurSpec := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    exact ⟨mkGArg?_curSpec h0, mkGArg?_curSpec h1, mkGArg?_curSpec h2⟩
  · cases h

theorem mkGBox?_arg0 {doms : Array DomC} {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? doms a0 a1 a2 = some b) : b.g0.arg = a0 := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    exact mkGArg?_arg h0
  · cases h

theorem mkGBox?_arg1 {doms : Array DomC} {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? doms a0 a1 a2 = some b) : b.g1.arg = a1 := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    exact mkGArg?_arg h1
  · cases h

theorem mkGBox?_arg2 {doms : Array DomC} {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? doms a0 a1 a2 = some b) : b.g2.arg = a2 := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    exact mkGArg?_arg h2
  · cases h

theorem mkGBox?_wf {view : EngineView} {slots : Array Nat}
    {a0 a1 a2 : DomIntArg} {b : GBox}
    (h : mkGBox? view.doms a0 a1 a2 = some b)
    (hWF : ViewWF view slots)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots), s ∈ slots.toList) :
    b.WF view := by
  unfold mkGBox? at h
  split at h
  · rename_i g0 g1 g2 h0 h1 h2
    injection h with hb
    subst hb
    have w0 : g0.WF view := by
      unfold mkGArg? at h0
      split at h0
      · cases h0
      · rename_i lo hi hb0
        injection h0 with hg0
        subst hg0
        cases a0 with
        | lit k => simp [GArg.WF]
        | slot s =>
            have hs : s ∈ slots.toList :=
              hslots s (by simp only [List.mem_append]; exact Or.inl (Or.inl (by simp [DomIntArg.slots])))
            simpa [GArg.WF] using hWF.dom_wf hs
    have w1 : g1.WF view := by
      unfold mkGArg? at h1
      split at h1
      · cases h1
      · rename_i lo hi hb1
        injection h1 with hg1
        subst hg1
        cases a1 with
        | lit k => simp [GArg.WF]
        | slot s =>
            have hs : s ∈ slots.toList :=
              hslots s (by simp only [List.mem_append]; exact Or.inl (Or.inr (by simp [DomIntArg.slots])))
            simpa [GArg.WF] using hWF.dom_wf hs
    have w2 : g2.WF view := by
      unfold mkGArg? at h2
      split at h2
      · cases h2
      · rename_i lo hi hb2
        injection h2 with hg2
        subst hg2
        cases a2 with
        | lit k => simp [GArg.WF]
        | slot s =>
            have hs : s ∈ slots.toList :=
              hslots s (by simp only [List.mem_append]; exact Or.inr (by simp [DomIntArg.slots]))
            simpa [GArg.WF] using hWF.dom_wf hs
    exact ⟨w0, w1, w2⟩
  · cases h

/-! ## Entailment kernels -/

theorem GArg.cur_of_lits_not_true {a : Assignment} {g : GArg} {x : Int}
    (hcs : g.CurSpec) (hread : DomIntArg.read a g.arg = .int x)
    (hnot : ∀ l ∈ g.lits, l.eval a ≠ some true) : g.Cur x := by
  cases harg : g.arg with
  | lit k =>
      have hx : x = k := by
        have h := hread
        rw [harg, DomIntArg.read_lit] at h
        injection h with h'
        omega
      subst hx
      have hk := hcs
      simp only [harg, GArg.CurSpec] at hk
      exact ⟨by omega, by omega⟩
  | slot s =>
      have hread' : a[s]! = .int x := by
        simpa [harg, DomIntArg.read_slot] using hread
      have hx : slotInt a s = some x := slotInt_eq_some_of_getElem!_int hread'
      have hloMem : loLit s g.lo ∈ g.lits := by simp [GArg.lits, harg]
      have hhiMem : hiLit s g.hi ∈ g.lits := by simp [GArg.lits, harg]
      exact ⟨le_of_loLit_not_true hx (hnot _ hloMem),
        le_of_hiLit_not_true hx (hnot _ hhiMem)⟩

theorem GArg.lits_eval_false {view : EngineView} {g : GArg}
    (hbound : g.BoundSpec view.doms) (hwf : g.WF view) :
    ∀ l ∈ g.lits, (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  intro l hl
  cases harg : g.arg with
  | lit k => simp [GArg.lits, harg] at hl
  | slot s =>
      have hs := hbound
      simp only [harg, GArg.BoundSpec] at hs
      have hw := hwf
      simp only [harg, GArg.WF] at hw
      simp only [GArg.lits, harg, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simpa [atomSlot] using loLit_eval_false hw hs.1 hs.2
      · simpa [atomSlot] using hiLit_eval_false hw hs.1 hs.2

theorem GBox.lits_eval_false {view : EngineView} {b : GBox}
    (hbound : b.BoundSpec view.doms) (hwf : b.WF view) :
    ∀ l ∈ b.lits, (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  intro l hl
  obtain ⟨hb0, hb1, hb2⟩ := hbound
  obtain ⟨hw0, hw1, hw2⟩ := hwf
  simp only [GBox.lits, List.mem_append] at hl
  rcases hl with (hl | hl) | hl
  · exact GArg.lits_eval_false hb0 hw0 l hl
  · exact GArg.lits_eval_false hb1 hw1 l hl
  · exact GArg.lits_eval_false hb2 hw2 l hl

theorem GBox.cur_of_lits_not_true {a : Assignment} {b : GBox}
    (hcs : b.CurSpec) {x y z : Int}
    (hx : DomIntArg.read a b.g0.arg = .int x)
    (hy : DomIntArg.read a b.g1.arg = .int y)
    (hz : DomIntArg.read a b.g2.arg = .int z)
    (hnot : ∀ l ∈ b.lits, l.eval a ≠ some true) :
    b.g0.Cur x ∧ b.g1.Cur y ∧ b.g2.Cur z := by
  obtain ⟨hc0, hc1, hc2⟩ := hcs
  have hn0 : ∀ l ∈ b.g0.lits, l.eval a ≠ some true := by
    intro l hl htrue
    exact hnot l (by simp only [GBox.lits, List.mem_append]; exact Or.inl (Or.inl hl)) htrue
  have hn1 : ∀ l ∈ b.g1.lits, l.eval a ≠ some true := by
    intro l hl htrue
    exact hnot l (by simp only [GBox.lits, List.mem_append]; exact Or.inl (Or.inr hl)) htrue
  have hn2 : ∀ l ∈ b.g2.lits, l.eval a ≠ some true := by
    intro l hl htrue
    exact hnot l (by simp only [GBox.lits, List.mem_append]; exact Or.inr hl) htrue
  exact ⟨GArg.cur_of_lits_not_true hc0 hx hn0,
    GArg.cur_of_lits_not_true hc1 hy hn1,
    GArg.cur_of_lits_not_true hc2 hz hn2⟩

/-- Every conflict literal evaluates to `false` on the view. -/
theorem GBox.conflict_lits_false {view : EngineView} {b : GBox}
    (hbound : b.BoundSpec view.doms) (hwf : b.WF view) :
    ∀ l ∈ b.lits, (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false :=
  GBox.lits_eval_false hbound hwf

theorem GBox.emptyNew_spec {b : GBox} (h : b.emptyNew = true) :
    b.g0.nlo > b.g0.nhi ∨ b.g1.nlo > b.g1.nhi ∨ b.g2.nlo > b.g2.nhi := by
  unfold GBox.emptyNew at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem GBox.emptyNew_false {b : GBox} (h : b.emptyNew = false) :
    b.g0.nlo ≤ b.g0.nhi ∧ b.g1.nlo ≤ b.g1.nhi ∧ b.g2.nlo ≤ b.g2.nhi := by
  unfold GBox.emptyNew at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  exact ⟨by omega, by omega, by omega⟩

theorem GBox.out_conflict {b : GBox} {ls : List Literal}
    (h : b.out = .conflict ls) : b.emptyNew = true ∧ ls = b.lits := by
  unfold GBox.out at h
  split at h
  · rename_i he
    injection h with hls
    exact ⟨by simpa using he, hls.symm⟩
  · rename_i he
    dsimp only at h
    split at h <;> cases h

theorem GBox.out_prune {b : GBox} {ps : List (Literal × List Literal)}
    (h : b.out = .prune ps) : b.emptyNew = false ∧ ps = b.prunes := by
  unfold GBox.out at h
  split at h
  · cases h
  · rename_i he
    dsimp only at h
    split at h
    · cases h
    · rename_i hne
      injection h with hps
      exact ⟨by simpa using he, hps.symm⟩

/-- Conflict entailment: the conjunction of current bound negations is a
valid conflict clause whenever an empty proposed interval meets the
semantic bridge and the propagation soundness proof. -/
theorem GBox.conflict_entailed (p : CompiledProblem DomConstraint)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b) {ls : List Literal}
    (hout : b.out = .conflict ls) : Entailed p ls := by
  intro a ha hacc
  have hsatB : dc.satisfiedB a = true := accepts_satisfiedB hacc hmem
  have hsat : dc.SatisfiedBy a := (DomConstraint.satisfiedB_iff dc a).mp hsatB
  obtain ⟨x, y, z, hx, hy, hz, hR⟩ := bridge a hsat
  by_cases hsome : ∃ l ∈ ls, l.eval a = some true
  · exact hsome
  · have hls := (GBox.out_conflict hout).2
    have hnone : ∀ l ∈ b.lits, l.eval a ≠ some true := by
      intro l hl hlt
      exact hsome ⟨l, by rw [hls]; exact hl, hlt⟩
    have hcur := GBox.cur_of_lits_not_true hcs hx hy hz hnone
    obtain ⟨hn0, hn1, hn2⟩ := hspec.sound x y z hcur.1 hcur.2.1 hcur.2.2 hR
    rcases GBox.emptyNew_spec (GBox.out_conflict hout).1 with he | he | he
    · obtain ⟨hlo, hhi⟩ := hn0
      omega
    · obtain ⟨hlo, hhi⟩ := hn1
      omega
    · obtain ⟨hlo, hhi⟩ := hn2
      omega

/-- The new literals of a prune are true on any assignment satisfying the
relation inside the current box. -/
theorem GArg.prune_lit_true {a : Assignment} {g : GArg} {s : Nat}
    {x : Int} (hread : DomIntArg.read a g.arg = .int x)
    (harg : g.arg = .slot s) (hnew : g.New x) :
    (geLit s g.nlo).eval a = some true ∧ (leLit s g.nhi).eval a = some true := by
  have hread' : a[s]! = .int x := by
    simpa [harg, DomIntArg.read_slot] using hread
  have hx : slotInt a s = some x := slotInt_eq_some_of_getElem!_int hread'
  obtain ⟨hlo, hhi⟩ := hnew
  constructor
  · rw [geLit, eval_negLe_iff]
    exact ⟨x, hx, by omega⟩
  · rw [leLit, eval_posLe_iff]
    exact ⟨x, hx, by omega⟩

/-- Membership in an operand's prune list exposes its exact shape. -/
theorem GArg.mem_prunes {g : GArg} {boxLits : List Literal}
    {l : Literal} {reason : List Literal}
    (h : (l, reason) ∈ g.prunes boxLits) :
    (∃ s, g.arg = .slot s ∧ l = geLit s g.nlo ∧ g.lo < g.nlo ∧
        reason = boxLits ++ [l]) ∨
      (∃ s, g.arg = .slot s ∧ l = leLit s g.nhi ∧ g.nhi < g.hi ∧
        reason = boxLits ++ [l]) := by
  unfold GArg.prunes at h
  cases harg : g.arg with
  | lit k => simp [harg] at h
  | slot s =>
      rw [harg] at h
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · split at h
        · rename_i hlt
          have heq : (l, reason) =
              (geLit s g.nlo, boxLits ++ [geLit s g.nlo]) := by
            simpa using h
          injection heq with hl hr
          exact Or.inl ⟨s, rfl, hl, hlt, by rw [hr, hl]⟩
        · cases h
      · split at h
        · rename_i hlt
          have heq : (l, reason) =
              (leLit s g.nhi, boxLits ++ [leLit s g.nhi]) := by
            simpa using h
          injection heq with hl hr
          exact Or.inr ⟨s, rfl, hl, hlt, by rw [hr, hl]⟩
        · cases h

/-- A prune reason is satisfied by any assignment whose operand value is
inside the proposed interval (the current bound literals are handled by
the caller). -/
theorem GArg.prune_reason_satisfied {a : Assignment} {g : GArg}
    {boxLits : List Literal} {x : Int} {q : Literal × List Literal}
    (hq : q ∈ g.prunes boxLits)
    (hread : DomIntArg.read a g.arg = .int x) (hnew : g.New x) :
    Clause.SatisfiedBy q.2 a := by
  rcases GArg.mem_prunes hq with ⟨s, harg, hl, hlt, hreason⟩ |
    ⟨s, harg, hl, hlt, hreason⟩
  · refine ⟨q.1, ?_, ?_⟩
    · change q.1 ∈ q.2
      rw [hreason]
      exact List.mem_append_right _ (by simp [hl])
    · rw [hl]
      exact (GArg.prune_lit_true hread harg hnew).1
  · refine ⟨q.1, ?_, ?_⟩
    · change q.1 ∈ q.2
      rw [hreason]
      exact List.mem_append_right _ (by simp [hl])
    · rw [hl]
      exact (GArg.prune_lit_true hread harg hnew).2

/-- Prune-reason entailment: the reason of every emitted prune is
entailed by the constraint. -/
theorem GBox.prune_reason_entailed (p : CompiledProblem DomConstraint)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b)
    {ps : List (Literal × List Literal)} (hout : b.out = .prune ps)
    {q : Literal × List Literal} (hq : q ∈ ps) : Entailed p q.2 := by
  have hps := (GBox.out_prune hout).2
  subst hps
  intro a ha hacc
  have hsatB : dc.satisfiedB a = true := accepts_satisfiedB hacc hmem
  have hsat : dc.SatisfiedBy a := (DomConstraint.satisfiedB_iff dc a).mp hsatB
  obtain ⟨x, y, z, hx, hy, hz, hR⟩ := bridge a hsat
  unfold GBox.prunes at hq
  simp only [List.mem_append] at hq
  by_cases hsome : ∃ l ∈ b.lits, l.eval a = some true
  · obtain ⟨l, hl, hlt⟩ := hsome
    have hq0 : q ∈ b.g0.prunes b.lits ∨ q ∈ b.g1.prunes b.lits ∨
        q ∈ b.g2.prunes b.lits := by
      rcases hq with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases hq0 with hq0 | hq0 | hq0
    · rcases GArg.mem_prunes hq0 with ⟨s, harg, hl', hlt', hreason⟩ |
        ⟨s, harg, hl', hlt', hreason⟩
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
    · rcases GArg.mem_prunes hq0 with ⟨s, harg, hl', hlt', hreason⟩ |
        ⟨s, harg, hl', hlt', hreason⟩
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
    · rcases GArg.mem_prunes hq0 with ⟨s, harg, hl', hlt', hreason⟩ |
        ⟨s, harg, hl', hlt', hreason⟩
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
      · refine ⟨l, ?_, hlt⟩
        rw [hreason]; exact List.mem_append_left _ hl
  · have hnone : ∀ l ∈ b.lits, l.eval a ≠ some true := by
      intro l hl hlt
      exact hsome ⟨l, hl, hlt⟩
    have hcur := GBox.cur_of_lits_not_true hcs hx hy hz hnone
    obtain ⟨hn0, hn1, hn2⟩ := hspec.sound x y z hcur.1 hcur.2.1 hcur.2.2 hR
    rcases hq with (h | h) | h
    · exact GArg.prune_reason_satisfied h hx hn0
    · exact GArg.prune_reason_satisfied h hy hn1
    · exact GArg.prune_reason_satisfied h hz hn2

/-- The pruned literal is unassigned and every other literal of its
reason is false on the current view. -/
theorem GBox.prune_lit_none {view : EngineView} {b : GBox}
    (hbound : b.BoundSpec view.doms) (hwf : b.WF view)
    (hsub : b.g0.Sub ∧ b.g1.Sub ∧ b.g2.Sub)
    {ps : List (Literal × List Literal)} (hout : b.out = .prune ps)
    {q : Literal × List Literal} (hq : q ∈ ps) :
    (view.doms.getD (atomSlot q.1.atom) DomC.empty).evalLit q.1 = none ∧
      (∀ l ∈ q.2, l ≠ q.1 →
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  have hps := (GBox.out_prune hout).2
  subst hps
  obtain ⟨hb0, hb1, hb2⟩ := hbound
  obtain ⟨hw0, hw1, hw2⟩ := hwf
  obtain ⟨hs0, hs1, hs2⟩ := hsub
  obtain ⟨hn0, hn1, hn2⟩ := GBox.emptyNew_false (GBox.out_prune hout).1
  unfold GBox.prunes at hq
  simp only [List.mem_append] at hq
  have harglem : ∀ (g : GArg) (hb : g.BoundSpec view.doms) (hw : g.WF view)
      (hn : g.nlo ≤ g.nhi) (hs : g.Sub), ∀ q,
      q ∈ g.prunes b.lits →
      (view.doms.getD (atomSlot q.1.atom) DomC.empty).evalLit q.1 = none ∧
        (∀ l ∈ q.2, l ≠ q.1 →
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
    intro g hb hw hn hs q hq
    cases harg : g.arg with
    | lit k => simp [GArg.prunes, harg] at hq
    | slot s =>
        have hbs := hb
        simp only [harg, GArg.BoundSpec] at hbs
        obtain ⟨hslo, hshi⟩ := hs
        constructor
        · rcases GArg.mem_prunes hq with ⟨s', harg', hl, hlt, hreason⟩ |
            ⟨s', harg', hl, hlt, hreason⟩
          · have hs' : s' = s := by
              rw [harg'] at harg
              injection harg
            subst s'
            rw [hl]
            have hslot : atomSlot (geLit s g.nlo).atom = s := rfl
            rw [hslot]
            exact evalLit_negLe_none (d := view.doms.getD s DomC.empty)
              (s := s) (k := g.nlo - 1) hbs.1 hbs.2 (by omega) (by omega)
          · have hs' : s' = s := by
              rw [harg'] at harg
              injection harg
            subst s'
            rw [hl]
            have hslot : atomSlot (leLit s g.nhi).atom = s := rfl
            rw [hslot]
            exact evalLit_posLe_none (d := view.doms.getD s DomC.empty)
              (s := s) (k := g.nhi) hbs.1 hbs.2 (by omega) (by omega)
        · intro l hl hne
          rcases GArg.mem_prunes hq with ⟨s', harg', hl', hlt, hreason⟩ |
            ⟨s', harg', hl', hlt, hreason⟩
          · rw [hreason] at hl
            rcases List.mem_append.mp hl with hbl | hnew
            · exact GBox.lits_eval_false ⟨hb0, hb1, hb2⟩ ⟨hw0, hw1, hw2⟩ l hbl
            · have : l = q.1 := by simpa using hnew
              exact absurd this hne
          · rw [hreason] at hl
            rcases List.mem_append.mp hl with hbl | hnew
            · exact GBox.lits_eval_false ⟨hb0, hb1, hb2⟩ ⟨hw0, hw1, hw2⟩ l hbl
            · have : l = q.1 := by simpa using hnew
              exact absurd this hne
  rcases hq with (hq | hq) | hq
  · exact harglem b.g0 hb0 hw0 hn0 hs0 q hq
  · exact harglem b.g1 hb1 hw1 hn1 hs1 q hq
  · exact harglem b.g2 hb2 hw2 hn2 hs2 q hq

/-! ## Turning a box into a `PropOut` -/

/-- A propagation step is a function of the whole box that proposes new
lower and upper bounds for the three operands; `apply` intersects each
proposal with the current interval, so every step is a genuine
narrowing. -/
structure GStep where
  nlo0 : GBox → Int
  nhi0 : GBox → Int
  nlo1 : GBox → Int
  nhi1 : GBox → Int
  nlo2 : GBox → Int
  nhi2 : GBox → Int

theorem GArg.intersect_sub (g : GArg) (lo hi : Int) :
    (g.intersect lo hi).Sub := by
  unfold GArg.Sub GArg.intersect
  exact ⟨Int.le_max_left _ _, Int.min_le_left _ _⟩

theorem GArg.curSpec_intersect {g : GArg} (h : g.CurSpec) (lo hi : Int) :
    (g.intersect lo hi).CurSpec := by
  cases harg : g.arg with
  | lit k =>
      have hk : g.lo = k ∧ g.hi = k := by
        simpa [GArg.CurSpec, harg] using h
      simp [GArg.CurSpec, GArg.intersect, harg, hk.1, hk.2]
  | slot s => simp [GArg.CurSpec, GArg.intersect, harg]

theorem GArg.boundSpec_intersect {doms : Array DomC} {g : GArg}
    (h : g.BoundSpec doms) (lo hi : Int) :
    (g.intersect lo hi).BoundSpec doms := by
  cases harg : g.arg with
  | lit k =>
      have hk : g.lo = k ∧ g.hi = k := by
        simpa [GArg.BoundSpec, harg] using h
      simp [GArg.BoundSpec, GArg.intersect, harg, hk.1, hk.2]
  | slot s =>
      have hs : (doms.getD s DomC.empty).lo? = some g.lo ∧
          (doms.getD s DomC.empty).hi? = some g.hi := by
        simpa [GArg.BoundSpec, harg] using h
      simpa [GArg.BoundSpec, GArg.intersect, harg] using hs

theorem GArg.wf_intersect {view : EngineView} {g : GArg}
    (h : g.WF view) (lo hi : Int) : (g.intersect lo hi).WF view := by
  cases harg : g.arg with
  | lit k => simp [GArg.WF, GArg.intersect, harg]
  | slot s =>
      have hs : (view.doms.getD s DomC.empty).WF := by
        simpa [GArg.WF, harg] using h
      simpa [GArg.WF, GArg.intersect, harg] using hs

namespace GStep

/-- Apply the proposal, intersecting with the current intervals. -/
def apply (st : GStep) (b : GBox) : GBox :=
  { g0 := b.g0.intersect (st.nlo0 b) (st.nhi0 b)
    g1 := b.g1.intersect (st.nlo1 b) (st.nhi1 b)
    g2 := b.g2.intersect (st.nlo2 b) (st.nhi2 b) }

@[simp] theorem apply_g0_arg (st : GStep) (b : GBox) :
    (st.apply b).g0.arg = b.g0.arg := rfl

@[simp] theorem apply_g1_arg (st : GStep) (b : GBox) :
    (st.apply b).g1.arg = b.g1.arg := rfl

@[simp] theorem apply_g2_arg (st : GStep) (b : GBox) :
    (st.apply b).g2.arg = b.g2.arg := rfl

theorem apply_curSpec (st : GStep) (b : GBox) (h : b.CurSpec) :
    (st.apply b).CurSpec := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨GArg.curSpec_intersect h0 _ _,
    GArg.curSpec_intersect h1 _ _,
    GArg.curSpec_intersect h2 _ _⟩

theorem apply_boundSpec (st : GStep) {doms : Array DomC} {b : GBox}
    (h : b.BoundSpec doms) : (st.apply b).BoundSpec doms := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨GArg.boundSpec_intersect h0 _ _,
    GArg.boundSpec_intersect h1 _ _,
    GArg.boundSpec_intersect h2 _ _⟩

theorem apply_wf (st : GStep) {view : EngineView} {b : GBox}
    (h : b.WF view) : (st.apply b).WF view := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨GArg.wf_intersect h0 _ _,
    GArg.wf_intersect h1 _ _,
    GArg.wf_intersect h2 _ _⟩

theorem apply_sub (st : GStep) (b : GBox) :
    (st.apply b).g0.Sub ∧ (st.apply b).g1.Sub ∧ (st.apply b).g2.Sub := by
  exact ⟨GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _⟩

end GStep

/-- The prune array produced from a list of source prunes, attaching the
entailment proof of each reason. -/
def mkPruneArray (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b)
    {ps : List (Literal × List Literal)} (hout : b.out = .prune ps) :
    Array (PLit × EClause p T) :=
  (ps.attach.map fun q =>
    (pLit q.1.1, EClause.ofLiterals p T q.1.2
      (GBox.prune_reason_entailed p dc hmem R b bridge hcs hspec hout q.2))).toArray

theorem mkPruneArray_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b)
    {ps : List (Literal × List Literal)} (hout : b.out = .prune ps)
    {q : PLit × EClause p T}
    (hq : q ∈ (mkPruneArray p T dc hmem R b bridge hcs hspec hout).toList) :
    ∃ l reason, (l, reason) ∈ ps ∧ q.1.lit = l ∧
      T.decodeClause q.2.lits = reason ∧ Entailed p reason := by
  unfold mkPruneArray at hq
  rw [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  refine ⟨x.1.1, x.1.2, x.2, rfl, ?_, ?_⟩
  · change T.decodeClause (x.1.2.toArray.map pLit) = x.1.2
    exact LitTable.decodeClause_map_pLit T x.1.2
  · change Entailed p x.1.2
    rw [← LitTable.decodeClause_map_pLit T x.1.2]
    exact (EClause.ofLiterals p T x.1.2
      (GBox.prune_reason_entailed p dc hmem R b bridge hcs hspec hout x.2)).ent

/-- Convert the computed output of a box into an engine output. -/
def GBox.toPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b) : PropOut p T :=
  match hout : b.out with
  | .fix => .fix
  | .conflict ls =>
      .conflict (EClause.ofLiterals p T ls
        (GBox.conflict_entailed p dc hmem R b bridge hcs hspec hout))
  | .prune ps =>
      .prune (mkPruneArray p T dc hmem R b bridge hcs hspec hout)

theorem GBox.toPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b)
    {ec : EClause p T}
    (h : b.toPropWith p T dc hmem R bridge hcs hspec = .conflict ec) :
    ∃ ls, b.out = .conflict ls ∧ ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  unfold GBox.toPropWith at h
  split at h
  · cases h
  · rename_i ls hout
    injection h with hec
    subst hec
    exact ⟨ls, hout, rfl, LitTable.decodeClause_map_pLit T ls,
      GBox.conflict_entailed p dc hmem R b bridge hcs hspec hout⟩
  · cases h

theorem GBox.toPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (R : Int → Int → Int → Prop) (b : GBox)
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a b.g0.arg = .int x ∧
        DomIntArg.read a b.g1.arg = .int y ∧
        DomIntArg.read a b.g2.arg = .int z ∧ R x y z)
    (hcs : b.CurSpec) (hspec : GSpec R b)
    {psArr : Array (PLit × EClause p T)}
    (h : b.toPropWith p T dc hmem R bridge hcs hspec = .prune psArr) :
    ∃ ps, b.out = .prune ps ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason) := by
  unfold GBox.toPropWith at h
  split at h
  · cases h
  · cases h
  · rename_i ps hout
    injection h with harr
    refine ⟨ps, hout, ?_⟩
    intro q hq
    rw [← harr] at hq
    exact mkPruneArray_mem p T dc hmem R b bridge hcs hspec hout hq

/-- A uniform three-operand builder.  The relation-specific step is
parameterised by its soundness proof; the bridge converts the source
constraint semantics into one tuple of the three operands. -/
def rel3PropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z) : PropV2 p T :=
  { vars := (dcSlotsFull dc).toArray
    events := (dcSlotsFull dc).toArray.map fun s => (s, .bounds)
    run := fun view =>
      match hb : mkGBox? view.doms a0 a1 a2 with
      | none => .fix
      | some b =>
          (step.apply b).toPropWith p T dc hmem R
            (fun a ha => by
              obtain ⟨x, y, z, hx, hy, hz, hR⟩ := bridge a ha
              refine ⟨x, y, z, ?_, ?_, ?_, hR⟩
              · rw [GStep.apply_g0_arg, mkGBox?_arg0 hb]
                exact hx
              · rw [GStep.apply_g1_arg, mkGBox?_arg1 hb]
                exact hy
              · rw [GStep.apply_g2_arg, mkGBox?_arg2 hb]
                exact hz)
            (GStep.apply_curSpec step b (mkGBox?_curSpec hb))
            (hstep b (mkGBox?_curSpec hb)) }

theorem rel3PropWith_run_fix_of_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView)
    (hmk : mkGBox? view.doms a0 a1 a2 = none) :
    (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view = .fix := by
  unfold rel3PropWith
  dsimp only
  split
  · rfl
  · rename_i b hb
    rw [hmk] at hb
    cases hb

theorem rel3PropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .conflict ec) :
    ∃ b ls, mkGBox? view.doms a0 a1 a2 = some b ∧
      (step.apply b).out = .conflict ls ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold rel3PropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i b hb
    obtain ⟨ls, hout, hlit, hdec, hent⟩ :=
      GBox.toPropWith_run_conflict p T dc hmem R (step.apply b)
        _ (GStep.apply_curSpec step b (mkGBox?_curSpec hb))
        (hstep b (mkGBox?_curSpec hb)) h
    have hbound : (step.apply b).BoundSpec view.doms :=
      GStep.apply_boundSpec step (mkGBox?_bounds hb)
    have hwf : (step.apply b).WF view :=
      GStep.apply_wf step (mkGBox?_wf hb hWF hslots)
    have hls : ls = (step.apply b).lits := (GBox.out_conflict hout).2
    have hfalse : ∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
      intro l hl
      exact GBox.conflict_lits_false hbound hwf l (by rwa [hls] at hl)
    exact ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩

theorem rel3PropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .prune psArr) :
    ∃ b ps, mkGBox? view.doms a0 a1 a2 = some b ∧
      (step.apply b).out = .prune ps ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      (step.apply b).g0.Sub ∧ (step.apply b).g1.Sub ∧ (step.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold rel3PropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i b hb
    obtain ⟨ps, hout, hmemfacts⟩ :=
      GBox.toPropWith_run_prune p T dc hmem R (step.apply b)
        _ (GStep.apply_curSpec step b (mkGBox?_curSpec hb))
        (hstep b (mkGBox?_curSpec hb)) h
    have hbound : (step.apply b).BoundSpec view.doms :=
      GStep.apply_boundSpec step (mkGBox?_bounds hb)
    have hwf : (step.apply b).WF view :=
      GStep.apply_wf step (mkGBox?_wf hb hWF hslots)
    have hsub := GStep.apply_sub step b
    refine ⟨b, ps, hb, hout, hbound, hwf, hsub.1, hsub.2.1, hsub.2.2, ?_⟩
    intro q hq
    obtain ⟨l, reason, hprune, hlit, hdec, hent⟩ := hmemfacts q hq
    obtain ⟨hnone, hother⟩ :=
      GBox.prune_lit_none (view := view) (b := step.apply b)
        hbound hwf hsub hout hprune
    exact ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩

/-! ## Generic public contracts for `rel3PropWith` -/

theorem rel3PropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
    rel3PropWith_run_conflict p T dc hmem a0 a1 a2 R step hstep bridge
      view hWF hslots h
  rw [hdec]
  exact hent

theorem rel3PropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
    rel3PropWith_run_conflict p T dc hmem a0 a1 a2 R step hstep bridge
      view hWF hslots h
  intro l hl
  rw [hdec] at hl
  exact hfalse l hl

theorem rel3PropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
    rel3PropWith_run_prune p T dc hmem a0 a1 a2 R step hstep bridge
      view hWF hslots h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hfacts q hq
  rwa [hdec]

theorem rel3PropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (a0 a1 a2 : DomIntArg) (R : Int → Int → Int → Prop)
    (step : GStep)
    (hstep : ∀ b, b.CurSpec → GSpec R (step.apply b))
    (bridge : ∀ a, dc.SatisfiedBy a →
      ∃ x y z, DomIntArg.read a a0 = .int x ∧
        DomIntArg.read a a1 = .int y ∧
        DomIntArg.read a a2 = .int z ∧ R x y z)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ (a0.slots ++ a1.slots ++ a2.slots),
      s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (rel3PropWith p T dc hmem a0 a1 a2 R step hstep bridge).run view
      = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
    rel3PropWith_run_prune p T dc hmem a0 a1 a2 R step hstep bridge
      view hWF hslots h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

/-! ## Stage 1: plus, min, max, abs -/

def plusRel (x y z : Int) : Prop := x + y = z

def plusStep : GStep where
  nlo0 b := b.g2.lo - b.g1.hi
  nhi0 b := b.g2.hi - b.g1.lo
  nlo1 b := b.g2.lo - b.g0.hi
  nhi1 b := b.g2.hi - b.g0.lo
  nlo2 b := b.g0.lo + b.g1.lo
  nhi2 b := b.g0.hi + b.g1.hi

theorem plusStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec plusRel (plusStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  simp only [plusRel] at hR
  unfold GStep.apply
  simp only [plusStep, GArg.intersect, GArg.New]
  omega

def minRel (x y z : Int) : Prop := min x y = z

def minStep : GStep where
  nlo0 b := b.g2.lo
  -- If the other operand is already above `z`, `z` can only come from
  -- this operand, so this operand shares `z`'s upper bound.
  nhi0 b := if b.g1.lo > b.g2.hi then b.g2.hi else b.g0.hi
  nlo1 b := b.g2.lo
  nhi1 b := if b.g0.lo > b.g2.hi then b.g2.hi else b.g1.hi
  nlo2 b := min b.g0.lo b.g1.lo
  nhi2 b := min b.g0.hi b.g1.hi

theorem minStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec minRel (minStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  simp only [minRel] at hR
  unfold GStep.apply
  simp only [minStep, GArg.intersect, GArg.New]
  by_cases h1 : b.g1.lo > b.g2.hi <;>
    by_cases h2 : b.g0.lo > b.g2.hi <;>
    simp [h1, h2] <;> omega

def maxRel (x y z : Int) : Prop := max x y = z

def maxStep3 : GStep where
  -- If the other operand is already below `z`, `z` can only come from
  -- this operand, so this operand shares `z`'s lower bound.
  nlo0 b := if b.g1.hi < b.g2.lo then b.g2.lo else b.g0.lo
  nhi0 b := b.g2.hi
  nlo1 b := if b.g0.hi < b.g2.lo then b.g2.lo else b.g1.lo
  nhi1 b := b.g2.hi
  nlo2 b := max b.g0.lo b.g1.lo
  nhi2 b := max b.g0.hi b.g1.hi

theorem maxStep3_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec maxRel (maxStep3.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  simp only [maxRel] at hR
  unfold GStep.apply
  simp only [maxStep3, GArg.intersect, GArg.New]
  by_cases h1 : b.g1.hi < b.g2.lo <;>
    by_cases h2 : b.g0.hi < b.g2.lo <;>
    simp [h1, h2] <;> omega

def absRel (x _y z : Int) : Prop := absValue x = z

def absStep : GStep where
  nlo0 b := -b.g2.hi
  nhi0 b := b.g2.hi
  nlo1 b := b.g1.lo
  nhi1 b := b.g1.hi
  nlo2 b := absCornerMin b.g0.lo b.g0.hi
  nhi2 b := max (absValue b.g0.lo) (absValue b.g0.hi)

theorem absStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec absRel (absStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  simp only [absRel] at hR
  have hneg := arith_neg_absValue_le x
  have hle := arith_le_absValue x
  have hcorner := arith_absCornerMin_le hxlo hxhi
  have hupper := arith_absValue_le_range hxlo hxhi
  unfold GStep.apply
  simp only [absStep, GArg.intersect, GArg.New]
  omega

/-! ## Semantic bridges -/

theorem read_slot_int_of_getElem? {a : Assignment} {i : Nat} {x : Int}
    (h : a[i]? = some (.int x)) :
    DomIntArg.read a (.slot i) = .int x := by
  rw [DomIntArg.read_slot, List.getElem!_eq_getElem?_getD, h]
  rfl

theorem plus_bridge {a : Assignment} {i j k : Nat}
    (ha : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a (.slot i) = .int x ∧
      DomIntArg.read a (.slot j) = .int y ∧
      DomIntArg.read a (.slot k) = .int z ∧ plusRel x y z := by
  obtain ⟨x, y, z, hx, hy, hz, hsum⟩ := ha
  exact ⟨x, y, z, read_slot_int_of_getElem? hx,
    read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hsum⟩

theorem min_bridge {a : Assignment} {i j k : Nat}
    (ha : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a (.slot i) = .int x ∧
      DomIntArg.read a (.slot j) = .int y ∧
      DomIntArg.read a (.slot k) = .int z ∧ minRel x y z := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := ha
  exact ⟨x, y, z, read_slot_int_of_getElem? hx,
    read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmin⟩

theorem max_bridge {a : Assignment} {i j k : Nat}
    (ha : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a (.slot i) = .int x ∧
      DomIntArg.read a (.slot j) = .int y ∧
      DomIntArg.read a (.slot k) = .int z ∧ maxRel x y z := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := ha
  exact ⟨x, y, z, read_slot_int_of_getElem? hx,
    read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmax⟩

theorem abs_bridge {a : Assignment} {i k : Nat}
    (ha : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a (.slot i) = .int x ∧
      DomIntArg.read a (.lit 0) = .int y ∧
      DomIntArg.read a (.slot k) = .int z ∧ absRel x y z := by
  obtain ⟨x, z, hx, hz, habs⟩ := ha
  exact ⟨x, 0, z, read_slot_int_of_getElem? hx, rfl,
    read_slot_int_of_getElem? hz, habs⟩

theorem minPair_bridge {a : Assignment} {o0 o1 r : DomIntArg}
    (ha : (DomConstraint.minPair o0 o1 r).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a o0 = .int x ∧
      DomIntArg.read a o1 = .int y ∧
      DomIntArg.read a r = .int z ∧ minRel x y z := by
  obtain ⟨x, y, hx, hy, hz⟩ := ha
  exact ⟨x, y, min x y, hx, hy, hz, rfl⟩

theorem maxPair_bridge {a : Assignment} {o0 o1 r : DomIntArg}
    (ha : (DomConstraint.maxPair o0 o1 r).SatisfiedBy a) :
    ∃ x y z, DomIntArg.read a o0 = .int x ∧
      DomIntArg.read a o1 = .int y ∧
      DomIntArg.read a r = .int z ∧ maxRel x y z := by
  obtain ⟨x, y, hx, hy, hz⟩ := ha
  exact ⟨x, y, max x y, hx, hy, hz, rfl⟩

/-! ## Stage-1 builders -/

def plusPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h)
    (fun a ha => plus_bridge ha)

def minPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h)
    (fun a ha => min_bridge ha)

def maxPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h)
    (fun a ha => max_bridge ha)

def absPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h)
    (fun a ha => abs_bridge ha)

def minPairPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h)
    (fun a ha => minPair_bridge ha)

def maxPairPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h)
    (fun a ha => maxPair_bridge ha)


theorem plusPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (plusPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (plusStep.apply b).out = .conflict ls ∧
      (plusStep.apply b).BoundSpec view.doms ∧ (plusStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold plusPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem plusPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (plusPropWith p T i j k hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (plusStep.apply b).out = .prune ps ∧
      (plusStep.apply b).BoundSpec view.doms ∧ (plusStep.apply b).WF view ∧
      (plusStep.apply b).g0.Sub ∧ (plusStep.apply b).g1.Sub ∧
      (plusStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold plusPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem plusPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (plusPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold plusPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem plusPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (plusPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold plusPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem plusPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (plusPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold plusPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem plusPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.plusSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (plusPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold plusPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem plusPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.plusSlot i j k ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms (.slot i) (.slot j) (.slot k) = none) :
    (plusPropWith p T i j k hmem).run view = .fix := by
  unfold plusPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.plusSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    plusRel plusStep (fun b h => plusStep_spec (b := b) h) (fun a ha => plus_bridge ha) view hmk

theorem minPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (minPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (minStep.apply b).out = .conflict ls ∧
      (minStep.apply b).BoundSpec view.doms ∧ (minStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold minPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem minPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPropWith p T i j k hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (minStep.apply b).out = .prune ps ∧
      (minStep.apply b).BoundSpec view.doms ∧ (minStep.apply b).WF view ∧
      (minStep.apply b).g0.Sub ∧ (minStep.apply b).g1.Sub ∧
      (minStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold minPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem minPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (minPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold minPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem minPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (minPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold minPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem minPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold minPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem minPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold minPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem minPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.minSlot i j k ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms (.slot i) (.slot j) (.slot k) = none) :
    (minPropWith p T i j k hmem).run view = .fix := by
  unfold minPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.minSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => min_bridge ha) view hmk

theorem maxPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (maxPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (maxStep3.apply b).out = .conflict ls ∧
      (maxStep3.apply b).BoundSpec view.doms ∧ (maxStep3.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold maxPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem maxPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPropWith p T i j k hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (maxStep3.apply b).out = .prune ps ∧
      (maxStep3.apply b).BoundSpec view.doms ∧ (maxStep3.apply b).WF view ∧
      (maxStep3.apply b).g0.Sub ∧ (maxStep3.apply b).g1.Sub ∧
      (maxStep3.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold maxPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem maxPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (maxPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold maxPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem maxPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (maxPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold maxPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem maxPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold maxPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem maxPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold maxPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem maxPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.maxSlot i j k ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms (.slot i) (.slot j) (.slot k) = none) :
    (maxPropWith p T i j k hmem).run view = .fix := by
  unfold maxPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.maxSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => max_bridge ha) view hmk

theorem absPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {ec : EClause p T}
    (h : (absPropWith p T i k hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms (.slot i) (.lit 0) (.slot k) = some b ∧
      (absStep.apply b).out = .conflict ls ∧
      (absStep.apply b).BoundSpec view.doms ∧ (absStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold absPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem absPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (absPropWith p T i k hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms (.slot i) (.lit 0) (.slot k) = some b ∧
      (absStep.apply b).out = .prune ps ∧
      (absStep.apply b).BoundSpec view.doms ∧ (absStep.apply b).WF view ∧
      (absStep.apply b).g0.Sub ∧ (absStep.apply b).g1.Sub ∧
      (absStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold absPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem absPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {ec : EClause p T}
    (h : (absPropWith p T i k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold absPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem absPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {ec : EClause p T}
    (h : (absPropWith p T i k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold absPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem absPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (absPropWith p T i k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold absPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem absPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.absSlot i k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (absPropWith p T i k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold absPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem absPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.absSlot i k ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms (.slot i) (.lit 0) (.slot k) = none) :
    (absPropWith p T i k hmem).run view = .fix := by
  unfold absPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.absSlot i k) hmem (.slot i) (.lit 0) (.slot k)
    absRel absStep (fun b h => absStep_spec (b := b) h) (fun a ha => abs_bridge ha) view hmk

theorem minPairPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms o0 o1 r = some b ∧
      (minStep.apply b).out = .conflict ls ∧
      (minStep.apply b).BoundSpec view.doms ∧ (minStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold minPairPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem minPairPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms o0 o1 r = some b ∧
      (minStep.apply b).out = .prune ps ∧
      (minStep.apply b).BoundSpec view.doms ∧ (minStep.apply b).WF view ∧
      (minStep.apply b).g0.Sub ∧ (minStep.apply b).g1.Sub ∧
      (minStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold minPairPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem minPairPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold minPairPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem minPairPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold minPairPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem minPairPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold minPairPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h hq

theorem minPairPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.minPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minPairPropWith p T o0 o1 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold minPairPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h hq

theorem minPairPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.minPair o0 o1 r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms o0 o1 r = none) :
    (minPairPropWith p T o0 o1 r hmem).run view = .fix := by
  unfold minPairPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.minPair o0 o1 r) hmem o0 o1 r
    minRel minStep (fun b h => minStep_spec (b := b) h) (fun a ha => minPair_bridge ha) view hmk

theorem maxPairPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms o0 o1 r = some b ∧
      (maxStep3.apply b).out = .conflict ls ∧
      (maxStep3.apply b).BoundSpec view.doms ∧ (maxStep3.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold maxPairPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem maxPairPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms o0 o1 r = some b ∧
      (maxStep3.apply b).out = .prune ps ∧
      (maxStep3.apply b).BoundSpec view.doms ∧ (maxStep3.apply b).WF view ∧
      (maxStep3.apply b).g0.Sub ∧ (maxStep3.apply b).g1.Sub ∧
      (maxStep3.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold maxPairPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem maxPairPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold maxPairPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem maxPairPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {ec : EClause p T}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold maxPairPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h

theorem maxPairPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold maxPairPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h hq

theorem maxPairPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxPair o0 o1 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxPairPropWith p T o0 o1 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold maxPairPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hWF (by intro s hs; simpa [dcSlotsFull] using hs) h hq

theorem maxPairPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (o0 o1 r : DomIntArg) (hmem : DomConstraint.maxPair o0 o1 r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms o0 o1 r = none) :
    (maxPairPropWith p T o0 o1 r hmem).run view = .fix := by
  unfold maxPairPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.maxPair o0 o1 r) hmem o0 o1 r
    maxRel maxStep3 (fun b h => maxStep3_spec (b := b) h) (fun a ha => maxPair_bridge ha) view hmk

/-! ## Stage 3: multiplication -/

def timesRel (x y z : Int) : Prop := x * y = z

/-- Four-corner interval multiplication, with reverse division when one
factor is fixed and nonzero. -/
def timesStep : GStep where
  nlo0 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      divResLo b.g1.lo b.g2.lo b.g2.hi
    else b.g0.lo
  nhi0 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      divResHi b.g1.lo b.g2.lo b.g2.hi
    else b.g0.hi
  nlo1 b :=
    if b.g0.lo = b.g0.hi ∧ b.g0.lo ≠ 0 then
      divResLo b.g0.lo b.g2.lo b.g2.hi
    else b.g1.lo
  nhi1 b :=
    if b.g0.lo = b.g0.hi ∧ b.g0.lo ≠ 0 then
      divResHi b.g0.lo b.g2.lo b.g2.hi
    else b.g1.hi
  nlo2 b := cornerMin b.g0.lo b.g0.hi b.g1.lo b.g1.hi
  nhi2 b := cornerMax b.g0.lo b.g0.hi b.g1.lo b.g1.hi

theorem timesStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec timesRel (timesStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  unfold timesRel at hR
  have hprod : z = x * y := hR.symm
  constructor
  · unfold GStep.apply
    simp only [timesStep, GArg.intersect, GArg.New]
    by_cases hfix : b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0
    · simp only [if_pos hfix]
      obtain ⟨hyfix, hyne⟩ := hfix
      have hy_eq : y = b.g1.lo := by omega
      have hyne' : y ≠ 0 := by omega
      have hdiv : Int.tdiv z y = x := by
        rw [hprod]
        exact Int.mul_tdiv_cancel x hyne'
      have hhull := tdiv_mem_hull (p := z) (d := y)
        (pl := b.g2.lo) (ph := b.g2.hi) hyne' hzlo hzhi
      rw [hdiv] at hhull
      rw [← hy_eq]
      omega
    · simp only [if_neg hfix]
      omega
  · constructor
    · unfold GStep.apply
      simp only [timesStep, GArg.intersect, GArg.New]
      by_cases hfix : b.g0.lo = b.g0.hi ∧ b.g0.lo ≠ 0
      · simp only [if_pos hfix]
        obtain ⟨hxfix, hxne⟩ := hfix
        have hx_eq : x = b.g0.lo := by omega
        have hxne' : x ≠ 0 := by omega
        have hdiv : Int.tdiv z x = y := by
          rw [hprod]
          rw [Int.mul_comm]
          exact Int.mul_tdiv_cancel y hxne'
        have hhull := tdiv_mem_hull (p := z) (d := x)
          (pl := b.g2.lo) (ph := b.g2.hi) hxne' hzlo hzhi
        rw [hdiv] at hhull
        rw [← hx_eq]
        omega
      · simp only [if_neg hfix]
        omega
    · unfold GStep.apply
      simp only [timesStep, GArg.intersect, GArg.New]
      have h1 := times_cornerMin_le hxlo hxhi hylo hyhi
      have h2 := times_le_cornerMax hxlo hxhi hylo hyhi
      omega

def timesPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.timesSlot i j k) hmem (.slot i) (.slot j) (.slot k)
    timesRel timesStep (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)

theorem timesPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (timesPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (timesStep.apply b).out = .conflict ls ∧
      (timesStep.apply b).BoundSpec view.doms ∧ (timesStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold timesPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem timesPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (timesPropWith p T i j k hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms (.slot i) (.slot j) (.slot k) = some b ∧
      (timesStep.apply b).out = .prune ps ∧
      (timesStep.apply b).BoundSpec view.doms ∧ (timesStep.apply b).WF view ∧
      (timesStep.apply b).g0.Sub ∧ (timesStep.apply b).g1.Sub ∧
      (timesStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold timesPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem timesPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (timesPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold timesPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem timesPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {ec : EClause p T}
    (h : (timesPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold timesPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem timesPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (timesPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold timesPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem timesPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.timesSlot i j k)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (timesPropWith p T i j k hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold timesPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem timesPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.timesSlot i j k ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms (.slot i) (.slot j) (.slot k) = none) :
    (timesPropWith p T i j k hmem).run view = .fix := by
  unfold timesPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.timesSlot i j k) hmem
    (.slot i) (.slot j) (.slot k) timesRel timesStep
    (fun b h => timesStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := ha
      exact ⟨x, y, z, read_slot_int_of_getElem? hx,
        read_slot_int_of_getElem? hy, read_slot_int_of_getElem? hz, hmul⟩)
    view hmk

/-! ## Stage 4: truncated division and remainder -/

def divRel (x y z : Int) : Prop := y ≠ 0 ∧ Int.tdiv x y = z

def modRel (x y z : Int) : Prop := y ≠ 0 ∧ Int.tmod x y = z

/-- Divisor interval narrowing shared by `div` and `mod`: a fixed zero
divisor is an immediate conflict (the proposed divisor interval is
empty); a divisor interval touching zero on one side is narrowed away
from zero. -/
def divNormLo (b : GBox) : Int :=
  if b.g1.lo = 0 ∧ b.g1.hi = 0 then b.g1.lo + 1
  else if b.g1.lo = 0 ∧ 0 < b.g1.hi then 1
  else b.g1.lo

def divNormHi (b : GBox) : Int :=
  if b.g1.lo = 0 ∧ b.g1.hi = 0 then b.g1.lo
  else if b.g1.lo = 0 ∧ 0 < b.g1.hi then b.g1.hi
  else if b.g1.hi = 0 ∧ b.g1.lo < 0 then -1
  else b.g1.hi

def divStep : GStep where
  nlo0 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 ∧ b.g2.lo = b.g2.hi then
      b.g1.lo * b.g2.lo - (absValue b.g1.lo - 1)
    else b.g0.lo
  nhi0 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 ∧ b.g2.lo = b.g2.hi then
      b.g1.lo * b.g2.lo + (absValue b.g1.lo - 1)
    else b.g0.hi
  nlo1 b := divNormLo b
  nhi1 b := divNormHi b
  nlo2 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      divResLo b.g1.lo b.g0.lo b.g0.hi
    else b.g2.lo
  nhi2 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      divResHi b.g1.lo b.g0.lo b.g0.hi
    else b.g2.hi

theorem divNorm_spec {b : GBox} {y : Int} (hy : y ≠ 0)
    (hylo : b.g1.lo ≤ y) (hyhi : y ≤ b.g1.hi) :
    max b.g1.lo (divNormLo b) ≤ y ∧ y ≤ min b.g1.hi (divNormHi b) := by
  unfold divNormLo divNormHi
  by_cases hzero : b.g1.lo = 0 ∧ b.g1.hi = 0
  · rw [if_pos hzero]
    omega
  · rw [if_neg hzero]
    by_cases hpos : b.g1.lo = 0 ∧ 0 < b.g1.hi
    · rw [if_pos hpos, if_pos hpos]
      omega
    · rw [if_neg hpos, if_neg hpos]
      by_cases hneg : b.g1.hi = 0 ∧ b.g1.lo < 0
      · rw [if_pos hneg]
        omega
      · rw [if_neg hneg]
        omega

theorem divStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec divRel (divStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  unfold divRel at hR
  obtain ⟨hyne, hdiv⟩ := hR
  constructor
  · unfold GStep.apply
    simp only [divStep, GArg.intersect, GArg.New]
    by_cases hfix : b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 ∧ b.g2.lo = b.g2.hi
    · rw [if_pos hfix]
      obtain ⟨hyfix, hd, hzfix⟩ := hfix
      have hy_eq : y = b.g1.lo := by omega
      have hz_eq : z = b.g2.lo := by omega
      have hq : Int.tdiv x b.g1.lo = b.g2.lo := by
        rw [← hy_eq, hdiv, hz_eq]
      have htmod := tmod_bounds (p := x) (d := b.g1.lo) hd
      have hmul := Int.mul_tdiv_add_tmod x b.g1.lo
      rw [hq] at hmul
      omega
    · rw [if_neg hfix]
      omega
  · constructor
    · unfold GStep.apply
      simp only [divStep, GArg.intersect, GArg.New, divNormLo, divNormHi]
      have hnorm := divNorm_spec (b := b) (y := y) hyne hylo hyhi
      exact hnorm
    · unfold GStep.apply
      simp only [divStep, GArg.intersect, GArg.New]
      by_cases hfix : b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0
      · rw [if_pos hfix]
        obtain ⟨hyfix, hd⟩ := hfix
        have hy_eq : y = b.g1.lo := by omega
        have hhull := tdiv_mem_hull (p := x) (d := y)
          (pl := b.g0.lo) (ph := b.g0.hi) hyne hxlo hxhi
        rw [hdiv] at hhull
        rw [← hy_eq]
        omega
      · rw [if_neg hfix]
        omega

def modStep : GStep where
  nlo0 b := b.g0.lo
  nhi0 b := b.g0.hi
  nlo1 b := divNormLo b
  nhi1 b := divNormHi b
  nlo2 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      modHullLo b.g1.lo b.g0.lo b.g0.hi
    else b.g2.lo
  nhi2 b :=
    if b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0 then
      modHullHi b.g1.lo b.g0.lo b.g0.hi
    else b.g2.hi

theorem modStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec modRel (modStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  unfold modRel at hR
  obtain ⟨hyne, hmod⟩ := hR
  constructor
  · unfold GStep.apply
    simp only [modStep, GArg.intersect, GArg.New]
    omega
  · constructor
    · unfold GStep.apply
      simp only [modStep, GArg.intersect, GArg.New, divNormLo, divNormHi]
      exact divNorm_spec (b := b) (y := y) hyne hylo hyhi
    · unfold GStep.apply
      simp only [modStep, GArg.intersect, GArg.New]
      by_cases hfix : b.g1.lo = b.g1.hi ∧ b.g1.lo ≠ 0
      · rw [if_pos hfix]
        obtain ⟨hyfix, hd⟩ := hfix
        have hy_eq : y = b.g1.lo := by omega
        have hhull := tmod_mem_hull (p := x) (d := y)
          (pl := b.g0.lo) (ph := b.g0.hi) hyne hxlo hxhi
        rw [hmod] at hhull
        rw [← hy_eq]
        omega
      · rw [if_neg hfix]
        omega

def divPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)

def modPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints) :
    PropV2 p T :=
  rel3PropWith p T (.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)

theorem divPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (divPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms o1 o2 r = some b ∧
      (divStep.apply b).out = .conflict ls ∧
      (divStep.apply b).BoundSpec view.doms ∧ (divStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold divPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem divPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (divPropWith p T o1 o2 r hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms o1 o2 r = some b ∧
      (divStep.apply b).out = .prune ps ∧
      (divStep.apply b).BoundSpec view.doms ∧ (divStep.apply b).WF view ∧
      (divStep.apply b).g0.Sub ∧ (divStep.apply b).g1.Sub ∧
      (divStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold divPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem divPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (divPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold divPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem divPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (divPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold divPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem divPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (divPropWith p T o1 o2 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold divPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem divPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.divGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (divPropWith p T o1 o2 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold divPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem divPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.divGen o1 o2 r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms o1 o2 r = none) :
    (divPropWith p T o1 o2 r hmem).run view = .fix := by
  unfold divPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.divGen o1 o2 r) hmem o1 o2 r
    divRel divStep (fun b h => divStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tdiv x y, hx, hy, hz, hq, rfl⟩)
    view hmk

theorem modPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (modPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms o1 o2 r = some b ∧
      (modStep.apply b).out = .conflict ls ∧
      (modStep.apply b).BoundSpec view.doms ∧ (modStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold modPropWith at h
  exact rel3PropWith_run_conflict p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem modPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (modPropWith p T o1 o2 r hmem).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms o1 o2 r = some b ∧
      (modStep.apply b).out = .prune ps ∧
      (modStep.apply b).BoundSpec view.doms ∧ (modStep.apply b).WF view ∧
      (modStep.apply b).g0.Sub ∧ (modStep.apply b).g1.Sub ∧
      (modStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold modPropWith at h
  exact rel3PropWith_run_prune p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem modPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (modPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold modPropWith at h
  exact rel3PropWith_conflict_entailed p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem modPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {ec : EClause p T}
    (h : (modPropWith p T o1 o2 r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold modPropWith at h
  exact rel3PropWith_conflict_lits_false p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h

theorem modPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (modPropWith p T o1 o2 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold modPropWith at h
  exact rel3PropWith_prune_reason_entailed p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem modPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull (DomConstraint.modGen o1 o2 r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (modPropWith p T o1 o2 r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold modPropWith at h
  exact rel3PropWith_prune_lit_none p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hWF (by intro s hs; simpa [dcSlotsFull, DomIntArg.slots] using hs) h hq

theorem modPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (o1 o2 r : DomIntArg) (hmem : DomConstraint.modGen o1 o2 r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGBox? view.doms o1 o2 r = none) :
    (modPropWith p T o1 o2 r hmem).run view = .fix := by
  unfold modPropWith
  exact rel3PropWith_run_fix_of_none p T (DomConstraint.modGen o1 o2 r) hmem o1 o2 r
    modRel modStep (fun b h => modStep_spec (b := b) h)
    (fun a ha => by
      obtain ⟨x, y, hx, hy, hq, hz⟩ := ha
      exact ⟨x, y, Int.tmod x y, hx, hy, hz, hq, rfl⟩)
    view hmk

/-! ## Stage 2: array minimum and maximum -/

/-- If every operand is a literal, recover the list of constants. -/
def constList? : List DomIntArg → Option (List Int)
  | [] => some []
  | .lit k :: rest => (constList? rest).map fun ks => k :: ks
  | .slot _ :: _ => none

/-- The evaluated minimum of a constant list (junk value at `[]`, which is
handled separately).  This is definitionally the source `minValue`. -/
def constMin (ks : List Int) : Int :=
  match minValue (ks.map Value.int) with
  | some m => m
  | none => 0

/-- The evaluated maximum of a constant list (junk value at `[]`). -/
def constMax (ks : List Int) : Int :=
  match maxValue (ks.map Value.int) with
  | some m => m
  | none => 0

theorem map_read_constList? {os : List DomIntArg} {ks : List Int}
    (h : constList? os = some ks) (a : Assignment) :
    os.map (DomIntArg.read a) = ks.map Value.int := by
  induction os generalizing ks with
  | nil =>
      simp [constList?] at h
      subst ks
      rfl
  | cons o os ih =>
      cases o with
      | lit k =>
          simp only [constList?] at h
          cases hrest : constList? os with
          | none => simp [hrest] at h
          | some ks' =>
              simp [hrest] at h
              subst ks
              simp only [List.map_cons, DomIntArg.read_lit]
              rw [ih hrest]
      | slot s => simp [constList?] at h

theorem minGen_const_force {os : List DomIntArg} {r : DomIntArg} {ks : List Int}
    (hconst : constList? os = some ks) :
    ∀ a, (DomConstraint.minGen os r).SatisfiedBy a →
      DomIntArg.read a r = .int (constMin ks) := by
  intro a ha
  obtain ⟨m, hr, hmin⟩ := ha
  have hmap := map_read_constList? hconst a
  rw [hmap] at hmin
  have hm : constMin ks = m := by
    unfold constMin
    rw [hmin]
  rw [hr, hm]

theorem maxGen_const_force {os : List DomIntArg} {r : DomIntArg} {ks : List Int}
    (hconst : constList? os = some ks) :
    ∀ a, (DomConstraint.maxGen os r).SatisfiedBy a →
      DomIntArg.read a r = .int (constMax ks) := by
  intro a ha
  obtain ⟨m, hr, hmax⟩ := ha
  have hmap := map_read_constList? hconst a
  rw [hmap] at hmax
  have hm : constMax ks = m := by
    unfold constMax
    rw [hmax]
  rw [hr, hm]

theorem minGen_empty_unsat (r : DomIntArg) :
    ∀ a, ¬(DomConstraint.minGen [] r).SatisfiedBy a := by
  intro a ha
  obtain ⟨m, _, hmin⟩ := ha
  simp [minValue] at hmin

theorem maxGen_empty_unsat (r : DomIntArg) :
    ∀ a, ¬(DomConstraint.maxGen [] r).SatisfiedBy a := by
  intro a ha
  obtain ⟨m, _, hmax⟩ := ha
  simp [maxValue] at hmax

/-- A step that narrows the first operand to the singleton `m` and leaves
the two dummy literal operands unchanged. -/
def eqLitStep (m : Int) : GStep where
  nlo0 _ := m
  nhi0 _ := m
  nlo1 b := b.g1.lo
  nhi1 b := b.g1.hi
  nlo2 b := b.g2.lo
  nhi2 b := b.g2.hi

theorem eqLitStep_spec (m : Int) {b : GBox} (_hcs : b.CurSpec) :
    GSpec (fun x _ _ => x = m) ((eqLitStep m).apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z hx hy hz hR
  unfold GStep.apply at hx hy hz
  simp only [GArg.Cur, GArg.intersect] at hx hy hz
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hzlo, hzhi⟩ := hz
  have hx_eq : x = m := hR
  constructor
  · unfold GStep.apply
    simp only [eqLitStep, GArg.intersect, GArg.New]
    omega
  · constructor
    · unfold GStep.apply
      simp only [eqLitStep, GArg.intersect, GArg.New]
      omega
    · unfold GStep.apply
      simp only [eqLitStep, GArg.intersect, GArg.New]
      omega

/-- A step that makes the first operand's proposed interval empty, used
only under an unsatisfiable relation. -/
def emptyStep : GStep where
  nlo0 b := b.g0.lo + 1
  nhi0 b := b.g0.lo
  nlo1 b := b.g1.lo
  nhi1 b := b.g1.hi
  nlo2 b := b.g2.lo
  nhi2 b := b.g2.hi

def falseRel (_ _ _ : Int) : Prop := False

theorem emptyStep_spec {b : GBox} (_hcs : b.CurSpec) :
    GSpec falseRel (emptyStep.apply b) := by
  refine ⟨GArg.intersect_sub _ _ _, GArg.intersect_sub _ _ _,
    GArg.intersect_sub _ _ _, ?_⟩
  intro x y z _ _ _ hR
  simp [falseRel] at hR

/-- Force the result operand `r` to the value `m`; the two dummy literal
operands carry `m` as well so that only `r` can generate a prune. -/
def forcedValuePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m) : PropV2 p T :=
  rel3PropWith p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m)
    (fun b h => eqLitStep_spec m h)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)

/-- The unsatisfiable-array builder: the first operand is the true result
operand so that missing bounds still produce `.fix`; with bounds present
it emits the result bounds (or the empty clause for a literal result). -/
def emptyGenPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints)
    (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a) : PropV2 p T :=
  rel3PropWith p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b h => emptyStep_spec h)
    (fun a ha => False.elim (hunsat a ha))

/-- The no-op fallback for operand lists whose non-integer-tail reading is
ambiguous. -/
def fixGenPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) : PropV2 p T :=
  { vars := (dcSlotsFull dc).toArray
    events := (dcSlotsFull dc).toArray.map fun s => (s, .bounds)
    run := fun _ => .fix }

def minGenPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints) : PropV2 p T :=
  match os with
  | [] => emptyGenPropWith p T (DomConstraint.minGen [] r) hmem r (minGen_empty_unsat r)
  | o :: os' =>
      match hconst : constList? (o :: os') with
      | some ks =>
          forcedValuePropWith p T (DomConstraint.minGen (o :: os') r) hmem r
            (constMin ks) (minGen_const_force hconst)
      | none => fixGenPropWith p T (DomConstraint.minGen (o :: os') r)

def maxGenPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints) : PropV2 p T :=
  match os with
  | [] => emptyGenPropWith p T (DomConstraint.maxGen [] r) hmem r (maxGen_empty_unsat r)
  | o :: os' =>
      match hconst : constList? (o :: os') with
      | some ks =>
          forcedValuePropWith p T (DomConstraint.maxGen (o :: os') r) hmem r
            (constMax ks) (maxGen_const_force hconst)
      | none => fixGenPropWith p T (DomConstraint.maxGen (o :: os') r)

/-! ### Contracts for the shared forced-value and empty-array builders -/

theorem forcedValuePropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms r (.lit m) (.lit m) = some b ∧
      ((eqLitStep m).apply b).out = .conflict ls ∧
      ((eqLitStep m).apply b).BoundSpec view.doms ∧
      ((eqLitStep m).apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_run_conflict p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem forcedValuePropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms r (.lit m) (.lit m) = some b ∧
      ((eqLitStep m).apply b).out = .prune ps ∧
      ((eqLitStep m).apply b).BoundSpec view.doms ∧
      ((eqLitStep m).apply b).WF view ∧
      ((eqLitStep m).apply b).g0.Sub ∧
      ((eqLitStep m).apply b).g1.Sub ∧
      ((eqLitStep m).apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_run_prune p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem forcedValuePropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_conflict_entailed p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem forcedValuePropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_conflict_lits_false p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem forcedValuePropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_prune_reason_entailed p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h hq

theorem forcedValuePropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (forcedValuePropWith p T dc hmem r m hforce).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold forcedValuePropWith at h
  exact rel3PropWith_prune_lit_none p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩)
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h hq

theorem forcedValuePropWith_run_fix_of_no_bounds
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg) (m : Int)
    (hforce : ∀ a, dc.SatisfiedBy a → DomIntArg.read a r = .int m)
    (view : EngineView)
    (hmk : mkGBox? view.doms r (.lit m) (.lit m) = none) :
    (forcedValuePropWith p T dc hmem r m hforce).run view = .fix := by
  unfold forcedValuePropWith
  exact rel3PropWith_run_fix_of_none p T dc hmem r (.lit m) (.lit m)
    (fun x _ _ => x = m) (eqLitStep m) (fun b hh => eqLitStep_spec m hh)
    (fun a ha => ⟨m, m, m, hforce a ha, rfl, rfl, rfl⟩) view hmk

theorem emptyGenPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .conflict ec) :
    ∃ b ls, mkGBox? view.doms r (.lit 0) (.lit 0) = some b ∧
      (emptyStep.apply b).out = .conflict ls ∧
      (emptyStep.apply b).BoundSpec view.doms ∧ (emptyStep.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_run_conflict p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem emptyGenPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .prune psArr) :
    ∃ b ps, mkGBox? view.doms r (.lit 0) (.lit 0) = some b ∧
      (emptyStep.apply b).out = .prune ps ∧
      (emptyStep.apply b).BoundSpec view.doms ∧ (emptyStep.apply b).WF view ∧
      (emptyStep.apply b).g0.Sub ∧ (emptyStep.apply b).g1.Sub ∧
      (emptyStep.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_run_prune p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem emptyGenPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_conflict_entailed p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem emptyGenPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {ec : EClause p T}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_conflict_lits_false p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h

theorem emptyGenPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_prune_reason_entailed p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h hq

theorem emptyGenPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView) (hWF : ViewWF view (dcSlotsFull dc).toArray)
    (hslots : ∀ s ∈ r.slots, s ∈ (dcSlotsFull dc).toArray.toList)
    {psArr : Array (PLit × EClause p T)}
    (h : (emptyGenPropWith p T dc hmem r hunsat).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  unfold emptyGenPropWith at h
  exact rel3PropWith_prune_lit_none p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha))
    view hWF (by
      intro s hs
      exact hslots s (by simpa [DomIntArg.slots] using hs)) h hq

theorem emptyGenPropWith_run_fix_of_no_bounds
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (dc : DomConstraint) (hmem : dc ∈ p.constraints) (r : DomIntArg)
    (hunsat : ∀ a, ¬dc.SatisfiedBy a)
    (view : EngineView)
    (hmk : mkGBox? view.doms r (.lit 0) (.lit 0) = none) :
    (emptyGenPropWith p T dc hmem r hunsat).run view = .fix := by
  unfold emptyGenPropWith
  exact rel3PropWith_run_fix_of_none p T dc hmem r (.lit 0) (.lit 0)
    falseRel emptyStep (fun b hh => emptyStep_spec hh)
    (fun a ha => False.elim (hunsat a ha)) view hmk


/-! ### Public contracts for the array builders -/

theorem minGen_slots_mem {os : List DomIntArg} {r : DomIntArg} {s : Nat}
    (hs : s ∈ r.slots) :
    s ∈ (dcSlotsFull (DomConstraint.minGen os r)).toArray.toList := by
  have h : s ∈ (os.flatMap DomIntArg.slots ++ r.slots) := List.mem_append_right _ hs
  simpa [dcSlotsFull] using h

theorem maxGen_slots_mem {os : List DomIntArg} {r : DomIntArg} {s : Nat}
    (hs : s ∈ r.slots) :
    s ∈ (dcSlotsFull (DomConstraint.maxGen os r)).toArray.toList := by
  have h : s ∈ (os.flatMap DomIntArg.slots ++ r.slots) := List.mem_append_right _ hs
  simpa [dcSlotsFull] using h

theorem minGenPropWith_nil (p : CompiledProblem DomConstraint) (T : LitTable)
    (r : DomIntArg) (hmem : DomConstraint.minGen [] r ∈ p.constraints) :
    minGenPropWith p T [] r hmem =
      emptyGenPropWith p T (DomConstraint.minGen [] r) hmem r (minGen_empty_unsat r) :=
  rfl

theorem maxGenPropWith_nil (p : CompiledProblem DomConstraint) (T : LitTable)
    (r : DomIntArg) (hmem : DomConstraint.maxGen [] r ∈ p.constraints) :
    maxGenPropWith p T [] r hmem =
      emptyGenPropWith p T (DomConstraint.maxGen [] r) hmem r (maxGen_empty_unsat r) :=
  rfl

theorem minGenPropWith_cons_some (p : CompiledProblem DomConstraint) (T : LitTable)
    (o : DomIntArg) (os' : List DomIntArg) (r : DomIntArg) (ks : List Int)
    (hmem : DomConstraint.minGen (o :: os') r ∈ p.constraints)
    (hconst : constList? (o :: os') = some ks) :
    minGenPropWith p T (o :: os') r hmem =
      forcedValuePropWith p T (DomConstraint.minGen (o :: os') r) hmem r
        (constMin ks) (minGen_const_force hconst) := by
  simp only [minGenPropWith]
  split
  · rename_i h
    rw [hconst] at h
    injection h with hks
    subst hks
    rfl
  · rename_i h
    rw [hconst] at h
    cases h

theorem maxGenPropWith_cons_some (p : CompiledProblem DomConstraint) (T : LitTable)
    (o : DomIntArg) (os' : List DomIntArg) (r : DomIntArg) (ks : List Int)
    (hmem : DomConstraint.maxGen (o :: os') r ∈ p.constraints)
    (hconst : constList? (o :: os') = some ks) :
    maxGenPropWith p T (o :: os') r hmem =
      forcedValuePropWith p T (DomConstraint.maxGen (o :: os') r) hmem r
        (constMax ks) (maxGen_const_force hconst) := by
  simp only [maxGenPropWith]
  split
  · rename_i h
    rw [hconst] at h
    injection h with hks
    subst hks
    rfl
  · rename_i h
    rw [hconst] at h
    cases h

theorem minGenPropWith_cons_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o : DomIntArg) (os' : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen (o :: os') r ∈ p.constraints)
    (hconst : constList? (o :: os') = none) :
    minGenPropWith p T (o :: os') r hmem =
      fixGenPropWith p T (DomConstraint.minGen (o :: os') r) := by
  simp only [minGenPropWith]
  split
  · rename_i h
    rw [hconst] at h
    cases h
  · rfl

theorem maxGenPropWith_cons_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (o : DomIntArg) (os' : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen (o :: os') r ∈ p.constraints)
    (hconst : constList? (o :: os') = none) :
    maxGenPropWith p T (o :: os') r hmem =
      fixGenPropWith p T (DomConstraint.maxGen (o :: os') r) := by
  simp only [maxGenPropWith]
  split
  · rename_i h
    rw [hconst] at h
    cases h
  · rfl

theorem minGenPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {ec : EClause p T}
    (h : (minGenPropWith p T os r hmem).run view = .conflict ec) :
    ∃ (step : GStep) (d : Int) (b : GBox) (ls : List Literal),
      mkGBox? view.doms r (.lit d) (.lit d) = some b ∧
      (step.apply b).out = .conflict ls ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
        emptyGenPropWith_run_conflict p T _ hmem r _ view hWF
          (fun s hs => minGen_slots_mem hs) h
      exact ⟨emptyStep, 0, b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
          forcedValuePropWith_run_conflict p T _ hmem r (constMin ks) _ view hWF
            (fun s hs => minGen_slots_mem hs) h
        exact ⟨eqLitStep (constMin ks), constMin ks, b, ls, hb, hout, hbound, hwf,
          hlit, hdec, hent, hfalse⟩

theorem minGenPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minGenPropWith p T os r hmem).run view = .prune psArr) :
    ∃ (step : GStep) (d : Int) (b : GBox) (ps : List (Literal × List Literal)),
      mkGBox? view.doms r (.lit d) (.lit d) = some b ∧
      (step.apply b).out = .prune ps ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      (step.apply b).g0.Sub ∧ (step.apply b).g1.Sub ∧ (step.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
        emptyGenPropWith_run_prune p T _ hmem r _ view hWF
          (fun s hs => minGen_slots_mem hs) h
      exact ⟨emptyStep, 0, b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
          forcedValuePropWith_run_prune p T _ hmem r (constMin ks) _ view hWF
            (fun s hs => minGen_slots_mem hs) h
        exact ⟨eqLitStep (constMin ks), constMin ks, b, ps, hb, hout, hbound, hwf,
          hs0, hs1, hs2, hfacts⟩

theorem minGenPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {ec : EClause p T}
    (h : (minGenPropWith p T os r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_conflict_entailed p T _ hmem r _ view hWF
        (fun s hs => minGen_slots_mem hs) h
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_conflict_entailed p T _ hmem r (constMin ks) _
          view hWF (fun s hs => minGen_slots_mem hs) h

theorem minGenPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {ec : EClause p T}
    (h : (minGenPropWith p T os r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_conflict_lits_false p T _ hmem r _ view hWF
        (fun s hs => minGen_slots_mem hs) h
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_conflict_lits_false p T _ hmem r (constMin ks) _
          view hWF (fun s hs => minGen_slots_mem hs) h

theorem minGenPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minGenPropWith p T os r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_prune_reason_entailed p T _ hmem r _ view hWF
        (fun s hs => minGen_slots_mem hs) h hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_prune_reason_entailed p T _ hmem r (constMin ks) _
          view hWF (fun s hs => minGen_slots_mem hs) h hq

theorem minGenPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.minGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (minGenPropWith p T os r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_prune_lit_none p T _ hmem r _ view hWF
        (fun s hs => minGen_slots_mem hs) h hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_prune_lit_none p T _ hmem r (constMin ks) _
          view hWF (fun s hs => minGen_slots_mem hs) h hq

theorem minGenPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.minGen os r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGArg? view.doms r = none) :
    (minGenPropWith p T os r hmem).run view = .fix := by
  cases os with
  | nil =>
      rw [minGenPropWith_nil p T r hmem]
      exact emptyGenPropWith_run_fix_of_no_bounds p T _ hmem r _ view
        (by simp [mkGBox?, hmk])
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [minGenPropWith_cons_none p T o os' r hmem hnone]
        rfl
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [minGenPropWith_cons_some p T o os' r ks hmem hks]
        exact forcedValuePropWith_run_fix_of_no_bounds p T _ hmem r (constMin ks) _
          view (by simp [mkGBox?, hmk])

theorem maxGenPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {ec : EClause p T}
    (h : (maxGenPropWith p T os r hmem).run view = .conflict ec) :
    ∃ (step : GStep) (d : Int) (b : GBox) (ls : List Literal),
      mkGBox? view.doms r (.lit d) (.lit d) = some b ∧
      (step.apply b).out = .conflict ls ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      ec.lits = ls.toArray.map pLit ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls ∧
      (∀ l ∈ ls,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
        emptyGenPropWith_run_conflict p T _ hmem r _ view hWF
          (fun s hs => maxGen_slots_mem hs) h
      exact ⟨emptyStep, 0, b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        obtain ⟨b, ls, hb, hout, hbound, hwf, hlit, hdec, hent, hfalse⟩ :=
          forcedValuePropWith_run_conflict p T _ hmem r (constMax ks) _ view hWF
            (fun s hs => maxGen_slots_mem hs) h
        exact ⟨eqLitStep (constMax ks), constMax ks, b, ls, hb, hout, hbound, hwf,
          hlit, hdec, hent, hfalse⟩

theorem maxGenPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxGenPropWith p T os r hmem).run view = .prune psArr) :
    ∃ (step : GStep) (d : Int) (b : GBox) (ps : List (Literal × List Literal)),
      mkGBox? view.doms r (.lit d) (.lit d) = some b ∧
      (step.apply b).out = .prune ps ∧
      (step.apply b).BoundSpec view.doms ∧ (step.apply b).WF view ∧
      (step.apply b).g0.Sub ∧ (step.apply b).g1.Sub ∧ (step.apply b).g2.Sub ∧
      (∀ q ∈ psArr.toList, ∃ l reason, (l, reason) ∈ ps ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
            = some false)) := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
        emptyGenPropWith_run_prune p T _ hmem r _ view hWF
          (fun s hs => maxGen_slots_mem hs) h
      exact ⟨emptyStep, 0, b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        obtain ⟨b, ps, hb, hout, hbound, hwf, hs0, hs1, hs2, hfacts⟩ :=
          forcedValuePropWith_run_prune p T _ hmem r (constMax ks) _ view hWF
            (fun s hs => maxGen_slots_mem hs) h
        exact ⟨eqLitStep (constMax ks), constMax ks, b, ps, hb, hout, hbound, hwf,
          hs0, hs1, hs2, hfacts⟩

theorem maxGenPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {ec : EClause p T}
    (h : (maxGenPropWith p T os r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_conflict_entailed p T _ hmem r _ view hWF
        (fun s hs => maxGen_slots_mem hs) h
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_conflict_entailed p T _ hmem r (constMax ks) _
          view hWF (fun s hs => maxGen_slots_mem hs) h

theorem maxGenPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {ec : EClause p T}
    (h : (maxGenPropWith p T os r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_conflict_lits_false p T _ hmem r _ view hWF
        (fun s hs => maxGen_slots_mem hs) h
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_conflict_lits_false p T _ hmem r (constMax ks) _
          view hWF (fun s hs => maxGen_slots_mem hs) h

theorem maxGenPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxGenPropWith p T os r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_prune_reason_entailed p T _ hmem r _ view hWF
        (fun s hs => maxGen_slots_mem hs) h hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_prune_reason_entailed p T _ hmem r (constMax ks) _
          view hWF (fun s hs => maxGen_slots_mem hs) h hq

theorem maxGenPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (DomConstraint.maxGen os r)).toArray)
    {psArr : Array (PLit × EClause p T)}
    (h : (maxGenPropWith p T os r hmem).run view = .prune psArr)
    {q : PLit × EClause p T} (hq : q ∈ psArr.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem] at h
      exact emptyGenPropWith_prune_lit_none p T _ hmem r _ view hWF
        (fun s hs => maxGen_slots_mem hs) h hq
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone] at h
        simp [fixGenPropWith] at h
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks] at h
        exact forcedValuePropWith_prune_lit_none p T _ hmem r (constMax ks) _
          view hWF (fun s hs => maxGen_slots_mem hs) h hq

theorem maxGenPropWith_run_fix_of_no_bounds (p : CompiledProblem DomConstraint) (T : LitTable)
    (os : List DomIntArg) (r : DomIntArg)
    (hmem : DomConstraint.maxGen os r ∈ p.constraints)
    (view : EngineView)
    (hmk : mkGArg? view.doms r = none) :
    (maxGenPropWith p T os r hmem).run view = .fix := by
  cases os with
  | nil =>
      rw [maxGenPropWith_nil p T r hmem]
      exact emptyGenPropWith_run_fix_of_no_bounds p T _ hmem r _ view
        (by simp [mkGBox?, hmk])
  | cons o os' =>
      by_cases hnone : constList? (o :: os') = none
      · rw [maxGenPropWith_cons_none p T o os' r hmem hnone]
        rfl
      · obtain ⟨ks, hks⟩ : ∃ ks, constList? (o :: os') = some ks := by
          cases hc : constList? (o :: os') with
          | none => exact absurd hc hnone
          | some ks => exact ⟨ks, rfl⟩
        rw [maxGenPropWith_cons_some p T o os' r ks hmem hks]
        exact forcedValuePropWith_run_fix_of_no_bounds p T _ hmem r (constMax ks) _
          view (by simp [mkGBox?, hmk])

end LeanFzn.Engine

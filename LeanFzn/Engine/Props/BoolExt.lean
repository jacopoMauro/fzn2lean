/-
File: LeanFzn/Engine/Props/BoolExt.lean

Dedicated Boolean propagators for the remaining Boolean families:
`bool_not`, `bool_and`, `bool_or`, `bool_eq` and `array_bool_and`.
`bool_clause` already has its N6 propagator in `Props/Bool.lean` and is
deliberately not duplicated here.

The module is built around a small Boolean-domain abstraction.  A
`BArg` records, for one operand slot, the two current Boolean values
(`curF`, `curT`) and two proposed values (`newF`, `newT`) after a
propagation step.  A step that removes values proves a `BSpec`: every
relation tuple inside the current box remains inside the proposed box.
The output layer is generic: a conflict clause is the list of negated
current singleton facts of all operands, and a prune reason for a removed
value `v` of slot `s` is `s = !v` together with the negated singleton
facts of the other operands.  Both are entailed by the corresponding
constraint whenever the step is sound.

Non-Boolean or empty operand domains make the run a `.fix` no-op.  The
duplicated-slot cases (`i = j` for the binary families, repeated slots in
`array_bool_and`) are also `.fix`: the Boolean abstractions below keep one
`BArg` per operand position, so duplicate positions would let a batch
prune both values of one domain.  Returning `.fix` there keeps every
emitted prune non-emptying.  `array_bool_and` additionally takes the
initial converted domains in its soundness contracts so that a Boolean
current source domain can be tied to Boolean values in accepted
assignments (the leaf semantics of `array_bool_and` treats a non-Boolean
source as `false`, unlike the binary Boolean families).

Dependencies:
  - LeanFzn.Engine.Prop: `PropV2`, `EClause.ofLiterals`, `Entailed`.
  - LeanFzn.Engine.Dom: `DomC`, `DomC.fixedValue`, `DomC.evalLit`.
  - LeanFzn.Engine.Props.Linear: `ViewWF` (not needed below: every
    Boolean fact follows from the `.bool` constructor).

DAG:
  LeanFzn.Engine.Prop -> LeanFzn.Engine.Props.BoolExt
-/
import LeanFzn.Engine.Prop

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Boolean operand boxes -/

/-- The Boolean state of one operand slot.

`curF`/`curT` say whether the current compact domain contains `false` /
`true`; `newF`/`newT` are the proposed values after one propagation step.
`ofDom?` only builds arguments whose current domain is a nonempty
`.bool` domain, so at least one of `curF`, `curT` is `true`. -/
structure BArg where
  slot : Nat
  curF : Bool
  curT : Bool
  newF : Bool
  newT : Bool
  deriving Repr, DecidableEq, Inhabited

namespace BArg

/-- Current membership of a Boolean value. -/
def cur (a : BArg) (v : Bool) : Bool := if v then a.curT else a.curF

/-- Proposed membership of a Boolean value. -/
def new (a : BArg) (v : Bool) : Bool := if v then a.newT else a.newF

/-- The proposed box is contained in the current box. -/
def Sub (a : BArg) : Prop := ∀ v, a.new v = true → a.cur v = true

/-- No Boolean value survives for this operand. -/
def emptyNew (a : BArg) : Bool := !a.newF && !a.newT

/-- The negated singleton fact of a fixed operand (`s ≠ false` is
`posBool s true`; `s ≠ true` is `posBool s false`). -/
def fixedLit? (a : BArg) : Option Literal :=
  if a.curF && !a.curT then some (posBool a.slot true)
  else if a.curT && !a.curF then some (posBool a.slot false)
  else none

/-- All negated singleton facts of a fixed operand (zero or one). -/
def fixedLit (a : BArg) : List Literal := a.fixedLit?.toList

/-- The three nonempty Boolean domain shapes recognised by the
propagators.  Keeping the shape separate from the argument record makes
the malformed-input proofs uniform. -/
inductive BShape where
  | fixedFalse
  | fixedTrue
  | full
  deriving Repr, DecidableEq, Inhabited

namespace BShape

def curF : BShape → Bool
  | fixedFalse | full => true
  | fixedTrue => false

def curT : BShape → Bool
  | fixedFalse => false
  | fixedTrue | full => true

/-- Recognise a nonempty Boolean compact domain. -/
def ofDom? (d : DomC) : Option BShape :=
  match d with
  | .bool _ =>
      match d.fixedValue with
      | some (.bool false) => some .fixedFalse
      | some (.bool true) => some .fixedTrue
      | some _ => none
      | none =>
          if d.mem (.bool false) && d.mem (.bool true) then some .full
          else none
  | _ => none

theorem ofDom?_isBool {d : DomC} {sh : BShape}
    (h : ofDom? d = some sh) : ∃ bits, d = .bool bits := by
  cases d with
  | bool bits => exact ⟨bits, rfl⟩
  | bounds lo hi => simp [ofDom?] at h
  | bitset lo words => simp [ofDom?] at h
  | boundsHoles lo hi holes => simp [ofDom?] at h
  | sparse values => simp [ofDom?] at h

theorem ofDom?_fixedFalse {d : DomC} {sh : BShape}
    (h : ofDom? d = some sh) (hsh : sh = fixedFalse) :
    d.fixedValue = some (.bool false) := by
  subst hsh
  cases d with
  | bool bits =>
      dsimp [ofDom?] at h
      split at h
      · assumption
      · cases h
      · cases h
      · split at h <;> cases h
  | bounds lo hi => simp [ofDom?] at h
  | bitset lo words => simp [ofDom?] at h
  | boundsHoles lo hi holes => simp [ofDom?] at h
  | sparse values => simp [ofDom?] at h

theorem ofDom?_fixedTrue {d : DomC} {sh : BShape}
    (h : ofDom? d = some sh) (hsh : sh = fixedTrue) :
    d.fixedValue = some (.bool true) := by
  subst hsh
  cases d with
  | bool bits =>
      dsimp [ofDom?] at h
      split at h
      · cases h
      · assumption
      · cases h
      · split at h <;> cases h
  | bounds lo hi => simp [ofDom?] at h
  | bitset lo words => simp [ofDom?] at h
  | boundsHoles lo hi holes => simp [ofDom?] at h
  | sparse values => simp [ofDom?] at h

theorem ofDom?_full_none {d : DomC} {sh : BShape}
    (h : ofDom? d = some sh) (hsh : sh = full) :
    d.fixedValue = none := by
  subst hsh
  cases d with
  | bool bits =>
      dsimp [ofDom?] at h
      split at h
      · cases h
      · cases h
      · cases h
      · split at h
        · assumption
        · cases h
  | bounds lo hi => simp [ofDom?] at h
  | bitset lo words => simp [ofDom?] at h
  | boundsHoles lo hi holes => simp [ofDom?] at h
  | sparse values => simp [ofDom?] at h

end BShape

/-- Build the argument of a slot from a recognised shape. -/
def ofShape (s : Nat) (sh : BShape) : BArg :=
  { slot := s, curF := sh.curF, curT := sh.curT,
    newF := sh.curF, newT := sh.curT }

/-- Build the argument of a slot whose current compact domain is a
nonempty `Bool` domain.  Fixed domains are recognised through
`fixedValue`; a domain with both values must have both membership bits
set.  Every other shape (integer domains, empty Boolean domains,
out-of-range slots) is malformed for these propagators. -/
def ofDom? (s : Nat) (d : DomC) : Option BArg :=
  (BShape.ofDom? d).map (ofShape s)

/-- Read the Boolean argument of a slot from an engine view. -/
def mk? (doms : Array DomC) (s : Nat) : Option BArg :=
  BArg.ofDom? s (doms.getD s DomC.empty)

theorem ofDom?_slot {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) : a.slot = s := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh =>
      simp [hsh] at h
      subst a
      rfl

/-- The current flags of a successfully built argument are one of the
three nonempty Boolean domains. -/
theorem ofDom?_cur_cases {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) :
    (a.curF = true ∧ a.curT = false) ∨
      (a.curF = false ∧ a.curT = true) ∨
      (a.curF = true ∧ a.curT = true) := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh =>
      simp [hsh] at h
      subst a
      cases sh <;> simp [BArg.ofShape, BShape.curF, BShape.curT]

theorem ofDom?_isBool {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) : ∃ bits, d = .bool bits := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh => exact BShape.ofDom?_isBool hsh

theorem ofDom?_eq_none_of_not_bool {s : Nat} {d : DomC}
    (h : ∀ bits, d ≠ .bool bits) : BArg.ofDom? s d = none := by
  cases d with
  | bool bits => exact absurd rfl (h bits)
  | bounds lo hi => rfl
  | bitset lo words => rfl
  | boundsHoles lo hi holes => rfl
  | sparse values => rfl

theorem ofDom?_fixed_false {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) (hf : a.curF = true) (ht : a.curT = false) :
    d.fixedValue = some (.bool false) := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh =>
      simp [hsh] at h
      subst a
      cases sh with
      | fixedFalse => exact BShape.ofDom?_fixedFalse hsh rfl
      | fixedTrue => simp [BArg.ofShape, BShape.curF] at hf
      | full => simp [BArg.ofShape, BShape.curT] at ht

theorem ofDom?_fixed_true {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) (hf : a.curF = false) (ht : a.curT = true) :
    d.fixedValue = some (.bool true) := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh =>
      simp [hsh] at h
      subst a
      cases sh with
      | fixedFalse => simp [BArg.ofShape, BShape.curF] at hf
      | fixedTrue => exact BShape.ofDom?_fixedTrue hsh rfl
      | full => simp [BArg.ofShape, BShape.curF] at hf

theorem ofDom?_full_fixed_none {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) (hf : a.curF = true) (ht : a.curT = true) :
    d.fixedValue = none := by
  unfold BArg.ofDom? at h
  cases hsh : BShape.ofDom? d with
  | none => simp [hsh] at h
  | some sh =>
      simp [hsh] at h
      subst a
      cases sh with
      | fixedFalse => simp [BArg.ofShape, BShape.curT] at ht
      | fixedTrue => simp [BArg.ofShape, BShape.curF] at hf
      | full => exact BShape.ofDom?_full_none hsh rfl

/-- The negated singleton facts of an operand built from `d` evaluate to
`false` on `d`. -/
theorem ofDom?_evalLit_fixed {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) :
    ∀ l ∈ a.fixedLit, d.evalLit l = some false := by
  rcases ofDom?_cur_cases h with ⟨hf, ht⟩ | ⟨hf, ht⟩ | ⟨hf, ht⟩
  · have hfv := ofDom?_fixed_false h hf ht
    have hsa : a.slot = s := ofDom?_slot h
    intro l hl
    have hl' : l = posBool s true := by
      simpa [BArg.fixedLit, BArg.fixedLit?, hf, ht, hsa] using hl
    subst hl'
    simpa using DomC.evalLit_posBool_of_fixed (d := d) (s := s) (b := false) hfv
  · have hfv := ofDom?_fixed_true h hf ht
    have hsa : a.slot = s := ofDom?_slot h
    intro l hl
    have hl' : l = posBool s false := by
      simpa [BArg.fixedLit, BArg.fixedLit?, hf, ht, hsa] using hl
    subst hl'
    simpa using DomC.evalLit_posBool_of_fixed (d := d) (s := s) (b := true) hfv
  · have hfv := ofDom?_full_fixed_none h hf ht
    intro l hl
    simp [BArg.fixedLit, BArg.fixedLit?, hf, ht] at hl

/-- A Boolean literal is unassigned on a full Boolean domain. -/
theorem ofDom?_evalLit_none_full {s : Nat} {d : DomC} {a : BArg}
    (h : BArg.ofDom? s d = some a) (hf : a.curF = true) (ht : a.curT = true)
    (b : Bool) : d.evalLit (posBool a.slot b) = none := by
  have hfv := ofDom?_full_fixed_none h hf ht
  simp [DomC.evalLit, posBool, hfv]

end BArg

/-! ## Lists of Boolean operands -/

/-- The evaluator's Boolean view of an operand.  A missing or non-Boolean
value reads as `false`; on an accepted assignment the source operand of
`array_bool_and` may be non-Boolean, and `slotIsBoolB` also reads it as
`false` for the `true` test. -/
def BArg.valAt (a : BArg) (b : Assignment) : Bool :=
  match b[a.slot]? with
  | some (.bool v) => v
  | _ => false

namespace BArgs

/-- Negated singleton facts of all currently fixed operands. -/
def fixedLits : List BArg → List Literal
  | [] => []
  | a :: as => a.fixedLit ++ fixedLits as

/-- All Boolean tuples in the current box.  Each operand contributes the
values still present in its current domain. -/
def enum : List BArg → List (List Bool)
  | [] => [[]]
  | a :: as =>
      (if a.curF then (enum as).map (fun vs => false :: vs) else []) ++
      (if a.curT then (enum as).map (fun vs => true :: vs) else [])

/-- Pointwise membership in the current Boolean box. -/
def curVec : List BArg → List Bool → Bool
  | [], [] => true
  | a :: as, v :: vs => a.cur v && curVec as vs
  | _, _ => false

/-- The values of an accepted assignment at a list of Boolean operands. -/
def valsOf (b : Assignment) (args : List BArg) : List Bool :=
  args.map (fun a => a.valAt b)

/-- Read a list of operand slots.  A non-Boolean or out-of-range slot
makes the whole list malformed. -/
def ofSlots (doms : Array DomC) : List Nat → Option (List BArg)
  | [] => some []
  | s :: ss =>
      match BArg.mk? doms s with
      | none => none
      | some a =>
          match ofSlots doms ss with
          | none => none
          | some as => some (a :: as)

/-- Every operand has at least one current Boolean value. -/
def AllCur (args : List BArg) : Prop :=
  ∀ a ∈ args, a.curF = true ∨ a.curT = true

theorem ofSlots_map_slot {doms : Array DomC} {slots : List Nat} {args : List BArg}
    (h : ofSlots doms slots = some args) : args.map BArg.slot = slots := by
  induction slots generalizing args with
  | nil =>
      simp [ofSlots] at h
      subst args
      rfl
  | cons s ss ih =>
      simp only [ofSlots] at h
      cases ha : BArg.mk? doms s with
      | none => rw [ha] at h; cases h
      | some a =>
          rw [ha] at h
          cases hr : ofSlots doms ss with
          | none => rw [hr] at h; cases h
          | some as =>
              rw [hr] at h
              injection h with hargs
              subst hargs
              simp only [List.map_cons, ih hr]
              rw [BArg.ofDom?_slot ha]

theorem ofSlots_allCur {doms : Array DomC} {slots : List Nat} {args : List BArg}
    (h : ofSlots doms slots = some args) : AllCur args := by
  induction slots generalizing args with
  | nil =>
      simp [ofSlots] at h
      subst args
      intro a ha
      simp at ha
  | cons s ss ih =>
      simp only [ofSlots] at h
      cases ha : BArg.mk? doms s with
      | none => rw [ha] at h; cases h
      | some a =>
          rw [ha] at h
          cases hr : ofSlots doms ss with
          | none => rw [hr] at h; cases h
          | some as =>
              rw [hr] at h
              injection h with hargs
              subst hargs
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · rcases BArg.ofDom?_cur_cases ha with h | h | h
                · exact Or.inl h.1
                · exact Or.inr h.2
                · exact Or.inl h.1
              · exact ih hr x hx

/-- A slot whose view domain is not a nonempty Boolean domain makes the
whole operand list malformed. -/
theorem ofSlots_eq_none_of_mem_mk_none {doms : Array DomC} {slots : List Nat}
    {s : Nat} (hs : s ∈ slots) (hm : BArg.mk? doms s = none) :
    ofSlots doms slots = none := by
  induction slots with
  | nil => simp at hs
  | cons t ts ih =>
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp [ofSlots, hm]
      · simp only [ofSlots]
        cases hmt : BArg.mk? doms t with
        | none => rfl
        | some a =>
            simp only [ih hs]

/-- Duplicate operand slots are rejected: a batch that treats two
positions independently would otherwise be able to prune both values of
one domain. -/
def hasDupSlot : List BArg → Bool
  | [] => false
  | a :: as => as.any (fun b => b.slot == a.slot) || hasDupSlot as

end BArgs

/-! ## Truth-table support -/

namespace BArgs

/-- Membership in the enumerator, in terms of the current box. -/
theorem mem_enum_iff {args : List BArg} {vs : List Bool} :
    vs ∈ enum args ↔ vs.length = args.length ∧ curVec args vs = true := by
  induction args generalizing vs with
  | nil =>
      cases vs <;> simp [enum, curVec]
  | cons a as ih =>
      cases vs with
      | nil => simp [enum]
      | cons v tl =>
          by_cases hf : a.curF
          · by_cases ht : a.curT
            · cases v <;>
                simp [enum, hf, ht, List.mem_append, ih, curVec, BArg.cur]
            · cases v <;>
                simp [enum, hf, ht, List.mem_append, ih, curVec, BArg.cur]
          · by_cases ht : a.curT
            · cases v <;>
                simp [enum, hf, ht, List.mem_append, ih, curVec, BArg.cur]
            · cases v <;>
                simp [enum, hf, ht, List.mem_append, ih, curVec, BArg.cur]

/-- Is there a satisfying tuple in the current box with value `v` at
position `pos`? -/
def hasSupport (R : List Bool → Bool) (args : List BArg) (pos : Nat) (v : Bool) : Bool :=
  (enum args).any (fun vs => (vs.getD pos false == v) && R vs)

/-- Is there any satisfying tuple in the current box? -/
def hasAnySupport (R : List Bool → Bool) (args : List BArg) : Bool :=
  (enum args).any R

theorem hasSupport_true {R : List Bool → Bool} {args : List BArg} {pos : Nat} {v : Bool}
    (h : hasSupport R args pos v = true) :
    ∃ vs ∈ enum args, vs.getD pos false = v ∧ R vs = true := by
  unfold hasSupport at h
  obtain ⟨vs, hvs, hb⟩ := List.any_eq_true.mp h
  have hb' : (vs.getD pos false == v) = true ∧ R vs = true := by
    simpa only [Bool.and_eq_true] using hb
  exact ⟨vs, hvs, beq_iff_eq.mp hb'.1, hb'.2⟩

theorem hasAnySupport_false {R : List Bool → Bool} {args : List BArg}
    (h : hasAnySupport R args = false) :
    ∀ vs ∈ enum args, R vs = false := by
  intro vs hvs
  have h' := List.any_eq_false.mp h vs hvs
  simpa using h'

theorem hasSupport_false {R : List Bool → Bool} {args : List BArg}
    {pos : Nat} {v : Bool} (h : hasSupport R args pos v = false) :
    ∀ vs ∈ enum args, ((vs.getD pos false == v) && R vs) = false := by
  intro vs hvs
  have h' := List.any_eq_false.mp h vs hvs
  simpa using h'

theorem valsOf_length (b : Assignment) (args : List BArg) :
    (valsOf b args).length = args.length := by
  simp [valsOf]

theorem valsOf_getD {b : Assignment} {args : List BArg} {p : Nat}
    (hp : p < args.length) :
    (valsOf b args).getD p false = (args.getD p default).valAt b := by
  unfold valsOf
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map]
  cases h : args[p]? with
  | none =>
      rw [List.getElem?_eq_getElem hp] at h
      cases h
  | some a =>
      simp [h]

theorem getD_mem {args : List BArg} {p : Nat} (hp : p < args.length) :
    args.getD p default ∈ args := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  exact List.getElem_mem hp

/-- Every literal of `fixedLits` is one of the two `posBool` pins of an
operand. -/
theorem mem_fixedLits {args : List BArg} {l : Literal}
    (h : l ∈ fixedLits args) :
    ∃ a ∈ args, l = posBool a.slot true ∨ l = posBool a.slot false := by
  induction args with
  | nil => simp [fixedLits] at h
  | cons a as ih =>
      simp only [fixedLits, List.mem_append] at h
      rcases h with h | h
      · by_cases hf : a.curF
        · by_cases ht : a.curT
          · simp [BArg.fixedLit, BArg.fixedLit?, hf, ht] at h
          · simp [BArg.fixedLit, BArg.fixedLit?, hf, ht] at h
            subst h
            exact ⟨a, by simp, Or.inl rfl⟩
        · by_cases ht : a.curT
          · simp [BArg.fixedLit, BArg.fixedLit?, hf, ht] at h
            subst h
            exact ⟨a, by simp, Or.inr rfl⟩
          · simp [BArg.fixedLit, BArg.fixedLit?, hf, ht] at h
      · obtain ⟨a', ha', h'⟩ := ih h
        exact ⟨a', by simp [ha'], h'⟩

end BArgs

namespace BArg

/-- Turn failure of truth for a Boolean pin into falsity on a slot known
to carry a Boolean value. -/
theorem eval_posBool_eq_false_of_not_true {b : Assignment} {s : Nat} {x : Bool}
    (hbool : ∃ v, b[s]? = some (.bool v))
    (h : (posBool s x).eval b ≠ some true) :
    (posBool s x).eval b = some false := by
  obtain ⟨v, hv⟩ := hbool
  have hne : v ≠ x := by
    intro hveq
    apply h
    rw [eval_posBool_iff]
    simpa [hveq] using hv
  rw [eval_posBool_false_iff]
  exact ⟨v, hv, hne⟩

end BArg

namespace BArgs

theorem fixedLits_false_of_not_true {args : List BArg} {b : Assignment}
    (hbool : ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (hnot : ∀ l ∈ fixedLits args, l.eval b ≠ some true) :
    ∀ l ∈ fixedLits args, l.eval b = some false := by
  intro l hl
  obtain ⟨a, ha, rfl | rfl⟩ := mem_fixedLits hl
  · exact BArg.eval_posBool_eq_false_of_not_true (hbool a ha) (hnot _ hl)
  · exact BArg.eval_posBool_eq_false_of_not_true (hbool a ha) (hnot _ hl)

end BArgs

namespace BArg

/-- `valAt` is true exactly when the slot carries Boolean `true`. -/
theorem valAt_eq_true_iff {a : BArg} {b : Assignment} :
    a.valAt b = true ↔ b[a.slot]? = some (.bool true) := by
  unfold valAt
  cases h : b[a.slot]? with
  | none => simp
  | some v =>
      cases v with
      | bool x => cases x <;> simp [h]
      | int x => simp [h]
      | setOfInt x => simp [h]
      | array x => simp [h]

/-- The Boolean reading of an operand is the actual value when the slot
carries a Boolean. -/
theorem valAt_eq_of_some_bool {a : BArg} {b : Assignment} {v : Bool}
    (h : b[a.slot]? = some (.bool v)) : a.valAt b = v := by
  unfold valAt
  rw [h]

/-- The Boolean reading of an operand is exactly the executable
`slotIsBoolB` test used by `array_bool_and`: non-Boolean and missing
values both read as `false`. -/
theorem valAt_eq_slotIsBoolB (a : BArg) (b : Assignment) :
    a.valAt b = slotIsBoolB b a.slot true := by
  unfold valAt slotIsBoolB
  cases h : b[a.slot]? with
  | none => rfl
  | some v =>
      cases v with
      | bool x => cases x <;> rfl
      | int x => rfl
      | setOfInt x => rfl
      | array x => rfl

/-- Every literal in an operand's fixed facts pins that operand's slot. -/
theorem slot_of_mem_fixedLit {a : BArg} {l : Literal}
    (h : l ∈ a.fixedLit) : l.atom.slot = a.slot := by
  unfold BArg.fixedLit at h
  cases hf : a.fixedLit? with
  | none => rw [hf] at h; simp at h
  | some x =>
      rw [hf, Option.toList_some] at h
      simp only [List.mem_singleton] at h
      subst h
      unfold BArg.fixedLit? at hf
      split at hf
      · injection hf with hx
        subst hx
        rfl
      · split at hf
        · injection hf with hx
          subst hx
          rfl
        · cases hf

/-- A current operand containing `false` keeps `false` on a Boolean
assignment whose fixed facts are false. -/
theorem cur_false_of_fixedLits_false {a : BArg} {b : Assignment}
    (ha : a.curF = true ∨ a.curT = true)
    (hb : b[a.slot]? = some (.bool false))
    (hfalse : ∀ l ∈ a.fixedLit, l.eval b = some false) :
    a.cur false = true := by
  simp only [BArg.cur, Bool.false_eq_true, ↓reduceIte]
  by_cases hf : a.curF = true
  · exact hf
  · have ht : a.curT = true := by
      rcases ha with h | h
      · exact absurd h hf
      · exact h
    have hl : posBool a.slot false ∈ a.fixedLit := by
      simp [BArg.fixedLit, BArg.fixedLit?, hf, ht]
    have hff := hfalse _ hl
    rw [eval_posBool_false_iff] at hff
    obtain ⟨x, hx, hne⟩ := hff
    rw [hb] at hx
    injection hx with hx
    cases hx
    exact absurd rfl hne

/-- A current operand containing `true` keeps `true` on a Boolean
assignment whose fixed facts are false. -/
theorem cur_true_of_fixedLits_false {a : BArg} {b : Assignment}
    (ha : a.curF = true ∨ a.curT = true)
    (hb : b[a.slot]? = some (.bool true))
    (hfalse : ∀ l ∈ a.fixedLit, l.eval b = some false) :
    a.cur true = true := by
  simp only [BArg.cur, ↓reduceIte]
  by_cases ht : a.curT = true
  · exact ht
  · have hf : a.curF = true := by
      rcases ha with h | h
      · exact h
      · exact absurd h ht
    have hl : posBool a.slot true ∈ a.fixedLit := by
      simp [BArg.fixedLit, BArg.fixedLit?, hf, ht]
    have hff := hfalse _ hl
    rw [eval_posBool_false_iff] at hff
    obtain ⟨x, hx, hne⟩ := hff
    rw [hb] at hx
    injection hx with hx
    cases hx
    exact absurd rfl hne

/-- A false fixed fact determines the Boolean value of the operand. -/
theorem valAt_of_fixed_false {a : BArg} {b : Assignment}
    (hf : a.curF = true) (ht : a.curT = false)
    (hfalse : ∀ l ∈ a.fixedLit, l.eval b = some false) :
    a.valAt b = false := by
  have hl : posBool a.slot true ∈ a.fixedLit := by
    simp [BArg.fixedLit, BArg.fixedLit?, hf, ht]
  have hff := hfalse _ hl
  rw [eval_posBool_false_iff] at hff
  obtain ⟨x, hx, hne⟩ := hff
  have hx' : x = false := by cases x <;> simp_all
  subst hx'
  simp [BArg.valAt, hx]

/-- A false fixed fact determines the Boolean value of the operand. -/
theorem valAt_of_fixed_true {a : BArg} {b : Assignment}
    (hf : a.curF = false) (ht : a.curT = true)
    (hfalse : ∀ l ∈ a.fixedLit, l.eval b = some false) :
    a.valAt b = true := by
  have hl : posBool a.slot false ∈ a.fixedLit := by
    simp [BArg.fixedLit, BArg.fixedLit?, hf, ht]
  have hff := hfalse _ hl
  rw [eval_posBool_false_iff] at hff
  obtain ⟨x, hx, hne⟩ := hff
  have hx' : x = true := by cases x <;> simp_all
  subst hx'
  simp [BArg.valAt, hx]

/-- Every current value of an operand stays current when all fixed facts
are false: fixed operands are forced to their remaining value, and full
operands contain both values. -/
theorem cur_valAt_of_fixedLits_false {a : BArg} {b : Assignment}
    (ha : a.curF = true ∨ a.curT = true)
    (hfalse : ∀ l ∈ a.fixedLit, l.eval b = some false) :
    a.cur (a.valAt b) = true := by
  by_cases hf : a.curF = true
  · by_cases ht : a.curT = true
    · simp [BArg.cur, hf, ht]
    · have ht' : a.curT = false := by simpa using ht
      have hv := valAt_of_fixed_false hf ht' hfalse
      rw [hv]
      simp [BArg.cur, hf]
  · have hf' : a.curF = false := by simpa using hf
    have ht : a.curT = true := by
      rcases ha with h | h
      · exact absurd h hf
      · exact h
    have hv := valAt_of_fixed_true hf' ht hfalse
    rw [hv]
    simp [BArg.cur, ht]

end BArg

namespace BArgs

/-- If all fixed facts are false, the assignment's Boolean tuple lies in
the current box.  No hypothesis on the assignment is needed beyond the
false fixed facts: those already force the corresponding Boolean
values. -/
theorem curVec_valsOf_of_fixedLits_false {args : List BArg} {b : Assignment}
    (hcur : AllCur args)
    (hfalse : ∀ l ∈ fixedLits args, l.eval b = some false) :
    curVec args (valsOf b args) = true := by
  induction args with
  | nil => simp [curVec, valsOf]
  | cons a as ih =>
      simp only [curVec, valsOf, List.map_cons]
      have ha : a.curF = true ∨ a.curT = true := hcur a (by simp)
      have hfalsea : ∀ l ∈ a.fixedLit, l.eval b = some false := by
        intro l hl
        exact hfalse l (by simp [fixedLits, hl])
      rw [BArg.cur_valAt_of_fixedLits_false ha hfalsea]
      simp only [Bool.true_and]
      exact ih
        (fun x hx => hcur x (by simp [hx]))
        (fun l hl => hfalse l (by simp [fixedLits, hl]))

end BArgs

/-! ## Support plans and their output -/

/-- One proposed value removal with its decoded reason.  `pos` is the
operand position in the plan's argument list. -/
structure BPrune where
  pos : Nat
  slot : Nat
  val : Bool
  lit : Literal
  reason : Clause

/-- A view-independent Boolean propagation plan. -/
structure BPlan where
  conflict? : Option (List Literal)
  prunes : List BPrune

namespace BArgs

/-- Remove every current value with no satisfying completion. -/
def mkPrunes (R : List Bool → Bool) (args : List BArg) : List BPrune :=
  (List.range args.length).flatMap fun p =>
    let a := args.getD p default
    (if a.curF && !hasSupport R args p false then
      [{ pos := p, slot := a.slot, val := false,
         lit := posBool a.slot true,
         reason := posBool a.slot true :: fixedLits args }]
     else []) ++
    (if a.curT && !hasSupport R args p true then
      [{ pos := p, slot := a.slot, val := true,
         lit := posBool a.slot false,
         reason := posBool a.slot false :: fixedLits args }]
     else [])

/-- Conflict when there is no satisfying tuple, otherwise prune every
unsupported current Boolean value. -/
def mkPlan (R : List Bool → Bool) (args : List BArg) : BPlan :=
  if hasAnySupport R args then
    { conflict? := none, prunes := mkPrunes R args }
  else
    { conflict? := some (fixedLits args), prunes := [] }

/-- Every entry of `mkPrunes` arose from a position and one of the two
current values, with the exact reason shape. -/
theorem mem_mkPrunes {R : List Bool → Bool} {args : List BArg} {bp : BPrune}
    (h : bp ∈ mkPrunes R args) :
    (∃ p, p < args.length ∧ (args.getD p default).curF = true ∧
      hasSupport R args p false = false ∧
      bp = { pos := p, slot := (args.getD p default).slot, val := false,
             lit := posBool (args.getD p default).slot true,
             reason := posBool (args.getD p default).slot true :: fixedLits args }) ∨
    (∃ p, p < args.length ∧ (args.getD p default).curT = true ∧
      hasSupport R args p true = false ∧
      bp = { pos := p, slot := (args.getD p default).slot, val := true,
             lit := posBool (args.getD p default).slot false,
             reason := posBool (args.getD p default).slot false :: fixedLits args }) := by
  unfold mkPrunes at h
  rw [List.mem_flatMap] at h
  obtain ⟨p, hp, hbp⟩ := h
  rw [List.mem_range] at hp
  simp only [List.mem_append] at hbp
  rcases hbp with hbp | hbp
  · by_cases hf : ((args.getD p default).curF && !hasSupport R args p false) = true
    · have hf2 : (args.getD p default).curF = true ∧
          (!hasSupport R args p false) = true := by
        simpa only [Bool.and_eq_true] using hf
      rw [if_pos hf] at hbp
      simp only [List.mem_singleton] at hbp
      subst bp
      exact Or.inl ⟨p, hp, hf2.1, by simpa using hf2.2, rfl⟩
    · rw [if_neg hf] at hbp
      simp at hbp
  · by_cases ht : ((args.getD p default).curT && !hasSupport R args p true) = true
    · have ht2 : (args.getD p default).curT = true ∧
          (!hasSupport R args p true) = true := by
        simpa only [Bool.and_eq_true] using ht
      rw [if_pos ht] at hbp
      simp only [List.mem_singleton] at hbp
      subst bp
      exact Or.inr ⟨p, hp, ht2.1, by simpa using ht2.2, rfl⟩
    · rw [if_neg ht] at hbp
      simp at hbp

/-- The conflict clause of a support plan is entailed whenever every
accepted assignment satisfies the relation and reads Boolean values at
all operands. -/
theorem mkPlan_conflict_entailed (p : CompiledProblem DomConstraint)
    (R : List Bool → Bool) (args : List BArg) (ls : List Literal)
    (hR : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      R (valsOf b args) = true)
    (hbool : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (hcur : AllCur args)
    (hls : (mkPlan R args).conflict? = some ls) :
    Entailed p ls := by
  intro b hb hacc
  by_cases hany : hasAnySupport R args = true
  · simp [mkPlan, hany] at hls
  · have hls' : fixedLits args = ls := by simpa [mkPlan, hany] using hls
    subst hls'
    by_cases hsat : Clause.SatisfiedBy (fixedLits args) b
    · exact hsat
    · exfalso
      have hnot : ∀ l ∈ fixedLits args, l.eval b ≠ some true := by
        intro l hl ht
        exact hsat ⟨l, hl, ht⟩
      have hfalse := fixedLits_false_of_not_true (hbool b hb hacc) hnot
      have hcv := curVec_valsOf_of_fixedLits_false hcur hfalse
      have hmem : valsOf b args ∈ enum args :=
        mem_enum_iff.mpr ⟨valsOf_length b args, hcv⟩
      have hanyf : hasAnySupport R args = false := by simpa using hany
      have hr := hR b hb hacc
      have hf := hasAnySupport_false hanyf _ hmem
      rw [hr] at hf
      exact Bool.noConfusion hf

/-- Every reason produced by `mkPrunes` is entailed under the same
relation and Boolean-value hypotheses. -/
theorem mkPrunes_reason_entailed (p : CompiledProblem DomConstraint)
    (R : List Bool → Bool) (args : List BArg)
    (hR : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      R (valsOf b args) = true)
    (hbool : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (hcur : AllCur args) {bp : BPrune}
    (hbp : bp ∈ mkPrunes R args) :
    Entailed p bp.reason := by
  intro b hb hacc
  by_cases hsat : Clause.SatisfiedBy bp.reason b
  · exact hsat
  · exfalso
    have hr := hR b hb hacc
    rcases mem_mkPrunes hbp with
      ⟨pos, hpos, _hcurF, hsupp, rfl⟩ |
      ⟨pos, hpos, _hcurT, hsupp, rfl⟩
    · have hhead : (posBool (args.getD pos default).slot true).eval b ≠ some true := by
        intro ht
        exact hsat ⟨_, List.mem_cons_self, ht⟩
      have htail : ∀ l ∈ fixedLits args, l.eval b ≠ some true := by
        intro l hl ht
        exact hsat ⟨l, List.mem_cons_of_mem _ hl, ht⟩
      have hbarg : ∃ v, b[(args.getD pos default).slot]? = some (.bool v) :=
        hbool b hb hacc _ (getD_mem hpos)
      have hheadf := BArg.eval_posBool_eq_false_of_not_true hbarg hhead
      rw [eval_posBool_false_iff] at hheadf
      obtain ⟨x, hx, hne⟩ := hheadf
      have hx' : x = false := by cases x <;> simp_all
      subst hx'
      have hfalse := fixedLits_false_of_not_true (hbool b hb hacc) htail
      have hcv := curVec_valsOf_of_fixedLits_false hcur hfalse
      have hmem : valsOf b args ∈ enum args :=
        mem_enum_iff.mpr ⟨valsOf_length b args, hcv⟩
      have hx' : b[(args[pos]?.getD default).slot]? = some (.bool false) := by
        simpa [List.getD_eq_getElem?_getD] using hx
      have hget : (valsOf b args).getD pos false = false := by
        rw [valsOf_getD hpos]
        simp [BArg.valAt, List.getD_eq_getElem?_getD, hx']
      have hb1 : ((valsOf b args).getD pos false == false) = true := by
        rw [hget]
        simp
      have hbad := hasSupport_false hsupp _ hmem
      rw [hb1, hr] at hbad
      exact Bool.noConfusion hbad
    · have hhead : (posBool (args.getD pos default).slot false).eval b ≠ some true := by
        intro ht
        exact hsat ⟨_, List.mem_cons_self, ht⟩
      have htail : ∀ l ∈ fixedLits args, l.eval b ≠ some true := by
        intro l hl ht
        exact hsat ⟨l, List.mem_cons_of_mem _ hl, ht⟩
      have hbarg : ∃ v, b[(args.getD pos default).slot]? = some (.bool v) :=
        hbool b hb hacc _ (getD_mem hpos)
      have hheadf := BArg.eval_posBool_eq_false_of_not_true hbarg hhead
      rw [eval_posBool_false_iff] at hheadf
      obtain ⟨x, hx, hne⟩ := hheadf
      have hx' : x = true := by cases x <;> simp_all
      subst hx'
      have hfalse := fixedLits_false_of_not_true (hbool b hb hacc) htail
      have hcv := curVec_valsOf_of_fixedLits_false hcur hfalse
      have hmem : valsOf b args ∈ enum args :=
        mem_enum_iff.mpr ⟨valsOf_length b args, hcv⟩
      have hx' : b[(args[pos]?.getD default).slot]? = some (.bool true) := by
        simpa [List.getD_eq_getElem?_getD] using hx
      have hget : (valsOf b args).getD pos false = true := by
        rw [valsOf_getD hpos]
        simp [BArg.valAt, List.getD_eq_getElem?_getD, hx']
      have hb1 : ((valsOf b args).getD pos false == true) = true := by
        rw [hget]
        simp
      have hbad := hasSupport_false hsupp _ hmem
      rw [hb1, hr] at hbad
      exact Bool.noConfusion hbad

/-- Every prune reason in `mkPlan` is entailed. -/
theorem mkPlan_prunes_entailed (p : CompiledProblem DomConstraint)
    (R : List Bool → Bool) (args : List BArg)
    (hR : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      R (valsOf b args) = true)
    (hbool : ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (hcur : AllCur args) {q : BPrune}
    (hq : q ∈ (mkPlan R args).prunes) :
    Entailed p q.reason := by
  by_cases hany : hasAnySupport R args = true
  · exact mkPrunes_reason_entailed p R args hR hbool hcur
      (by simpa [mkPlan, hany] using hq)
  · simp [mkPlan, hany] at hq

end BArgs

namespace BPlan

/-- Turn a support plan into a `PropOut`, attaching the supplied
entailment proofs for the conflict clause and every prune reason. -/
def out (p : CompiledProblem DomConstraint) (T : LitTable) (plan : BPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ q ∈ plan.prunes, Entailed p q.reason) : PropOut p T :=
  match hc : plan.conflict? with
  | some ls => .conflict (EClause.ofLiterals p T ls (hconf ls hc))
  | none =>
      match _hp : plan.prunes with
      | [] => .fix
      | _ :: _ =>
          .prune ((plan.prunes.attach.map fun q =>
            (pLit q.1.lit,
              EClause.ofLiterals p T q.1.reason
                (hprune q.1 q.2))).toArray)

theorem out_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : BPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ q ∈ plan.prunes, Entailed p q.reason)
    {ec : EClause p T}
    (h : plan.out p T hconf hprune = .conflict ec) :
    ∃ ls, plan.conflict? = some ls ∧ T.decodeClause ec.lits = ls ∧
      Entailed p ls := by
  unfold BPlan.out at h
  split at h
  · rename_i ls hls
    injection h with hec
    subst hec
    exact ⟨ls, hls, LitTable.decodeClause_map_pLit T ls, hconf ls hls⟩
  · split at h <;> cases h

theorem out_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : BPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ q ∈ plan.prunes, Entailed p q.reason)
    {ps : Array (PLit × EClause p T)}
    (h : plan.out p T hconf hprune = .prune ps) :
    plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          Entailed p q'.reason) := by
  unfold BPlan.out at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i ps0 hps0
      injection h with hps
      subst hps
      refine ⟨hc, by simp [hps0], ?_⟩
      intro q hq
      rw [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      refine ⟨y.1, y.2, rfl, ?_, ?_⟩
      · change T.decodeClause (Array.map pLit y.1.reason.toArray) = y.1.reason
        exact LitTable.decodeClause_map_pLit T y.1.reason
      · exact hprune y.1 y.2

theorem out_run_fix_of_no_prunes (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : BPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ q ∈ plan.prunes, Entailed p q.reason)
    (hc : plan.conflict? = none) (hp : plan.prunes = []) :
    plan.out p T hconf hprune = .fix := by
  unfold BPlan.out
  split
  · rename_i ls hls
    rw [hc] at hls
    cases hls
  · split
    · rfl
    · rename_i ps0 hps0
      rw [hp] at hps0
      cases hps0

end BPlan

/-! ## Fixed-arity operand shapes and relation specifications -/

namespace BArgs

/-- The two operands of a binary constraint. -/
theorem ofSlots_two {doms : Array DomC} {i j : Nat} {args : List BArg}
    (h : ofSlots doms [i, j] = some args) :
    ∃ a b, args = [a, b] ∧ a.slot = i ∧ b.slot = j := by
  have hmap := ofSlots_map_slot h
  have hlen : args.length = 2 := by
    have := congrArg List.length hmap
    simpa using this
  cases args with
  | nil => simp at hlen
  | cons a as =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
          cases bs with
          | nil =>
              have h1 : a.slot = i := by
                have := congrArg (fun l : List Nat => l[0]?) hmap
                simpa using this
              have h2 : b.slot = j := by
                have := congrArg (fun l : List Nat => l[1]?) hmap
                simpa using this
              exact ⟨a, b, rfl, h1, h2⟩
          | cons c cs => simp at hlen

/-- The three operands of a ternary constraint. -/
theorem ofSlots_three {doms : Array DomC} {i j k : Nat} {args : List BArg}
    (h : ofSlots doms [i, j, k] = some args) :
    ∃ a b c, args = [a, b, c] ∧ a.slot = i ∧ b.slot = j ∧ c.slot = k := by
  have hmap := ofSlots_map_slot h
  have hlen : args.length = 3 := by
    have := congrArg List.length hmap
    simpa using this
  cases args with
  | nil => simp at hlen
  | cons a as =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
          cases bs with
          | nil => simp at hlen
          | cons c cs =>
              cases cs with
              | nil =>
                  have h1 : a.slot = i := by
                    have := congrArg (fun l : List Nat => l[0]?) hmap
                    simpa using this
                  have h2 : b.slot = j := by
                    have := congrArg (fun l : List Nat => l[1]?) hmap
                    simpa using this
                  have h3 : c.slot = k := by
                    have := congrArg (fun l : List Nat => l[2]?) hmap
                    simpa using this
                  exact ⟨a, b, c, rfl, h1, h2, h3⟩
              | cons d ds => simp at hlen

/-- The array operand list splits into the sources and the single result
slot. -/
theorem ofSlots_array : ∀ (is : List Nat) {k : Nat} {args : List BArg}
    {doms : Array DomC}, ofSlots doms (is ++ [k]) = some args →
      ∃ src ak, args = src ++ [ak] ∧ src.map BArg.slot = is ∧ ak.slot = k := by
  intro is
  induction is with
  | nil =>
      intro k args doms h
      simp only [List.nil_append] at h
      cases ha : BArg.mk? doms k with
      | none => simp [ofSlots, ha] at h
      | some ak =>
          have hargs : args = [ak] := by simpa [ofSlots, ha] using h.symm
          subst hargs
          exact ⟨[], ak, rfl, rfl, BArg.ofDom?_slot ha⟩
  | cons s ss ih =>
      intro k args doms h
      simp only [List.cons_append] at h
      cases ha : BArg.mk? doms s with
      | none => simp [ofSlots, ha] at h
      | some a =>
          cases hr : ofSlots doms (ss ++ [k]) with
          | none => simp [ofSlots, ha, hr] at h
          | some rest =>
              have hargs : args = a :: rest := by
                simpa [ofSlots, ha, hr] using h.symm
              subst hargs
              obtain ⟨src, ak, rfl, hmap, hk⟩ := ih hr
              exact ⟨a :: src, ak, rfl,
                by simp [BArg.ofDom?_slot ha, hmap], hk⟩

/-- A full plan computation: no operands for malformed views or duplicate
operand slots, otherwise the support plan. -/
def planOf (R : List Bool → Bool) (slots : List Nat) (doms : Array DomC) :
    Option (List BArg × BPlan) :=
  match ofSlots doms slots with
  | none => none
  | some args =>
      if hasDupSlot args then none else some (args, mkPlan R args)

theorem planOf_some {R : List Bool → Bool} {slots : List Nat}
    {doms : Array DomC} {args : List BArg} {plan : BPlan}
    (h : planOf R slots doms = some (args, plan)) :
    ofSlots doms slots = some args ∧ hasDupSlot args = false ∧
      plan = mkPlan R args := by
  unfold planOf at h
  cases hf : ofSlots doms slots with
  | none => rw [hf] at h; cases h
  | some args0 =>
      rw [hf] at h
      change (if hasDupSlot args0 = true then none
        else some (args0, mkPlan R args0)) = some (args, plan) at h
      by_cases hd : hasDupSlot args0 = true
      · rw [if_pos hd] at h; cases h
      · rw [if_neg hd] at h
        injection h with hpair
        injection hpair with hargs hpl
        subst hargs
        subst hpl
        exact ⟨rfl, by simpa using hd, rfl⟩

/-- A non-conflicting plan is exactly the support-prune list. -/
theorem planOf_prunes_eq {R : List Bool → Bool} {slots : List Nat}
    {doms : Array DomC} {args : List BArg} {plan : BPlan}
    (h : planOf R slots doms = some (args, plan))
    (hc : plan.conflict? = none) :
    plan.prunes = mkPrunes R args := by
  obtain ⟨_hargs, _hdup, rfl⟩ := planOf_some h
  unfold mkPlan at hc ⊢
  by_cases hany : hasAnySupport R args = true
  · simp [hany]
  · simp [hany] at hc

end BArgs

/-- Relation of `bool_not`: the second operand is the negation of the
first. -/
def boolNotR (vs : List Bool) : Bool :=
  vs.getD 1 false == !(vs.getD 0 false)

/-- Relation of `bool_and`: the third operand is the conjunction of the
first two. -/
def boolAndR (vs : List Bool) : Bool :=
  vs.getD 2 false == (vs.getD 0 false && vs.getD 1 false)

/-- Relation of `bool_or`: the third operand is the disjunction of the
first two. -/
def boolOrR (vs : List Bool) : Bool :=
  vs.getD 2 false == (vs.getD 0 false || vs.getD 1 false)

/-- Relation of `bool_eq`: the two operands agree. -/
def boolEqR (vs : List Bool) : Bool :=
  vs.getD 0 false == vs.getD 1 false

/-- Relation of `array_bool_and`: the last operand is the conjunction of
the first `n` operands.  The `take` formulation avoids index arithmetic in
the soundness proof. -/
def arrayBoolAndR (n : Nat) (vs : List Bool) : Bool :=
  vs.getD n false == (vs.take n).all id

/-- `getD` of the appended last element at its own index. -/
theorem getD_append_singleton_self (vs : List Bool) (x : Bool) :
    (vs ++ [x]).getD vs.length false = x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.cons_append, List.length_cons, List.getD_cons_succ]
      exact ih

namespace BArgs

/-- Runtime guard: the initial compiled domain of a slot is a Boolean
domain.  `array_bool_and` sources need this because the leaf semantics
treats a non-Boolean source as `false`, while the Boolean support box only
describes Boolean values. -/
def initBoolB (p : CompiledProblem DomConstraint) (s : Nat) : Bool :=
  match DomC.ofDom? (p.domains.getD s Dom.empty) with
  | some (.bool _) => true
  | _ => false

theorem initBoolB_some {p : CompiledProblem DomConstraint} {s : Nat}
    (h : initBoolB p s = true) :
    ∃ bits, DomC.ofDom? (p.domains.getD s Dom.empty) = some (.bool bits) := by
  unfold initBoolB at h
  rw [List.getD_eq_getElem?_getD] at h
  cases hd : p.domains[s]? with
  | none =>
      have hget : (p.domains[s]?).getD Dom.empty = Dom.empty := by simp [hd]
      rw [hget] at h
      rw [DomC.ofDom?_empty] at h
      simp at h
  | some d =>
      have hget : (p.domains[s]?).getD Dom.empty = d := by simp [hd]
      rw [hget] at h
      cases hc : DomC.ofDom? d with
      | none => simp [hc] at h
      | some c =>
          cases c with
          | bool bits =>
              refine ⟨bits, ?_⟩
              rw [List.getD_eq_getElem?_getD, hget]
              exact hc
          | bounds lo hi => simp [hc] at h
          | bitset lo words => simp [hc] at h
          | boundsHoles lo hi holes => simp [hc] at h
          | sparse values => simp [hc] at h

theorem exists_bool_of_mem_bool {bits : UInt8} {v : Value}
    (h : (DomC.bool bits).mem v = true) : ∃ b, v = .bool b := by
  cases v <;> simp [DomC.mem] at h ⊢

/-- A Boolean initial domain forces a Boolean value at that slot in every
enumerated assignment. -/
theorem mem_getD_bool_of_init {p : CompiledProblem DomConstraint}
    {b : Assignment} {s : Nat} {bits : UInt8}
    (hb : b ∈ allAssigns p.domains)
    (hconv : DomC.ofDom? (p.domains.getD s Dom.empty) = some (.bool bits)) :
    ∃ v, b[s]? = some (.bool v) := by
  have hfit := allAssigns_fits_dom p.domains b hb
  have hslt : s < p.domains.length := by
    apply Nat.lt_of_not_le
    intro hle
    have hnone : p.domains[s]? = none := List.getElem?_eq_none hle
    rw [List.getD_eq_getElem?_getD, hnone] at hconv
    change DomC.ofDom? Dom.empty = some (.bool bits) at hconv
    rw [DomC.ofDom?_empty] at hconv
    cases hconv
  have hsblt : s < b.length := by rw [hfit.1]; exact hslt
  obtain ⟨v, hv⟩ : ∃ v, b[s]? = some v := ⟨b[s], List.getElem?_eq_getElem hsblt⟩
  have hvdom : v ∈ p.domains.getD s Dom.empty := hfit.2 s v hv
  have hmem : (DomC.bool bits).mem v = true :=
    (DomC.mem_iff _ _ hconv v).mpr hvdom
  obtain ⟨bv, rfl⟩ := exists_bool_of_mem_bool hmem
  exact ⟨bv, hv⟩

/-- Every accepted assignment reads the operands of `bool_not` as Boolean
and satisfies the truth-table relation. -/
theorem boolNotR_spec (p : CompiledProblem DomConstraint) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints)
    (doms : Array DomC) (args : List BArg)
    (hargs : ofSlots doms [i, j] = some args) :
    ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      boolNotR (valsOf b args) = true ∧
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v) := by
  intro b hb hacc
  obtain ⟨a1, a2, rfl, hs1, hs2⟩ := ofSlots_two hargs
  have hsat : (DomConstraint.boolNotSlot i j).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, y, hbi, hbj, hxy⟩ := (DomConstraint.satisfiedB_iff _ _).mp hsat
  have hbi1 : b[a1.slot]? = some x := by rwa [hs1]
  have hbj2 : b[a2.slot]? = some y := by rwa [hs2]
  constructor
  · rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x; subst y
      have hv1 : a1.valAt b = true := BArg.valAt_eq_of_some_bool hbi1
      have hv2 : a2.valAt b = false := BArg.valAt_eq_of_some_bool hbj2
      simp [valsOf, boolNotR, hv1, hv2]
    · subst x; subst y
      have hv1 : a1.valAt b = false := BArg.valAt_eq_of_some_bool hbi1
      have hv2 : a2.valAt b = true := BArg.valAt_eq_of_some_bool hbj2
      simp [valsOf, boolNotR, hv1, hv2]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x; subst y
      rcases ha with rfl | rfl
      · exact ⟨true, by rwa [hs1]⟩
      · exact ⟨false, by rwa [hs2]⟩
    · subst x; subst y
      rcases ha with rfl | rfl
      · exact ⟨false, by rwa [hs1]⟩
      · exact ⟨true, by rwa [hs2]⟩

/-- Every accepted assignment reads the operands of `bool_and` as Boolean
and satisfies the truth-table relation. -/
theorem boolAndR_spec (p : CompiledProblem DomConstraint) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints)
    (doms : Array DomC) (args : List BArg)
    (hargs : ofSlots doms [i, j, k] = some args) :
    ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      boolAndR (valsOf b args) = true ∧
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v) := by
  intro b hb hacc
  obtain ⟨a1, a2, a3, rfl, hs1, hs2, hs3⟩ := ofSlots_three hargs
  have hsat : (DomConstraint.boolAndSlot i j k).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, y, z, hbi, hbj, hbk, hrel⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hsat
  have hbi1 : b[a1.slot]? = some (.bool x) := by rwa [hs1]
  have hbj2 : b[a2.slot]? = some (.bool y) := by rwa [hs2]
  have hbk3 : b[a3.slot]? = some (.bool z) := by rwa [hs3]
  constructor
  · have hv1 : a1.valAt b = x := BArg.valAt_eq_of_some_bool hbi1
    have hv2 : a2.valAt b = y := BArg.valAt_eq_of_some_bool hbj2
    have hv3 : a3.valAt b = z := BArg.valAt_eq_of_some_bool hbk3
    simp [valsOf, boolAndR, hv1, hv2, hv3, hrel]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨x, hbi1⟩
    · exact ⟨y, hbj2⟩
    · exact ⟨z, hbk3⟩

/-- Every accepted assignment reads the operands of `bool_or` as Boolean
and satisfies the truth-table relation. -/
theorem boolOrR_spec (p : CompiledProblem DomConstraint) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints)
    (doms : Array DomC) (args : List BArg)
    (hargs : ofSlots doms [i, j, k] = some args) :
    ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      boolOrR (valsOf b args) = true ∧
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v) := by
  intro b hb hacc
  obtain ⟨a1, a2, a3, rfl, hs1, hs2, hs3⟩ := ofSlots_three hargs
  have hsat : (DomConstraint.boolOrSlot i j k).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, y, z, hbi, hbj, hbk, hrel⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hsat
  have hbi1 : b[a1.slot]? = some (.bool x) := by rwa [hs1]
  have hbj2 : b[a2.slot]? = some (.bool y) := by rwa [hs2]
  have hbk3 : b[a3.slot]? = some (.bool z) := by rwa [hs3]
  constructor
  · have hv1 : a1.valAt b = x := BArg.valAt_eq_of_some_bool hbi1
    have hv2 : a2.valAt b = y := BArg.valAt_eq_of_some_bool hbj2
    have hv3 : a3.valAt b = z := BArg.valAt_eq_of_some_bool hbk3
    simp [valsOf, boolOrR, hv1, hv2, hv3, hrel]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨x, hbi1⟩
    · exact ⟨y, hbj2⟩
    · exact ⟨z, hbk3⟩

/-- Every accepted assignment reads the operands of `bool_eq` as Boolean
and satisfies equality. -/
theorem boolEqR_spec (p : CompiledProblem DomConstraint) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints)
    (doms : Array DomC) (args : List BArg)
    (hargs : ofSlots doms [i, j] = some args) :
    ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      boolEqR (valsOf b args) = true ∧
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v) := by
  intro b hb hacc
  obtain ⟨a1, a2, rfl, hs1, hs2⟩ := ofSlots_two hargs
  have hsat : (DomConstraint.boolEqSlot i j).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, y, hbi, hbj, hrel⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hsat
  have hbi1 : b[a1.slot]? = some (.bool x) := by rwa [hs1]
  have hbj2 : b[a2.slot]? = some (.bool y) := by rwa [hs2]
  constructor
  · have hv1 : a1.valAt b = x := BArg.valAt_eq_of_some_bool hbi1
    have hv2 : a2.valAt b = y := BArg.valAt_eq_of_some_bool hbj2
    simp [valsOf, boolEqR, hv1, hv2, hrel]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨x, hbi1⟩
    · exact ⟨y, hbj2⟩

/-- Every accepted assignment satisfies the `array_bool_and` relation on
the operand vector, provided the initial source domains are Boolean. -/
theorem arrayBoolAndR_spec (p : CompiledProblem DomConstraint)
    (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (doms : Array DomC) (args : List BArg)
    (hargs : ofSlots doms (is ++ [k]) = some args)
    (hinit : ∀ s ∈ is, initBoolB p s = true) :
    ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
      arrayBoolAndR is.length (valsOf b args) = true ∧
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v) := by
  intro b hb hacc
  obtain ⟨src, ak, rfl, hmap, hk⟩ := ofSlots_array is hargs
  have hsat : (DomConstraint.arrayBoolAndSlot is k).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  have hsem : b[k]? = some (.bool (is.all fun i => slotIsBoolB b i true)) :=
    (DomConstraint.satisfiedB_iff _ _).mp hsat
  have hbk : b[ak.slot]? = some (.bool (is.all fun i => slotIsBoolB b i true)) := by
    rwa [hk]
  have hvalk : ak.valAt b = is.all fun i => slotIsBoolB b i true :=
    BArg.valAt_eq_of_some_bool hbk
  have hvals_src : valsOf b src = is.map (fun i => slotIsBoolB b i true) := by
    calc
      valsOf b src = src.map (fun a => BArg.valAt a b) := rfl
      _ = src.map (fun a => slotIsBoolB b a.slot true) := by
        apply List.map_congr_left
        intro a _ha
        exact BArg.valAt_eq_slotIsBoolB a b
      _ = is.map (fun i => slotIsBoolB b i true) := by
        rw [← hmap, List.map_map]
        simp [Function.comp]
  have hvals : valsOf b (src ++ [ak]) =
      is.map (fun i => slotIsBoolB b i true) ++
        [is.all fun i => slotIsBoolB b i true] := by
    simp only [valsOf, List.map_append, List.map_cons, List.map_nil]
    rw [show src.map (fun a => BArg.valAt a b) =
      is.map (fun i => slotIsBoolB b i true) from hvals_src]
    rw [hvalk]
  constructor
  · have htake : List.take is.length (valsOf b (src ++ [ak])) =
        is.map (fun i => slotIsBoolB b i true) := by
      rw [hvals]
      rw [List.take_append_of_le_length (by simp)]
      rw [List.take_of_length_le (by simp)]
    have hget : (valsOf b (src ++ [ak])).getD is.length false =
        is.all fun i => slotIsBoolB b i true := by
      rw [hvals]
      simpa [List.length_map] using
        getD_append_singleton_self
          (is.map (fun i => slotIsBoolB b i true))
          (is.all fun i => slotIsBoolB b i true)
    simp only [arrayBoolAndR]
    rw [hget, htake, List.all_map]
    simp [Function.comp]
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · have hmem_is : a.slot ∈ is := by
        have := List.mem_map_of_mem (f := BArg.slot) ha
        rwa [hmap] at this
      obtain ⟨bits, hconv⟩ := initBoolB_some (hinit a.slot hmem_is)
      exact mem_getD_bool_of_init hb hconv
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨_, hbk⟩

/-- Membership in `fixedLits` gives membership in one operand's own fixed
facts. -/
theorem mem_fixedLits_fixedLit {args : List BArg} {l : Literal}
    (h : l ∈ fixedLits args) : ∃ a ∈ args, l ∈ a.fixedLit := by
  induction args with
  | nil => simp [fixedLits] at h
  | cons a as ih =>
      simp only [fixedLits, List.mem_append] at h
      rcases h with h | h
      · exact ⟨a, by simp, h⟩
      · obtain ⟨a', ha', h'⟩ := ih h
        exact ⟨a', by simp [ha'], h'⟩

/-- A member of a successfully parsed operand list is exactly the
`BArg.mk?` result at its own slot. -/
theorem ofSlots_mem_mk {doms : Array DomC} {slots : List Nat}
    {args : List BArg} (h : ofSlots doms slots = some args)
    {a : BArg} (ha : a ∈ args) : BArg.mk? doms a.slot = some a := by
  induction slots generalizing args with
  | nil =>
      simp [ofSlots] at h
      subst args
      simp at ha
  | cons s ss ih =>
      simp only [ofSlots] at h
      cases hm : BArg.mk? doms s with
      | none => rw [hm] at h; cases h
      | some a0 =>
          rw [hm] at h
          cases hr : ofSlots doms ss with
          | none => rw [hr] at h; cases h
          | some rest =>
              rw [hr] at h
              injection h with hargs
              subst hargs
              rcases List.mem_cons.mp ha with rfl | ha
              · simpa [BArg.mk?, BArg.ofDom?_slot hm] using hm
              · exact ih hr ha

/-- The fixed facts of a successfully parsed operand list all evaluate to
`false` on the view domains. -/
theorem ofSlots_eval_fixed {doms : Array DomC} {slots : List Nat}
    {args : List BArg} (h : ofSlots doms slots = some args)
    {l : Literal} (hl : l ∈ fixedLits args) :
    (doms.getD l.atom.slot DomC.empty).evalLit l = some false := by
  obtain ⟨a, ha, hla⟩ := mem_fixedLits_fixedLit hl
  have hmk := ofSlots_mem_mk h ha
  have hsl := BArg.slot_of_mem_fixedLit hla
  rw [hsl]
  exact BArg.ofDom?_evalLit_fixed hmk l hla

/-- Truth of `hasAnySupport` exposes a satisfying tuple in the box. -/
theorem hasAnySupport_true {R : List Bool → Bool} {args : List BArg}
    (h : hasAnySupport R args = true) :
    ∃ vs ∈ enum args, R vs = true := by
  unfold hasAnySupport at h
  exact List.any_eq_true.mp h

/-- A tuple in the current box has the current value at every in-range
position. -/
theorem curVec_getD {args : List BArg} {vs : List Bool} {p : Nat}
    (h : curVec args vs = true) (hp : p < args.length) :
    (args.getD p default).cur (vs.getD p false) = true := by
  induction args generalizing vs p with
  | nil => simp at hp
  | cons a as ih =>
      cases vs with
      | nil => simp [curVec] at h
      | cons v vs =>
          simp only [curVec, Bool.and_eq_true] at h
          obtain ⟨ha, hrest⟩ := h
          cases p with
          | zero => simpa using ha
          | succ p =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at hp
              simpa using ih hrest hp

/-- If a value has no support but some tuple has support, the opposite
value is still current. -/
theorem cur_other_of_prune {R : List Bool → Bool} {args : List BArg}
    {p : Nat} {v : Bool} (hany : hasAnySupport R args = true)
    (hsupp : hasSupport R args p v = false) (hp : p < args.length) :
    (args.getD p default).cur (!v) = true := by
  obtain ⟨vs, hvs, hr⟩ := hasAnySupport_true hany
  have hcur := curVec_getD (mem_enum_iff.mp hvs).2 hp
  have hne : vs.getD p false ≠ v := by
    intro heq
    have ht : hasSupport R args p v = true := by
      unfold hasSupport
      rw [List.any_eq_true]
      exact ⟨vs, hvs, by rw [heq, hr]; simp⟩
    rw [hsupp] at ht
    cases ht
  have hother : vs.getD p false = !v := by
    cases hv : vs.getD p false <;> cases vv : v <;> simp_all
  rwa [hother] at hcur

/-- A conflicting support plan's clause is exactly the fixed facts. -/
theorem mkPlan_conflict_eq_fixedLits {R : List Bool → Bool}
    {args : List BArg} {ls : List Literal}
    (h : (mkPlan R args).conflict? = some ls) : ls = fixedLits args := by
  unfold mkPlan at h
  by_cases hany : hasAnySupport R args = true
  · simp [hany] at h
  · have h' : fixedLits args = ls := by simpa [hany] using h
    exact h'.symm

/-- The reason and pruned literal of a generated prune have the exact
complement shape. -/
theorem mem_mkPrunes_shape {R : List Bool → Bool} {args : List BArg} {bp : BPrune}
    (h : bp ∈ mkPrunes R args) :
    bp.reason = posBool bp.slot (!bp.val) :: fixedLits args ∧
      bp.lit = posBool bp.slot (!bp.val) := by
  rcases mem_mkPrunes h with ⟨p, hp, _, _, rfl⟩ | ⟨p, hp, _, _, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A generated prune is sound: its literal is unassigned on the view and
every other literal of its reason is already false.  This uses that a
non-conflicting plan has a satisfying tuple, so a pruned value cannot be
the unique value of a fixed domain. -/
theorem mkPrunes_evalLit_none {R : List Bool → Bool} {args : List BArg}
    {doms : Array DomC} {slots : List Nat}
    (hargs : ofSlots doms slots = some args)
    (hany : hasAnySupport R args = true)
    {bp : BPrune} (hbp : bp ∈ mkPrunes R args) :
    (doms.getD bp.lit.atom.slot DomC.empty).evalLit bp.lit = none ∧
      ∀ q ∈ bp.reason, q ≠ bp.lit →
        (doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  rcases mem_mkPrunes hbp with ⟨p, hp, hcurF, hsupp, rfl⟩ |
    ⟨p, hp, hcurT, hsupp, rfl⟩
  · have hcurT : (args.getD p default).curT = true := by
      have := cur_other_of_prune hany hsupp hp
      simpa [BArg.cur] using this
    have hmk := ofSlots_mem_mk hargs (getD_mem hp)
    constructor
    · exact BArg.ofDom?_evalLit_none_full hmk hcurF hcurT true
    · intro q hq hne
      have hqtail : q ∈ fixedLits args := by
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact absurd rfl hne
        · exact hq
      exact ofSlots_eval_fixed hargs hqtail
  · have hcurF : (args.getD p default).curF = true := by
      have := cur_other_of_prune hany hsupp hp
      simpa [BArg.cur] using this
    have hmk := ofSlots_mem_mk hargs (getD_mem hp)
    constructor
    · exact BArg.ofDom?_evalLit_none_full hmk hcurF hcurT false
    · intro q hq hne
      have hqtail : q ∈ fixedLits args := by
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact absurd rfl hne
        · exact hq
      exact ofSlots_eval_fixed hargs hqtail

def dedupGo (seen : List Nat) (out : List BArg) : List BArg → List BArg
  | [] => out.reverse
  | a :: as =>
      if a.slot ∈ seen then dedupGo seen out as
      else dedupGo (a.slot :: seen) (a :: out) as

/-- First occurrence of each operand slot, in order. -/
def dedupArgs (args : List BArg) : List BArg := dedupGo [] [] args

theorem mem_dedupGo_of_mem_out {seen : List Nat} {out as : List BArg}
    {b : BArg} (hb : b ∈ out) : b ∈ dedupGo seen out as := by
  induction as generalizing seen out with
  | nil => simpa [dedupGo] using hb
  | cons a as ih =>
      by_cases h : a.slot ∈ seen
      · simpa [dedupGo, h] using ih (seen := seen) (out := out) hb
      · simpa [dedupGo, h] using
          ih (seen := a.slot :: seen) (out := a :: out)
            (List.mem_cons_of_mem _ hb)

theorem dedupGo_subset {seen : List Nat} {out as : List BArg} :
    ∀ {b : BArg}, b ∈ dedupGo seen out as → b ∈ out ∨ b ∈ as := by
  induction as generalizing seen out with
  | nil =>
      intro b hb
      exact Or.inl (by simpa [dedupGo] using hb)
  | cons a as ih =>
      intro b hb
      by_cases h : a.slot ∈ seen
      · rw [dedupGo, if_pos h] at hb
        rcases ih hb with ho | ha
        · exact Or.inl ho
        · exact Or.inr (List.mem_cons_of_mem _ ha)
      · rw [dedupGo, if_neg h] at hb
        rcases ih hb with ho | ha
        · rcases List.mem_cons.mp ho with rfl | ho
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl ho
        · exact Or.inr (List.mem_cons_of_mem _ ha)

theorem dedupArgs_subset {args : List BArg} {b : BArg}
    (hb : b ∈ dedupArgs args) : b ∈ args := by
  have h := dedupGo_subset (seen := []) (out := []) (as := args) hb
  rcases h with h | h
  · simpa using h
  · exact h

theorem dedupGo_slot_mem {seen : List Nat} {out as : List BArg}
    (hinv : ∀ s ∈ seen, ∃ b ∈ out, b.slot = s) :
    ∀ a ∈ as, ∃ b ∈ dedupGo seen out as, b.slot = a.slot := by
  induction as generalizing seen out with
  | nil => intro a ha; simp at ha
  | cons a0 as ih =>
      intro a ha
      by_cases h : a0.slot ∈ seen
      · rw [dedupGo, if_pos h]
        rcases List.mem_cons.mp ha with rfl | ha
        · rcases hinv a.slot h with ⟨b, hb, hbs⟩
          exact ⟨b, mem_dedupGo_of_mem_out hb, hbs⟩
        · exact ih (seen := seen) (out := out) hinv a ha
      · rw [dedupGo, if_neg h]
        have hinv' : ∀ s ∈ a0.slot :: seen,
            ∃ b ∈ a0 :: out, b.slot = s := by
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ⟨a0, List.mem_cons_self .., rfl⟩
          · rcases hinv s hs with ⟨b, hb, hbs⟩
            exact ⟨b, List.mem_cons_of_mem _ hb, hbs⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨a, mem_dedupGo_of_mem_out (List.mem_cons_self ..), rfl⟩
        · exact ih (seen := a0.slot :: seen) (out := a0 :: out) hinv' a ha

theorem dedupArgs_slot_mem {args : List BArg} {a : BArg} (ha : a ∈ args) :
    ∃ b ∈ dedupArgs args, b.slot = a.slot :=
  dedupGo_slot_mem (seen := []) (out := []) (as := args)
    (by intro s hs; simp at hs) a ha

/-- Position of the first operand with slot `s` in a deduped list. -/
def idxOfSlot (s : Nat) : List BArg → Nat
  | [] => 0
  | a :: as => if a.slot = s then 0 else idxOfSlot s as + 1

theorem idxOfSlot_spec (s : Nat) (args : List BArg)
    (h : ∃ b ∈ args, b.slot = s) :
    idxOfSlot s args < args.length ∧
      (args.getD (idxOfSlot s args) default).slot = s := by
  induction args with
  | nil =>
      rcases h with ⟨b, hb, _⟩
      simp at hb
  | cons a as ih =>
      by_cases ha : a.slot = s
      · simp [idxOfSlot, ha]
      · have h' : ∃ b ∈ as, b.slot = s := by
          rcases h with ⟨b, hb, hbs⟩
          rcases List.mem_cons.mp hb with rfl | hb
          · exact absurd hbs ha
          · exact ⟨b, hb, hbs⟩
        have hs := ih h'
        constructor
        · simp only [idxOfSlot, if_neg ha, List.length_cons]
          omega
        · simp only [idxOfSlot, if_neg ha, List.getD_cons_succ]
          exact hs.2

/-- Expand a value vector over distinct slots to the positional vector. -/
def expandVals (full dedup : List BArg) (vs : List Bool) : List Bool :=
  full.map fun a => vs.getD (idxOfSlot a.slot dedup) false

theorem valsOf_expand (b : Assignment) (args : List BArg) :
    valsOf b args =
      expandVals args (dedupArgs args) (valsOf b (dedupArgs args)) := by
  change args.map (fun a => a.valAt b) =
    args.map (fun a =>
      (valsOf b (dedupArgs args)).getD (idxOfSlot a.slot (dedupArgs args)) false)
  apply List.map_congr_left
  intro a ha
  have hocc : ∃ c ∈ dedupArgs args, c.slot = a.slot := dedupArgs_slot_mem ha
  have hspec := idxOfSlot_spec a.slot (dedupArgs args) hocc
  rw [valsOf_getD (b := b) (args := dedupArgs args)
    (p := idxOfSlot a.slot (dedupArgs args)) hspec.1]
  simp only [BArg.valAt]
  rw [hspec.2]

theorem ofSlots_of_mk? {doms : Array DomC} :
    ∀ {args : List BArg}, (∀ a ∈ args, BArg.mk? doms a.slot = some a) →
      ofSlots doms (args.map BArg.slot) = some args
  | [], _ => by simp [ofSlots]
  | a :: as, hm => by
      have ha := hm a (List.mem_cons_self ..)
      have ht : ofSlots doms (as.map BArg.slot) = some as :=
        ofSlots_of_mk? (doms := doms) (args := as)
          (fun b hb => hm b (List.mem_cons_of_mem _ hb))
      simp only [List.map_cons, ofSlots, ha, ht]

theorem ofSlots_dedup {doms : Array DomC} {slots : List Nat} {args : List BArg}
    (h : ofSlots doms slots = some args) :
    ofSlots doms ((dedupArgs args).map BArg.slot) = some (dedupArgs args) := by
  apply ofSlots_of_mk?
  intro a ha
  exact ofSlots_mem_mk h (dedupArgs_subset ha)

/-- Runtime guard: the slot list repeats a slot. -/
def hasDupSlots : List Nat → Bool
  | [] => false
  | s :: ss => ss.contains s || hasDupSlots ss

end BArgs

namespace BPlan

/-- Exact conflict output of a plan computed by `BArgs.planOf`, exposing
the fixed source facts. -/
theorem out_run_conflict_plan {p : CompiledProblem DomConstraint} {T : LitTable}
    {R : List Bool → Bool} {slots : List Nat} {doms : Array DomC}
    {args : List BArg} {plan : BPlan}
    (hplan : BArgs.planOf R slots doms = some (args, plan))
    {hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls}
    {hprune : ∀ q ∈ plan.prunes, Entailed p q.reason}
    {ec : EClause p T}
    (h : plan.out p T hconf hprune = .conflict ec) :
    ∃ ls, plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  obtain ⟨ls, hls, hdec, hent⟩ := out_run_conflict p T plan hconf hprune h
  obtain ⟨_hargs, _hdup, rfl⟩ := BArgs.planOf_some hplan
  exact ⟨ls, hls, BArgs.mkPlan_conflict_eq_fixedLits hls, hdec, hent⟩

/-- Exact prune output of a plan computed by `BArgs.planOf`, exposing the
fixed source facts and the exact reason shape. -/
theorem out_run_prune_plan {p : CompiledProblem DomConstraint} {T : LitTable}
    {R : List Bool → Bool} {slots : List Nat} {doms : Array DomC}
    {args : List BArg} {plan : BPlan}
    (hplan : BArgs.planOf R slots doms = some (args, plan))
    {hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls}
    {hprune : ∀ q ∈ plan.prunes, Entailed p q.reason}
    {ps : Array (PLit × EClause p T)}
    (h : plan.out p T hconf hprune = .prune ps) :
    plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      ∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason := by
  obtain ⟨hc, hne, hforall⟩ := out_run_prune p T plan hconf hprune h
  obtain ⟨_hargs, _hdup, rfl⟩ := BArgs.planOf_some hplan
  have hpr : (BArgs.mkPlan R args).prunes = BArgs.mkPrunes R args :=
    BArgs.planOf_prunes_eq hplan hc
  refine ⟨hc, hne, ?_⟩
  intro q hq
  obtain ⟨q', hq', hlit, hdec, hent⟩ := hforall q hq
  refine ⟨q', hq', hlit, hdec, ?_, hent⟩
  exact (BArgs.mem_mkPrunes_shape (by rwa [hpr] at hq')).1

/-- A pruned literal of a plan computed by `BArgs.planOf` is unassigned
and the rest of its reason is false. -/
theorem out_run_prune_lit_none_plan {p : CompiledProblem DomConstraint}
    {T : LitTable} {R : List Bool → Bool} {slots : List Nat}
    {doms : Array DomC} {args : List BArg} {plan : BPlan}
    (hplan : BArgs.planOf R slots doms = some (args, plan))
    {hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls}
    {hprune : ∀ q ∈ plan.prunes, Entailed p q.reason}
    {ps : Array (PLit × EClause p T)}
    (h : plan.out p T hconf hprune = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  obtain ⟨hc, _hne, hforall⟩ := out_run_prune p T plan hconf hprune h
  obtain ⟨hargs, _hdup, rfl⟩ := BArgs.planOf_some hplan
  have hpr : (BArgs.mkPlan R args).prunes = BArgs.mkPrunes R args :=
    BArgs.planOf_prunes_eq hplan hc
  have hany : BArgs.hasAnySupport R args = true := by
    cases hh : BArgs.hasAnySupport R args with
    | false => simp [BArgs.mkPlan, hh] at hc
    | true => rfl
  obtain ⟨q', hq', hlit, hdec, _hent⟩ := hforall q hq
  have hq'' : q' ∈ BArgs.mkPrunes R args := by rwa [hpr] at hq'
  obtain ⟨hnone, hfalse⟩ := BArgs.mkPrunes_evalLit_none hargs hany hq''
  constructor
  · rw [hlit]
    exact hnone
  · intro r hr hne
    rw [hdec] at hr
    exact hfalse r hr (by rwa [hlit] at hne)

end BPlan

/-! ## Generic certified truth-table propagator -/

/-- Generic Boolean truth-table propagator over a fixed operand list.
`hR` proves the relation on every accepted assignment and `hbool` proves
that every accepted assignment reads the operands as Booleans.  The plan
is computed on the current Boolean box; malformed views and duplicate
operand slots produce `.fix`. -/
def boolSupportPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v)) : PropV2 p T :=
  { vars := slots.toArray
    events := slots.toArray.map fun s => (s, .fix)
    run := fun view =>
      match hplan : BArgs.planOf R slots view.doms with
      | none => .fix
      | some ap =>
          BPlan.out p T (BArgs.mkPlan R ap.1)
            (fun ls hls =>
              BArgs.mkPlan_conflict_entailed p R ap.1 ls
                (hR view.doms ap.1 (BArgs.planOf_some hplan).1)
                (hbool view.doms ap.1 (BArgs.planOf_some hplan).1)
                (BArgs.ofSlots_allCur (BArgs.planOf_some hplan).1) hls)
            (fun q hq =>
              BArgs.mkPlan_prunes_entailed p R ap.1
                (hR view.doms ap.1 (BArgs.planOf_some hplan).1)
                (hbool view.doms ap.1 (BArgs.planOf_some hplan).1)
                (BArgs.ofSlots_allCur (BArgs.planOf_some hplan).1) hq) }

/-! ### Generic run contracts -/

theorem boolSupportPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ec : EClause p T}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .conflict ec) :
    ∃ args plan ls,
      BArgs.planOf R slots view.doms = some (args, plan) ∧
      plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  unfold boolSupportPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ap hplan
    cases ap with
    | mk args plan =>
      have hpl : plan = BArgs.mkPlan R args :=
        (BArgs.planOf_some hplan).2.2
      have hplan' : BArgs.planOf R slots view.doms =
          some (args, BArgs.mkPlan R args) := by
        rw [← hpl]
        exact hplan
      obtain ⟨ls, hls, hls', hdec, hent⟩ :=
        BPlan.out_run_conflict_plan (R := R) (slots := slots)
          (doms := view.doms) (args := args)
          (plan := BArgs.mkPlan R args) hplan' h
      exact ⟨args, BArgs.mkPlan R args, ls, hplan', hls, hls', hdec, hent⟩

theorem boolSupportPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .prune ps) :
    ∃ args plan,
      BArgs.planOf R slots view.doms = some (args, plan) ∧
      plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason) := by
  unfold boolSupportPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ap hplan
    cases ap with
    | mk args plan =>
      have hpl : plan = BArgs.mkPlan R args :=
        (BArgs.planOf_some hplan).2.2
      have hplan' : BArgs.planOf R slots view.doms =
          some (args, BArgs.mkPlan R args) := by
        rw [← hpl]
        exact hplan
      obtain ⟨hc, hne, hforall⟩ :=
        BPlan.out_run_prune_plan (R := R) (slots := slots)
          (doms := view.doms) (args := args)
          (plan := BArgs.mkPlan R args) hplan' h
      exact ⟨args, BArgs.mkPlan R args, hplan', hc, hne, hforall⟩

theorem boolSupportPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ec : EClause p T}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, hdec, hent⟩ :=
    boolSupportPropWith_run_conflict p T R slots hR hbool view h
  rwa [hdec]

theorem boolSupportPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ec : EClause p T}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  obtain ⟨args, _, _, hplan, _, hls', hdec, _⟩ :=
    boolSupportPropWith_run_conflict p T R slots hR hbool view h
  have hargs := (BArgs.planOf_some hplan).1
  rw [hdec, hls']
  intro q hq
  exact BArgs.ofSlots_eval_fixed hargs hq

theorem boolSupportPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, hforall⟩ :=
    boolSupportPropWith_run_prune p T R slots hR hbool view h
  obtain ⟨_, _, _, hdec, _, hent⟩ := hforall q hq
  rwa [hdec]

theorem boolSupportPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (boolSupportPropWith p T R slots hR hbool).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  unfold boolSupportPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ap hplan
    cases ap with
    | mk args plan =>
      have hpl : plan = BArgs.mkPlan R args :=
        (BArgs.planOf_some hplan).2.2
      have hplan' : BArgs.planOf R slots view.doms =
          some (args, BArgs.mkPlan R args) := by
        rw [← hpl]
        exact hplan
      exact BPlan.out_run_prune_lit_none_plan (R := R) (slots := slots)
        (doms := view.doms) (args := args)
        (plan := BArgs.mkPlan R args) hplan' h hq

theorem boolSupportPropWith_run_fix_of_no_plan
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView)
    (hpn : BArgs.planOf R slots view.doms = none) :
    (boolSupportPropWith p T R slots hR hbool).run view = .fix := by
  unfold boolSupportPropWith
  dsimp only
  split
  · rfl
  · rename_i ap hplan
    rw [hpn] at hplan
    cases hplan

def boolSupportDupPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v)) : PropV2 p T :=
  { vars := slots.toArray
    events := slots.toArray.map fun s => (s, .fix)
    run := fun view =>
      match hfull : BArgs.ofSlots view.doms slots with
      | none => .fix
      | some args =>
          let dargs := BArgs.dedupArgs args
          let R' : List Bool → Bool :=
            fun vs => R (BArgs.expandVals args dargs vs)
          BPlan.out p T (BArgs.mkPlan R' dargs)
            (fun ls hls =>
              BArgs.mkPlan_conflict_entailed p R' dargs ls
                (fun b hb hacc => by
                  have h := hR view.doms args hfull b hb hacc
                  rw [BArgs.valsOf_expand b args] at h
                  exact h)
                (fun b hb hacc a ha =>
                  hbool view.doms args hfull b hb hacc a
                    (BArgs.dedupArgs_subset ha))
                (fun a ha =>
                  BArgs.ofSlots_allCur hfull a (BArgs.dedupArgs_subset ha))
                hls)
            (fun q hq =>
              BArgs.mkPlan_prunes_entailed p R' dargs
                (fun b hb hacc => by
                  have h := hR view.doms args hfull b hb hacc
                  rw [BArgs.valsOf_expand b args] at h
                  exact h)
                (fun b hb hacc a ha =>
                  hbool view.doms args hfull b hb hacc a
                    (BArgs.dedupArgs_subset ha))
                (fun a ha =>
                  BArgs.ofSlots_allCur hfull a (BArgs.dedupArgs_subset ha))
                hq) }

theorem boolSupportDupPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ec : EClause p T}
    (h : (boolSupportDupPropWith p T R slots hR hbool).run view = .conflict ec) :
    ∃ args dargs,
      BArgs.ofSlots view.doms slots = some args ∧
      dargs = BArgs.dedupArgs args ∧
      (BArgs.mkPlan (fun vs => R (BArgs.expandVals args dargs vs)) dargs).conflict?
        = some (BArgs.fixedLits dargs) ∧
      T.decodeClause ec.lits = BArgs.fixedLits dargs ∧
      Entailed p (BArgs.fixedLits dargs) := by
  unfold boolSupportDupPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i args hfull
    obtain ⟨ls, hls, hdec, hent⟩ :=
      BPlan.out_run_conflict p T _ _ _ h
    have hls' : ls = BArgs.fixedLits (BArgs.dedupArgs args) :=
      BArgs.mkPlan_conflict_eq_fixedLits hls
    subst hls'
    exact ⟨args, BArgs.dedupArgs args, hfull, rfl, hls, hdec, hent⟩

theorem boolSupportDupPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (boolSupportDupPropWith p T R slots hR hbool).run view = .prune ps) :
    ∃ args dargs,
      BArgs.ofSlots view.doms slots = some args ∧
      dargs = BArgs.dedupArgs args ∧
      (BArgs.mkPlan (fun vs => R (BArgs.expandVals args dargs vs)) dargs).conflict? = none ∧
      (BArgs.mkPlan (fun vs => R (BArgs.expandVals args dargs vs)) dargs).prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈
        (BArgs.mkPlan (fun vs => R (BArgs.expandVals args dargs vs)) dargs).prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits dargs ∧
          Entailed p q'.reason) := by
  unfold boolSupportDupPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i args hfull
    obtain ⟨hc, hne, hforall⟩ :=
      BPlan.out_run_prune p T _ _ _ h
    refine ⟨args, BArgs.dedupArgs args, hfull, rfl, hc, hne, ?_⟩
    intro q hq
    obtain ⟨q', hq', hlit, hdec, hent⟩ := hforall q hq
    have hpr : (BArgs.mkPlan
        (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
        (BArgs.dedupArgs args)).prunes =
        BArgs.mkPrunes
          (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
          (BArgs.dedupArgs args) := by
      have hany : BArgs.hasAnySupport
          (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
          (BArgs.dedupArgs args) = true := by
        cases hh : BArgs.hasAnySupport
            (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
            (BArgs.dedupArgs args) with
        | false => simp [BArgs.mkPlan, hh] at hc
        | true => rfl
      simp [BArgs.mkPlan, hany]
    exact ⟨q', hq', hlit, hdec,
      (BArgs.mem_mkPrunes_shape (by rwa [hpr] at hq')).1, hent⟩

theorem boolSupportDupPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (R : List Bool → Bool) (slots : List Nat)
    (hR : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        R (BArgs.valsOf b args) = true)
    (hbool : ∀ (doms : Array DomC) (args : List BArg),
      BArgs.ofSlots doms slots = some args →
      ∀ b, b ∈ allAssigns p.domains → accepts p b = true →
        ∀ a ∈ args, ∃ v, b[a.slot]? = some (.bool v))
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (boolSupportDupPropWith p T R slots hR hbool).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  obtain ⟨args, dargs, hfull, hdargs, hc, _hne, hforall⟩ :=
    boolSupportDupPropWith_run_prune p T R slots hR hbool view h
  subst hdargs
  have hany : BArgs.hasAnySupport
      (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
      (BArgs.dedupArgs args) = true := by
    cases hh : BArgs.hasAnySupport
        (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
        (BArgs.dedupArgs args) with
    | false => simp [BArgs.mkPlan, hh] at hc
    | true => rfl
  have hpr : (BArgs.mkPlan
      (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
      (BArgs.dedupArgs args)).prunes =
      BArgs.mkPrunes
        (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
        (BArgs.dedupArgs args) := by
    simp [BArgs.mkPlan, hany]
  obtain ⟨q', hq', hlit, hdec, _hent⟩ := hforall q hq
  have hq'' : q' ∈ BArgs.mkPrunes
      (fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
      (BArgs.dedupArgs args) := by rwa [hpr] at hq'
  obtain ⟨hnone, hfalse⟩ := BArgs.mkPrunes_evalLit_none
    (R := fun vs => R (BArgs.expandVals args (BArgs.dedupArgs args) vs))
    (args := BArgs.dedupArgs args) (doms := view.doms)
    (slots := (BArgs.dedupArgs args).map BArg.slot)
    (BArgs.ofSlots_dedup hfull) hany hq''
  constructor
  · rw [hlit]
    exact hnone
  · intro r hr hne
    rw [hdec] at hr
    exact hfalse r hr (by rwa [hlit] at hne)

/-! ## Dedicated propagators -/

/-- Certified `bool_not` propagator. -/
def boolNotPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) : PropV2 p T :=
  boolSupportPropWith p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j))
    (fun doms args hargs b hb hacc =>
      (BArgs.boolNotR_spec p i j hmem doms args hargs b hb hacc).1)
    (fun doms args hargs b hb hacc =>
      (BArgs.boolNotR_spec p i j hmem doms args hargs b hb hacc).2)

/-- Certified `bool_and` propagator. -/
def boolAndPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) : PropV2 p T :=
  boolSupportPropWith p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k))
    (fun doms args hargs b hb hacc =>
      (BArgs.boolAndR_spec p i j k hmem doms args hargs b hb hacc).1)
    (fun doms args hargs b hb hacc =>
      (BArgs.boolAndR_spec p i j k hmem doms args hargs b hb hacc).2)

/-- Certified `bool_or` propagator. -/
def boolOrPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) : PropV2 p T :=
  boolSupportPropWith p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k))
    (fun doms args hargs b hb hacc =>
      (BArgs.boolOrR_spec p i j k hmem doms args hargs b hb hacc).1)
    (fun doms args hargs b hb hacc =>
      (BArgs.boolOrR_spec p i j k hmem doms args hargs b hb hacc).2)

/-- Certified `bool_eq` propagator. -/
def boolEqPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) : PropV2 p T :=
  boolSupportPropWith p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j))
    (fun doms args hargs b hb hacc =>
      (BArgs.boolEqR_spec p i j hmem doms args hargs b hb hacc).1)
    (fun doms args hargs b hb hacc =>
      (BArgs.boolEqR_spec p i j hmem doms args hargs b hb hacc).2)

/-- Runtime dispatch for Boolean rows: a row with repeated operand slots
takes the deduplicated support propagator, a duplicate-free row keeps the
original one unchanged. -/
def boolNotPropChoice (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat) (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) : PropV2 p T :=
  if BArgs.hasDupSlots [i, j] then
    boolSupportDupPropWith p T boolNotR [i, j]
      (fun doms args hargs b hb hacc =>
        (BArgs.boolNotR_spec p i j hmem doms args hargs b hb hacc).1)
      (fun doms args hargs b hb hacc =>
        (BArgs.boolNotR_spec p i j hmem doms args hargs b hb hacc).2)
  else boolNotPropWith p T i j hmem

/-- Runtime dispatch for `bool_and` rows (see `boolNotPropChoice`). -/
def boolAndPropChoice (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) : PropV2 p T :=
  if BArgs.hasDupSlots [i, j, k] then
    boolSupportDupPropWith p T boolAndR [i, j, k]
      (fun doms args hargs b hb hacc =>
        (BArgs.boolAndR_spec p i j k hmem doms args hargs b hb hacc).1)
      (fun doms args hargs b hb hacc =>
        (BArgs.boolAndR_spec p i j k hmem doms args hargs b hb hacc).2)
  else boolAndPropWith p T i j k hmem

/-- Runtime dispatch for `bool_or` rows (see `boolNotPropChoice`). -/
def boolOrPropChoice (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j k : Nat) (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) : PropV2 p T :=
  if BArgs.hasDupSlots [i, j, k] then
    boolSupportDupPropWith p T boolOrR [i, j, k]
      (fun doms args hargs b hb hacc =>
        (BArgs.boolOrR_spec p i j k hmem doms args hargs b hb hacc).1)
      (fun doms args hargs b hb hacc =>
        (BArgs.boolOrR_spec p i j k hmem doms args hargs b hb hacc).2)
  else boolOrPropWith p T i j k hmem

/-- Runtime dispatch for `bool_eq` rows (see `boolNotPropChoice`). -/
def boolEqPropChoice (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat) (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) : PropV2 p T :=
  if BArgs.hasDupSlots [i, j] then
    boolSupportDupPropWith p T boolEqR [i, j]
      (fun doms args hargs b hb hacc =>
        (BArgs.boolEqR_spec p i j hmem doms args hargs b hb hacc).1)
      (fun doms args hargs b hb hacc =>
        (BArgs.boolEqR_spec p i j hmem doms args hargs b hb hacc).2)
  else boolEqPropWith p T i j hmem

/-- Certified `array_bool_and` propagator.  The runtime guard requires the
initial source domains to be Boolean: the leaf semantics reads a
non-Boolean source as `false`, while the Boolean support box only
describes Boolean values.  When the guard fails the propagator is a
sound `.fix`. -/
def arrayBoolAndPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints) : PropV2 p T :=
  let ready := is.all (BArgs.initBoolB p)
  { vars := (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)).toArray
    events := (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)).toArray.map
      fun s => (s, .fix)
    run := fun view =>
      if hguard : ready = true then
        (boolSupportPropWith p T (arrayBoolAndR is.length)
          (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k))
          (fun doms args hargs b hb hacc =>
            (BArgs.arrayBoolAndR_spec p is k hmem doms args hargs
              (List.all_eq_true.mp hguard) b hb hacc).1)
          (fun doms args hargs b hb hacc =>
            (BArgs.arrayBoolAndR_spec p is k hmem doms args hargs
              (List.all_eq_true.mp hguard) b hb hacc).2)).run view
      else .fix }

/-! ### `bool_not` contracts -/

theorem boolNotPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolNotPropWith p T i j hmem).run view = .conflict ec) :
    ∃ args plan ls,
      BArgs.planOf boolNotR
          (dcSlotsFull (DomConstraint.boolNotSlot i j)) view.doms =
        some (args, plan) ∧
      plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls :=
  boolSupportPropWith_run_conflict p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h

theorem boolNotPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolNotPropWith p T i j hmem).run view = .prune ps) :
    ∃ args plan,
      BArgs.planOf boolNotR
          (dcSlotsFull (DomConstraint.boolNotSlot i j)) view.doms =
        some (args, plan) ∧
      plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason) :=
  boolSupportPropWith_run_prune p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h

theorem boolNotPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolNotPropWith p T i j hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) :=
  boolSupportPropWith_conflict_entailed p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h

theorem boolNotPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolNotPropWith p T i j hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolSupportPropWith_conflict_lits_false p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h

theorem boolNotPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolNotPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) :=
  boolSupportPropWith_prune_reason_entailed p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h hq

theorem boolNotPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolNotPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false :=
  boolSupportPropWith_prune_lit_none p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view h hq

theorem boolNotPropWith_run_fix_of_malformed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    (hi : BArg.mk? view.doms i = none) :
    (boolNotPropWith p T i j hmem).run view = .fix := by
  have hop : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolNotSlot i j)) = none := by
    change BArgs.ofSlots view.doms [i, j] = none
    exact BArgs.ofSlots_eq_none_of_mem_mk_none (by simp) hi
  have hpn : BArgs.planOf boolNotR
      (dcSlotsFull (DomConstraint.boolNotSlot i j)) view.doms = none := by
    unfold BArgs.planOf
    rw [hop]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view hpn

/-! ### `bool_and` contracts -/

theorem boolAndPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolAndPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ args plan ls,
      BArgs.planOf boolAndR
          (dcSlotsFull (DomConstraint.boolAndSlot i j k)) view.doms =
        some (args, plan) ∧
      plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls :=
  boolSupportPropWith_run_conflict p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h

theorem boolAndPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolAndPropWith p T i j k hmem).run view = .prune ps) :
    ∃ args plan,
      BArgs.planOf boolAndR
          (dcSlotsFull (DomConstraint.boolAndSlot i j k)) view.doms =
        some (args, plan) ∧
      plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason) :=
  boolSupportPropWith_run_prune p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h

theorem boolAndPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolAndPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) :=
  boolSupportPropWith_conflict_entailed p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h

theorem boolAndPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolAndPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolSupportPropWith_conflict_lits_false p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h

theorem boolAndPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolAndPropWith p T i j k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) :=
  boolSupportPropWith_prune_reason_entailed p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h hq

theorem boolAndPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolAndPropWith p T i j k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false :=
  boolSupportPropWith_prune_lit_none p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view h hq

theorem boolAndPropWith_run_fix_of_malformed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    (hi : BArg.mk? view.doms i = none) :
    (boolAndPropWith p T i j k hmem).run view = .fix := by
  have hop : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolAndSlot i j k)) = none := by
    change BArgs.ofSlots view.doms [i, j, k] = none
    exact BArgs.ofSlots_eq_none_of_mem_mk_none (by simp) hi
  have hpn : BArgs.planOf boolAndR
      (dcSlotsFull (DomConstraint.boolAndSlot i j k)) view.doms = none := by
    unfold BArgs.planOf
    rw [hop]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view hpn

/-! ### `bool_or` contracts -/

theorem boolOrPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolOrPropWith p T i j k hmem).run view = .conflict ec) :
    ∃ args plan ls,
      BArgs.planOf boolOrR
          (dcSlotsFull (DomConstraint.boolOrSlot i j k)) view.doms =
        some (args, plan) ∧
      plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls :=
  boolSupportPropWith_run_conflict p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h

theorem boolOrPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolOrPropWith p T i j k hmem).run view = .prune ps) :
    ∃ args plan,
      BArgs.planOf boolOrR
          (dcSlotsFull (DomConstraint.boolOrSlot i j k)) view.doms =
        some (args, plan) ∧
      plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason) :=
  boolSupportPropWith_run_prune p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h

theorem boolOrPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolOrPropWith p T i j k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) :=
  boolSupportPropWith_conflict_entailed p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h

theorem boolOrPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolOrPropWith p T i j k hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolSupportPropWith_conflict_lits_false p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h

theorem boolOrPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolOrPropWith p T i j k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) :=
  boolSupportPropWith_prune_reason_entailed p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h hq

theorem boolOrPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolOrPropWith p T i j k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false :=
  boolSupportPropWith_prune_lit_none p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view h hq

theorem boolOrPropWith_run_fix_of_malformed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    (hi : BArg.mk? view.doms i = none) :
    (boolOrPropWith p T i j k hmem).run view = .fix := by
  have hop : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolOrSlot i j k)) = none := by
    change BArgs.ofSlots view.doms [i, j, k] = none
    exact BArgs.ofSlots_eq_none_of_mem_mk_none (by simp) hi
  have hpn : BArgs.planOf boolOrR
      (dcSlotsFull (DomConstraint.boolOrSlot i j k)) view.doms = none := by
    unfold BArgs.planOf
    rw [hop]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view hpn

/-! ### `bool_eq` contracts -/

theorem boolEqPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolEqPropWith p T i j hmem).run view = .conflict ec) :
    ∃ args plan ls,
      BArgs.planOf boolEqR
          (dcSlotsFull (DomConstraint.boolEqSlot i j)) view.doms =
        some (args, plan) ∧
      plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls :=
  boolSupportPropWith_run_conflict p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h

theorem boolEqPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolEqPropWith p T i j hmem).run view = .prune ps) :
    ∃ args plan,
      BArgs.planOf boolEqR
          (dcSlotsFull (DomConstraint.boolEqSlot i j)) view.doms =
        some (args, plan) ∧
      plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
        q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
          q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
          Entailed p q'.reason) :=
  boolSupportPropWith_run_prune p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h

theorem boolEqPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolEqPropWith p T i j hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) :=
  boolSupportPropWith_conflict_entailed p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h

theorem boolEqPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (boolEqPropWith p T i j hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolSupportPropWith_conflict_lits_false p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h

theorem boolEqPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolEqPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) :=
  boolSupportPropWith_prune_reason_entailed p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h hq

theorem boolEqPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (boolEqPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false :=
  boolSupportPropWith_prune_lit_none p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view h hq

theorem boolEqPropWith_run_fix_of_malformed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    (hi : BArg.mk? view.doms i = none) :
    (boolEqPropWith p T i j hmem).run view = .fix := by
  have hop : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolEqSlot i j)) = none := by
    change BArgs.ofSlots view.doms [i, j] = none
    exact BArgs.ofSlots_eq_none_of_mem_mk_none (by simp) hi
  have hpn : BArgs.planOf boolEqR
      (dcSlotsFull (DomConstraint.boolEqSlot i j)) view.doms = none := by
    unfold BArgs.planOf
    rw [hop]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view hpn

/-! ### `array_bool_and` contracts -/

theorem arrayBoolAndPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .conflict ec) :
    is.all (BArgs.initBoolB p) = true ∧
      ∃ args plan ls,
        BArgs.planOf (arrayBoolAndR is.length)
            (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) view.doms =
          some (args, plan) ∧
        plan.conflict? = some ls ∧ ls = BArgs.fixedLits args ∧
        T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · rename_i hguard
    obtain ⟨args, plan, ls, hplan, hls, hls', hdec, hent⟩ :=
      boolSupportPropWith_run_conflict p T (arrayBoolAndR is.length)
        (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h
    exact ⟨hguard, args, plan, ls, hplan, hls, hls', hdec, hent⟩
  · cases h

theorem arrayBoolAndPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .prune ps) :
    is.all (BArgs.initBoolB p) = true ∧
      ∃ args plan,
        BArgs.planOf (arrayBoolAndR is.length)
            (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) view.doms =
          some (args, plan) ∧
        plan.conflict? = none ∧ plan.prunes ≠ [] ∧
        (∀ q ∈ ps.toList, ∃ q' ∈ plan.prunes,
          q.1.lit = q'.lit ∧ T.decodeClause q.2.lits = q'.reason ∧
            q'.reason = posBool q'.slot (!q'.val) :: BArgs.fixedLits args ∧
            Entailed p q'.reason) := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · rename_i hguard
    obtain ⟨args, plan, hplan, hc, hne, hforall⟩ :=
      boolSupportPropWith_run_prune p T (arrayBoolAndR is.length)
        (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h
    exact ⟨hguard, args, plan, hplan, hc, hne, hforall⟩
  · cases h

theorem arrayBoolAndPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · exact boolSupportPropWith_conflict_entailed p T (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h
  · cases h

theorem arrayBoolAndPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · exact boolSupportPropWith_conflict_lits_false p T
      (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h
  · cases h

theorem arrayBoolAndPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · exact boolSupportPropWith_prune_reason_entailed p T
      (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h hq
  · cases h

theorem arrayBoolAndPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (arrayBoolAndPropWith p T is k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  unfold arrayBoolAndPropWith at h
  dsimp only at h
  split at h
  · exact boolSupportPropWith_prune_lit_none p T (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view h hq
  · cases h

theorem arrayBoolAndPropWith_run_fix_of_malformed
    (p : CompiledProblem DomConstraint)
    (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView) {s : Nat} (hs : s ∈ is)
    (hi : BArg.mk? view.doms s = none) :
    (arrayBoolAndPropWith p T is k hmem).run view = .fix := by
  have hop : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) = none := by
    change BArgs.ofSlots view.doms (is ++ [k]) = none
    exact BArgs.ofSlots_eq_none_of_mem_mk_none (List.mem_append.mpr (Or.inl hs)) hi
  have hpn : BArgs.planOf (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) view.doms = none := by
    unfold BArgs.planOf
    rw [hop]
  unfold arrayBoolAndPropWith
  dsimp only
  split
  · exact boolSupportPropWith_run_fix_of_no_plan p T
      (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view hpn
  · rfl

/-! ### General malformed-view statements

These take the whole operand list as malformed, so they cover a
non-Boolean or out-of-range domain at *any* operand, including the result
slot of `array_bool_and`. -/

theorem boolNotPropWith_run_fix_of_slots_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolNotSlot i j ∈ p.constraints) (view : EngineView)
    (h : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolNotSlot i j)) = none) :
    (boolNotPropWith p T i j hmem).run view = .fix := by
  have hpn : BArgs.planOf boolNotR
      (dcSlotsFull (DomConstraint.boolNotSlot i j)) view.doms = none := by
    unfold BArgs.planOf
    rw [h]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolNotR
    (dcSlotsFull (DomConstraint.boolNotSlot i j)) _ _ view hpn

theorem boolAndPropWith_run_fix_of_slots_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolAndSlot i j k ∈ p.constraints) (view : EngineView)
    (h : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolAndSlot i j k)) = none) :
    (boolAndPropWith p T i j k hmem).run view = .fix := by
  have hpn : BArgs.planOf boolAndR
      (dcSlotsFull (DomConstraint.boolAndSlot i j k)) view.doms = none := by
    unfold BArgs.planOf
    rw [h]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolAndR
    (dcSlotsFull (DomConstraint.boolAndSlot i j k)) _ _ view hpn

theorem boolOrPropWith_run_fix_of_slots_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j k : Nat)
    (hmem : DomConstraint.boolOrSlot i j k ∈ p.constraints) (view : EngineView)
    (h : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolOrSlot i j k)) = none) :
    (boolOrPropWith p T i j k hmem).run view = .fix := by
  have hpn : BArgs.planOf boolOrR
      (dcSlotsFull (DomConstraint.boolOrSlot i j k)) view.doms = none := by
    unfold BArgs.planOf
    rw [h]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolOrR
    (dcSlotsFull (DomConstraint.boolOrSlot i j k)) _ _ view hpn

theorem boolEqPropWith_run_fix_of_slots_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.boolEqSlot i j ∈ p.constraints) (view : EngineView)
    (h : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.boolEqSlot i j)) = none) :
    (boolEqPropWith p T i j hmem).run view = .fix := by
  have hpn : BArgs.planOf boolEqR
      (dcSlotsFull (DomConstraint.boolEqSlot i j)) view.doms = none := by
    unfold BArgs.planOf
    rw [h]
  exact boolSupportPropWith_run_fix_of_no_plan p T boolEqR
    (dcSlotsFull (DomConstraint.boolEqSlot i j)) _ _ view hpn

theorem arrayBoolAndPropWith_run_fix_of_slots_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (view : EngineView)
    (h : BArgs.ofSlots view.doms
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) = none) :
    (arrayBoolAndPropWith p T is k hmem).run view = .fix := by
  have hpn : BArgs.planOf (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) view.doms = none := by
    unfold BArgs.planOf
    rw [h]
  unfold arrayBoolAndPropWith
  dsimp only
  split
  · exact boolSupportPropWith_run_fix_of_no_plan p T
      (arrayBoolAndR is.length)
      (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)) _ _ view hpn
  · rfl

/-! ## Closed-form `array_bool_and` plan -/

/-- All sources currently contain `true`. -/
def allCurT (src : List BArg) : Bool := src.all fun a => a.curT

/-- Some source currently contains `false`. -/
def anyCurF (src : List BArg) : Bool := src.any fun a => a.curF

/-- Some source other than position `p` currently contains `false`.  The
index scan is quadratic in the operand count, which is harmless for the
small arrays produced by FlatZinc flattening, and avoids any `eraseIdx`
reasoning. -/
def anyOtherCurF (src : List BArg) (p : Nat) : Bool :=
  (List.range src.length).any fun i =>
    (src.getD i default).curF && i != p

theorem allCurT_eq_true {src : List BArg} :
    allCurT src = true ↔ ∀ a ∈ src, a.curT = true := by
  simp [allCurT]

theorem anyCurF_eq_true {src : List BArg} :
    anyCurF src = true ↔ ∃ a ∈ src, a.curF = true := by
  simp [anyCurF]

theorem anyOtherCurF_eq_true {src : List BArg} {p : Nat} :
    anyOtherCurF src p = true ↔
      ∃ i, i < src.length ∧ (src.getD i default).curF = true ∧ i ≠ p := by
  unfold anyOtherCurF
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hc⟩
    rw [List.mem_range] at hi
    simp only [Bool.and_eq_true] at hc
    exact ⟨i, hi, hc.1, by simpa using hc.2⟩
  · rintro ⟨i, hi, hc, hne⟩
    refine ⟨i, by simpa using hi, ?_⟩
    have hc' : src[i].curF = true := by
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hc
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hc', hne]

/-- Closed-form support test for `array_bool_and` on `src ++ [ak]`.
`pos < src.length` is a source position; `pos = src.length` is the result
position.  The test is exact on nonempty Boolean boxes, but only its
forward direction (a satisfying assignment reaches a current value that
passes the test) is needed for soundness. -/
def arrayBoolAndSupp (src : List BArg) (ak : BArg) (pos : Nat) (v : Bool) : Bool :=
  if pos < src.length then
    (if v then
      (ak.curT && allCurT src) || (ak.curF && anyOtherCurF src pos)
     else ak.curF)
  else if pos = src.length then
    (if v then allCurT src else anyCurF src)
  else false

@[simp] theorem arrayBoolAndSupp_source_false {src : List BArg} {ak : BArg}
    {p : Nat} (hp : p < src.length) :
    arrayBoolAndSupp src ak p false = ak.curF := by
  simp [arrayBoolAndSupp, hp]

@[simp] theorem arrayBoolAndSupp_source_true {src : List BArg} {ak : BArg}
    {p : Nat} (hp : p < src.length) :
    arrayBoolAndSupp src ak p true =
      ((ak.curT && allCurT src) || (ak.curF && anyOtherCurF src p)) := by
  simp [arrayBoolAndSupp, hp]

@[simp] theorem arrayBoolAndSupp_result_false {src : List BArg} (ak : BArg) :
    arrayBoolAndSupp src ak src.length false = anyCurF src := by
  unfold arrayBoolAndSupp
  simp

@[simp] theorem arrayBoolAndSupp_result_true {src : List BArg} (ak : BArg) :
    arrayBoolAndSupp src ak src.length true = allCurT src := by
  unfold arrayBoolAndSupp
  simp

/-- A target value at one operand position: the position, slot and value
to remove.  Turning targets into `BPrune` records keeps the prune shape
uniform and makes membership decoding cheap. -/
structure BTarget where
  pos : Nat
  slot : Nat
  val : Bool
  deriving Repr, DecidableEq

def BTarget.toPrune (args : List BArg) (t : BTarget) : BPrune :=
  { pos := t.pos
    slot := t.slot
    val := t.val
    lit := posBool t.slot (!t.val)
    reason := posBool t.slot (!t.val) :: BArgs.fixedLits args }

/-- Values with no closed-form support. -/
def arrayBoolAndTargets (src : List BArg) (ak : BArg) : List BTarget :=
  let allT := allCurT src
  let anyF := anyCurF src
  (List.range src.length).flatMap (fun p =>
      let a := src.getD p default
      (if a.curF && !ak.curF then
        [{ pos := p, slot := a.slot, val := false }]
       else []) ++
      (if a.curT && !((ak.curT && allT) || (ak.curF && anyOtherCurF src p)) then
        [{ pos := p, slot := a.slot, val := true }]
       else [])) ++
  (if ak.curF && !anyF then
    [{ pos := src.length, slot := ak.slot, val := false }]
   else []) ++
  (if ak.curT && !allT then
    [{ pos := src.length, slot := ak.slot, val := true }]
   else [])

/-- The closed-form prune list for `array_bool_and`. -/
def arrayBoolAndPrunesFast (src : List BArg) (ak : BArg) : List BPrune :=
  (arrayBoolAndTargets src ak).map (fun t => t.toPrune (src ++ [ak]))

/-- No satisfying Boolean tuple remains. -/
def arrayBoolAndConflict (src : List BArg) (ak : BArg) : Bool :=
  !((ak.curF && anyCurF src) || (ak.curT && allCurT src))

/-- View-independent closed-form plan for `array_bool_and`. -/
def arrayBoolAndPlanFast (src : List BArg) (ak : BArg) : BPlan :=
  if arrayBoolAndConflict src ak then
    { conflict? := some (BArgs.fixedLits (src ++ [ak])), prunes := [] }
  else
    { conflict? := none, prunes := arrayBoolAndPrunesFast src ak }

/-- Every generated target has a failing closed-form support test and
refers either to a source position or to the result position. -/
theorem mem_arrayBoolAndTargets_spec {src : List BArg} {ak : BArg}
    {t : BTarget} (h : t ∈ arrayBoolAndTargets src ak) :
    arrayBoolAndSupp src ak t.pos t.val = false ∧
      ((t.pos < src.length ∧ t.slot = (src.getD t.pos default).slot) ∨
       (t.pos = src.length ∧ t.slot = ak.slot)) := by
  unfold arrayBoolAndTargets at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at h
  rcases h with (⟨p, hp, h⟩ | h) | h
  · rcases h with h | h
    · by_cases hf : ((src.getD p default).curF &&
          !ak.curF) = true
      · rw [if_pos hf] at h
        simp only [List.mem_singleton] at h
        subst h
        refine ⟨?_, Or.inl ⟨hp, rfl⟩⟩
        rw [arrayBoolAndSupp_source_false hp]
        have := (Bool.and_eq_true_iff.mp hf).2
        rwa [Bool.not_eq_true'] at this
      · rw [if_neg hf] at h
        simp at h
    · by_cases ht : ((src.getD p default).curT &&
          !((ak.curT && allCurT src) ||
            (ak.curF && anyOtherCurF src p))) = true
      · rw [if_pos ht] at h
        simp only [List.mem_singleton] at h
        subst h
        refine ⟨?_, Or.inl ⟨hp, rfl⟩⟩
        rw [arrayBoolAndSupp_source_true hp]
        have := (Bool.and_eq_true_iff.mp ht).2
        rwa [Bool.not_eq_true'] at this
      · rw [if_neg ht] at h
        simp at h
  · by_cases hf : (ak.curF && !anyCurF src) = true
    · rw [if_pos hf] at h
      simp only [List.mem_singleton] at h
      subst h
      refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [arrayBoolAndSupp_result_false]
      have := (Bool.and_eq_true_iff.mp hf).2
      rwa [Bool.not_eq_true'] at this
    · rw [if_neg hf] at h
      simp at h
  · by_cases ht : (ak.curT && !allCurT src) = true
    · rw [if_pos ht] at h
      simp only [List.mem_singleton] at h
      subst h
      refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [arrayBoolAndSupp_result_true]
      have := (Bool.and_eq_true_iff.mp ht).2
      rwa [Bool.not_eq_true'] at this
    · rw [if_neg ht] at h
      simp at h

/-- Support-failure projection of `mem_arrayBoolAndTargets_spec`. -/
theorem arrayBoolAndSupp_of_mem_targets {src : List BArg} {ak : BArg}
    {t : BTarget} (h : t ∈ arrayBoolAndTargets src ak) :
    arrayBoolAndSupp src ak t.pos t.val = false :=
  (mem_arrayBoolAndTargets_spec h).1

/-- A target's prune has the standard complement-literal shape. -/
theorem mem_arrayBoolAndPrunesFast {src : List BArg} {ak : BArg} {bp : BPrune}
    (h : bp ∈ arrayBoolAndPrunesFast src ak) :
    ∃ t ∈ arrayBoolAndTargets src ak, bp = t.toPrune (src ++ [ak]) := by
  unfold arrayBoolAndPrunesFast at h
  rw [List.mem_map] at h
  obtain ⟨t, ht, hbp⟩ := h
  exact ⟨t, ht, hbp.symm⟩

/-- `getD` of an in-range index is a member. -/
theorem mem_getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α}
    (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- `getD` at a left index is unchanged by appending. -/
theorem getD_append_left {α : Type} {l₁ l₂ : List α} {i : Nat} {d : α}
    (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

/-- A failing `all id` on a Boolean list exposes a false element at an
index. -/
theorem exists_getD_false_of_all_false {l : List Bool} (h : l.all id = false) :
    ∃ i, i < l.length ∧ l.getD i false = false := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : x = false
      · exact ⟨0, by simp, by simpa using hx⟩
      · have hx' : x = true := by cases x <;> simp_all
        have hxs : xs.all id = false := by simpa [hx'] using h
        obtain ⟨i, hi, hget⟩ := ih hxs
        exact ⟨i + 1, by simpa using hi, by simpa using hget⟩

/-- Values of an appended operand list. -/
theorem valsOf_append_singleton (b : Assignment) (src : List BArg) (ak : BArg) :
    BArgs.valsOf b (src ++ [ak]) = BArgs.valsOf b src ++ [ak.valAt b] := by
  simp [BArgs.valsOf]

/-- Reading a source position from the appended value list. -/
theorem valsOf_append_getD_left {b : Assignment} {src : List BArg} {ak : BArg}
    {p : Nat} (hp : p < src.length) :
    (BArgs.valsOf b (src ++ [ak])).getD p false =
      (src.getD p default).valAt b := by
  rw [valsOf_append_singleton]
  rw [getD_append_left (l₁ := BArgs.valsOf b src) (l₂ := [ak.valAt b])
    (i := p) (d := false) (by simpa [BArgs.valsOf_length] using hp)]
  exact BArgs.valsOf_getD (by simpa [BArgs.valsOf_length] using hp)

/-- Reading the result position from the appended value list. -/
theorem valsOf_append_getD_right {b : Assignment} {src : List BArg} {ak : BArg} :
    (BArgs.valsOf b (src ++ [ak])).getD src.length false = ak.valAt b := by
  rw [valsOf_append_singleton, ← BArgs.valsOf_length b src]
  exact getD_append_singleton_self (BArgs.valsOf b src) (ak.valAt b)

/-- Forward support: if the assignment's values are current and satisfy
the `array_bool_and` relation, then the value at any operand position
passes the closed-form test.  This is the only semantic direction needed
for entailed reasons. -/
theorem arrayBoolAndSupp_of_vals {src : List BArg} {ak : BArg}
    {b : Assignment}
    (hcurSrc : ∀ a ∈ src, a.cur (a.valAt b) = true)
    (hcurAk : ak.cur (ak.valAt b) = true)
    (hrel : ak.valAt b = (BArgs.valsOf b src).all id)
    {pos : Nat} (hpos : pos < (src ++ [ak]).length) :
    arrayBoolAndSupp src ak pos
      ((BArgs.valsOf b (src ++ [ak])).getD pos false) = true := by
  by_cases hp : pos < src.length
  · rw [valsOf_append_getD_left hp]
    have hcurP := hcurSrc (src.getD pos default) (BArgs.getD_mem hp)
    by_cases hval : (src.getD pos default).valAt b = true
    · rw [hval, arrayBoolAndSupp_source_true hp]
      by_cases hak : ak.valAt b = true
      · have hallvals : (BArgs.valsOf b src).all id = true := by
          rw [← hrel, hak]
        have hallT : allCurT src = true := by
          rw [allCurT_eq_true]
          intro a ha
          have hva : a.valAt b = true :=
            List.all_eq_true.mp hallvals (a.valAt b)
              (List.mem_map_of_mem (f := fun a => a.valAt b) ha)
          have hca := hcurSrc a ha
          simpa [BArg.cur, hva] using hca
        have hcurT : ak.curT = true := by
          simpa [BArg.cur, hak] using hcurAk
        simp [hallT, hcurT]
      · have hakf : ak.valAt b = false := by simpa using hak
        have hcurF : ak.curF = true := by
          simpa [BArg.cur, hakf] using hcurAk
        have hrelf : (BArgs.valsOf b src).all id = false := by
          rw [← hrel, hakf]
        have hother : anyOtherCurF src pos = true := by
          rw [anyOtherCurF_eq_true]
          obtain ⟨q, hq, hqval⟩ := exists_getD_false_of_all_false hrelf
          have hqsrc : q < src.length := by
            simpa [BArgs.valsOf_length] using hq
          refine ⟨q, hqsrc, ?_, ?_⟩
          · have hqv : (src.getD q default).valAt b = false := by
              have hgd := BArgs.valsOf_getD (b := b) (args := src) (p := q) hqsrc
              rw [hqval] at hgd
              exact hgd.symm
            have hcq := hcurSrc (src.getD q default) (BArgs.getD_mem hqsrc)
            unfold BArg.cur at hcq
            rw [hqv] at hcq
            simpa using hcq
          · intro hqpos
            have hpv : (BArgs.valsOf b src).getD pos false = true := by
              have hgd := BArgs.valsOf_getD (b := b) (args := src) (p := pos) hp
              rw [hval] at hgd
              exact hgd
            rw [hqpos] at hqval
            rw [hpv] at hqval
            cases hqval
        simp [hcurF, hother]
    · have hvalf : (src.getD pos default).valAt b = false := by simpa using hval
      rw [hvalf, arrayBoolAndSupp_source_false hp]
      have hrelf : (BArgs.valsOf b src).all id = false := by
        cases hh : (BArgs.valsOf b src).all id with
        | false => rfl
        | true =>
            have hmem : (BArgs.valsOf b src).getD pos false ∈ BArgs.valsOf b src :=
              mem_getD_of_lt (by simpa [BArgs.valsOf_length] using hp)
            have hgd := List.all_eq_true.mp hh _ hmem
            have hpv : (BArgs.valsOf b src).getD pos false = false := by
              have hgd' := BArgs.valsOf_getD (b := b) (args := src) (p := pos) hp
              rw [hvalf] at hgd'
              exact hgd'
            rw [hpv] at hgd
            cases hgd
      have hrelak : ak.valAt b = false := by rw [hrel, hrelf]
      simpa [BArg.cur, hrelak] using hcurAk
  · have hpos' : pos = src.length := by
      have hlt : pos < src.length + 1 := by simpa using hpos
      omega
    subst hpos'
    rw [valsOf_append_getD_right]
    by_cases hak : ak.valAt b = true
    · rw [hak, arrayBoolAndSupp_result_true]
      have hallvals : (BArgs.valsOf b src).all id = true := by
        rw [← hrel, hak]
      rw [allCurT_eq_true]
      intro a ha
      have hva : a.valAt b = true :=
        List.all_eq_true.mp hallvals (a.valAt b)
          (List.mem_map_of_mem (f := fun a => a.valAt b) ha)
      have hca := hcurSrc a ha
      simpa [BArg.cur, hva] using hca
    · have hakf : ak.valAt b = false := by simpa using hak
      rw [hakf, arrayBoolAndSupp_result_false]
      have hrelf : (BArgs.valsOf b src).all id = false := by
        rw [← hrel, hakf]
      rw [anyCurF_eq_true]
      obtain ⟨q, hq, hqval⟩ := exists_getD_false_of_all_false hrelf
      have hqsrc : q < src.length := by
        simpa [BArgs.valsOf_length] using hq
      have hqv : (src.getD q default).valAt b = false := by
        have hgd := BArgs.valsOf_getD (b := b) (args := src) (p := q) hqsrc
        rw [hqval] at hgd
        exact hgd.symm
      have hcq := hcurSrc (src.getD q default) (BArgs.getD_mem hqsrc)
      refine ⟨src.getD q default, BArgs.getD_mem hqsrc, ?_⟩
      unfold BArg.cur at hcq
      rw [hqv] at hcq
      simpa using hcq

/-- A current member at the result position contradicts the conflict
flag. -/
theorem arrayBoolAndConflict_eq_false_of_supp {src : List BArg} {ak : BArg}
    {v : Bool} (hcur : ak.cur v = true)
    (h : arrayBoolAndSupp src ak src.length v = true) :
    arrayBoolAndConflict src ak = false := by
  cases v with
  | false =>
      rw [arrayBoolAndSupp_result_false] at h
      have hcur' : ak.curF = true := by simpa [BArg.cur] using hcur
      have hc : ((ak.curF && anyCurF src) || (ak.curT && allCurT src)) = true := by
        rw [h, hcur']
        simp
      unfold arrayBoolAndConflict
      rw [hc]
      rfl
  | true =>
      rw [arrayBoolAndSupp_result_true] at h
      have hcur' : ak.curT = true := by simpa [BArg.cur] using hcur
      have hc : ((ak.curF && anyCurF src) || (ak.curT && allCurT src)) = true := by
        rw [h, hcur']
        simp
      unfold arrayBoolAndConflict
      rw [hc]
      rfl

/-- Membership of an operand's fixed fact in the whole operand list's
fixed facts. -/
theorem fixedLits_of_mem_fixedLit {a : BArg} {args : List BArg}
    (ha : a ∈ args) : ∀ l ∈ a.fixedLit, l ∈ BArgs.fixedLits args := by
  induction args with
  | nil => simp at ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · intro l hl
        simp [BArgs.fixedLits, hl]
      · intro l hl
        simp only [BArgs.fixedLits, List.mem_append]
        exact Or.inr (ih ha l hl)

/-- Decode a failing complement literal into the removed Boolean value. -/
theorem valAt_eq_of_not_eval_posBool {b : Assignment} {a : BArg}
    (hbool : ∃ v, b[a.slot]? = some (.bool v)) {v : Bool}
    (h : (posBool a.slot (!v)).eval b ≠ some true) :
    a.valAt b = v := by
  have hf := BArg.eval_posBool_eq_false_of_not_true hbool h
  rw [eval_posBool_false_iff] at hf
  obtain ⟨x, hx, hne⟩ := hf
  have hx' : x = v := by
    cases v <;> cases x <;> simp_all
  subst hx'
  exact BArg.valAt_eq_of_some_bool hx

/-- Semantic support fact for `array_bool_and`: an accepted assignment
whose fixed facts are false reaches a current value that passes the
closed-form test, and the result operand is current. -/
theorem arrayBoolAndSupport_of_accepts
    (p : CompiledProblem DomConstraint) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (doms : Array DomC) (src : List BArg) (ak : BArg)
    (hargs : BArgs.ofSlots doms (is ++ [k]) = some (src ++ [ak]))
    (hinit : is.all (BArgs.initBoolB p) = true)
    {b : Assignment} (hb : b ∈ allAssigns p.domains)
    (hacc : accepts p b = true)
    (hfalse : ∀ l ∈ BArgs.fixedLits (src ++ [ak]), l.eval b = some false)
    {pos : Nat} (hpos : pos < (src ++ [ak]).length) :
    arrayBoolAndSupp src ak pos
        ((BArgs.valsOf b (src ++ [ak])).getD pos false) = true ∧
      ak.cur (ak.valAt b) = true := by
  have hspec := BArgs.arrayBoolAndR_spec p is k hmem doms (src ++ [ak])
    hargs (List.all_eq_true.mp hinit) b hb hacc
  have hlen : is.length = src.length := by
    have hmap := BArgs.ofSlots_map_slot hargs
    have := congrArg List.length hmap
    simp at this
    omega
  have hR : arrayBoolAndR src.length
      (BArgs.valsOf b (src ++ [ak])) = true := by
    simpa [hlen] using hspec.1
  have hrel : ak.valAt b = (BArgs.valsOf b src).all id := by
    have h := hR
    unfold arrayBoolAndR at h
    have hget := valsOf_append_getD_right (b := b) (src := src) (ak := ak)
    have htake : (BArgs.valsOf b (src ++ [ak])).take src.length =
        BArgs.valsOf b src := by
      rw [valsOf_append_singleton, ← BArgs.valsOf_length b src]
      simp
    rw [hget, htake] at h
    exact beq_iff_eq.mp h
  have hcurAll := BArgs.ofSlots_allCur hargs
  have hfalseArg : ∀ a ∈ src ++ [ak], ∀ l ∈ a.fixedLit,
      l.eval b = some false := by
    intro a ha l hl
    exact hfalse l (fixedLits_of_mem_fixedLit ha l hl)
  have hcurSrc : ∀ a ∈ src, a.cur (a.valAt b) = true := by
    intro a ha
    exact BArg.cur_valAt_of_fixedLits_false
      (hcurAll a (List.mem_append_left [ak] ha))
      (hfalseArg a (List.mem_append_left [ak] ha))
  have hcurAk : ak.cur (ak.valAt b) = true :=
    BArg.cur_valAt_of_fixedLits_false
      (hcurAll ak (by simp)) (hfalseArg ak (by simp))
  exact ⟨arrayBoolAndSupp_of_vals hcurSrc hcurAk hrel hpos, hcurAk⟩

/-- Runtime entry for the closed-form plan: parse sources and result once,
reject duplicate slots, then compute the fast plan. -/
def arrayBoolAndPlanOf (doms : Array DomC) (is : List Nat) (k : Nat) :
    Option (List BArg × BArg × BPlan) :=
  match BArgs.ofSlots doms is with
  | none => none
  | some src =>
      match BArg.mk? doms k with
      | none => none
      | some ak =>
          if BArgs.hasDupSlot (src ++ [ak]) then none
          else some (src, ak, arrayBoolAndPlanFast src ak)

theorem arrayBoolAndPlanOf_some {doms : Array DomC} {is : List Nat} {k : Nat}
    {src : List BArg} {ak : BArg} {plan : BPlan}
    (h : arrayBoolAndPlanOf doms is k = some (src, ak, plan)) :
    BArgs.ofSlots doms is = some src ∧ BArg.mk? doms k = some ak ∧
      BArgs.hasDupSlot (src ++ [ak]) = false ∧
      plan = arrayBoolAndPlanFast src ak := by
  unfold arrayBoolAndPlanOf at h
  split at h
  · cases h
  · rename_i src0 hsrc
    split at h
    · cases h
    · rename_i ak0 hak
      split at h
      · cases h
      · rename_i hd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hsrc, hak, by simpa using hd, rfl⟩

/-- Parsing sources and the result separately is the same as parsing the
appended slot list. -/
theorem ofSlots_append_singleton (is : List Nat) :
    ∀ {k : Nat} {doms : Array DomC} {src : List BArg} {ak : BArg},
      BArgs.ofSlots doms is = some src → BArg.mk? doms k = some ak →
      BArgs.ofSlots doms (is ++ [k]) = some (src ++ [ak]) := by
  induction is with
  | nil =>
      intro k doms src ak hsrc hak
      simp only [List.nil_append, BArgs.ofSlots] at hsrc ⊢
      injection hsrc with hsrc'
      subst hsrc'
      simp [hak]
  | cons s ss ih =>
      intro k doms src ak hsrc hak
      simp only [List.cons_append, BArgs.ofSlots] at hsrc ⊢
      cases hm : BArg.mk? doms s with
      | none => rw [hm] at hsrc; cases hsrc
      | some a =>
          rw [hm] at hsrc
          cases hr : BArgs.ofSlots doms ss with
          | none => rw [hr] at hsrc; cases hsrc
          | some rest =>
              rw [hr] at hsrc
              injection hsrc with hsrc'
              subst hsrc'
              rw [ih hr hak]
              simp

/-- Conflict clause of the closed-form plan is entailed. -/
theorem arrayBoolAndPlanFast_conflict_entailed
    (p : CompiledProblem DomConstraint) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (doms : Array DomC) (src : List BArg) (ak : BArg)
    (hargs : BArgs.ofSlots doms (is ++ [k]) = some (src ++ [ak]))
    (hinit : is.all (BArgs.initBoolB p) = true)
    {ls : List Literal}
    (hls : (arrayBoolAndPlanFast src ak).conflict? = some ls) :
    Entailed p ls := by
  intro b hb hacc
  by_cases hsat : Clause.SatisfiedBy ls b
  · exact hsat
  · exfalso
    by_cases hconf : arrayBoolAndConflict src ak = true
    · have hls' : BArgs.fixedLits (src ++ [ak]) = ls := by
        simpa [arrayBoolAndPlanFast, hconf] using hls
      subst hls'
      have htail : ∀ l ∈ BArgs.fixedLits (src ++ [ak]), l.eval b ≠ some true := by
        intro l hl htrue
        exact hsat ⟨l, hl, htrue⟩
      have hspec := BArgs.arrayBoolAndR_spec p is k hmem doms (src ++ [ak])
        hargs (List.all_eq_true.mp hinit) b hb hacc
      have hfalse := BArgs.fixedLits_false_of_not_true hspec.2 htail
      have hs := arrayBoolAndSupport_of_accepts p is k hmem doms src ak
        hargs hinit hb hacc hfalse (pos := src.length) (by simp)
      have hsupp : arrayBoolAndSupp src ak src.length (ak.valAt b) = true := by
        rw [← valsOf_append_getD_right (b := b) (src := src) (ak := ak)]
        exact hs.1
      have hcf := arrayBoolAndConflict_eq_false_of_supp hs.2 hsupp
      rw [hcf] at hconf
      cases hconf
    · simp [arrayBoolAndPlanFast, hconf] at hls

/-- Every prune reason of the closed-form plan is entailed. -/
theorem arrayBoolAndPlanFast_prunes_entailed
    (p : CompiledProblem DomConstraint) (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints)
    (doms : Array DomC) (src : List BArg) (ak : BArg)
    (hargs : BArgs.ofSlots doms (is ++ [k]) = some (src ++ [ak]))
    (hinit : is.all (BArgs.initBoolB p) = true)
    {q : BPrune} (hq : q ∈ (arrayBoolAndPlanFast src ak).prunes) :
    Entailed p q.reason := by
  intro b hb hacc
  by_cases hsat : Clause.SatisfiedBy q.reason b
  · exact hsat
  · exfalso
    by_cases hconf : arrayBoolAndConflict src ak = true
    · simp [arrayBoolAndPlanFast, hconf] at hq
    · have hpr : (arrayBoolAndPlanFast src ak).prunes =
          arrayBoolAndPrunesFast src ak := by
        simp [arrayBoolAndPlanFast, hconf]
      have hq' : q ∈ arrayBoolAndPrunesFast src ak := by rwa [hpr] at hq
      obtain ⟨t, ht, rfl⟩ := mem_arrayBoolAndPrunesFast hq'
      have htspec := mem_arrayBoolAndTargets_spec ht
      have hhead : (posBool t.slot (!t.val)).eval b ≠ some true := by
        intro htrue
        exact hsat ⟨_, by simp [BTarget.toPrune], htrue⟩
      have htail : ∀ l ∈ BArgs.fixedLits (src ++ [ak]), l.eval b ≠ some true := by
        intro l hl htrue
        exact hsat ⟨l, by simp [BTarget.toPrune, hl], htrue⟩
      have hspec := BArgs.arrayBoolAndR_spec p is k hmem doms (src ++ [ak])
        hargs (List.all_eq_true.mp hinit) b hb hacc
      have hfalse := BArgs.fixedLits_false_of_not_true hspec.2 htail
      have hboolArg : ∃ v, b[t.slot]? = some (.bool v) := by
        rcases htspec.2 with ⟨hlt, hslot⟩ | ⟨_heq, hslot⟩
        · have hb' := hspec.2 (src.getD t.pos default)
            (List.mem_append_left [ak] (BArgs.getD_mem hlt))
          simpa [hslot] using hb'
        · have hb' := hspec.2 ak (by simp)
          simpa [hslot] using hb'
      have hposArgs : t.pos < (src ++ [ak]).length := by
        rcases htspec.2 with ⟨hlt, _⟩ | ⟨heq, _⟩
        · simp [List.length_append]; omega
        · simp [List.length_append]; omega
      have hget : (BArgs.valsOf b (src ++ [ak])).getD t.pos false = t.val := by
        rcases htspec.2 with ⟨hlt, hslot⟩ | ⟨heq, hslot⟩
        · have hbarg : ∃ v, b[(src.getD t.pos default).slot]? =
              some (.bool v) := by
            simpa [hslot] using hboolArg
          have hhead' : (posBool (src.getD t.pos default).slot (!t.val)).eval b
              ≠ some true := by
            simpa [hslot] using hhead
          have hva := valAt_eq_of_not_eval_posBool hbarg hhead'
          rw [valsOf_append_getD_left hlt, hva]
        · rw [heq]
          have hbarg : ∃ v, b[ak.slot]? = some (.bool v) := by
            simpa [hslot] using hboolArg
          have hhead' : (posBool ak.slot (!t.val)).eval b ≠ some true := by
            simpa [hslot] using hhead
          have hva := valAt_eq_of_not_eval_posBool hbarg hhead'
          rw [valsOf_append_getD_right, hva]
      have hs := arrayBoolAndSupport_of_accepts p is k hmem doms src ak
        hargs hinit hb hacc hfalse hposArgs
      have hsupp := hs.1
      rw [hget] at hsupp
      rw [htspec.1] at hsupp
      cases hsupp

/-- Certified closed-form `array_bool_and` propagator.  It parses the
sources and the result separately (avoiding a second `ofSlots` pass and
the exponential truth-table enumerator), rejects duplicate slots, and
uses the closed-form plan when the initial source domains are Boolean. -/
def arrayBoolAndPropFast (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (k : Nat)
    (hmem : DomConstraint.arrayBoolAndSlot is k ∈ p.constraints) : PropV2 p T :=
  let ready := is.all (BArgs.initBoolB p)
  { vars := (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)).toArray
    events := (dcSlotsFull (DomConstraint.arrayBoolAndSlot is k)).toArray.map
      fun s => (s, .fix)
    run := fun view =>
      if hguard : ready = true then
        match hplan : arrayBoolAndPlanOf view.doms is k with
        | none => .fix
        | some (src, ak, plan) =>
            have hargs := ofSlots_append_singleton is
              (arrayBoolAndPlanOf_some hplan).1
              (arrayBoolAndPlanOf_some hplan).2.1
            have hplanEq : plan = arrayBoolAndPlanFast src ak :=
              (arrayBoolAndPlanOf_some hplan).2.2.2
            BPlan.out p T plan
              (fun ls hls =>
                arrayBoolAndPlanFast_conflict_entailed p is k hmem view.doms
                  src ak hargs hguard (hplanEq ▸ hls))
              (fun q hq =>
                arrayBoolAndPlanFast_prunes_entailed p is k hmem view.doms
                  src ak hargs hguard (hplanEq ▸ hq))
      else .fix }

end LeanFzn.Engine

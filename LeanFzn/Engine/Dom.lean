/-
File: LeanFzn/Engine/Dom.lean

Compact-domain operations for Core, with their denotation against the
compiled `Dom`.  The representation is the frozen `DomC` from
`LeanFzn/Engine/Types.lean`; nothing here enumerates a wide `.bounds` or
`.bitset` domain on the hot path.  Entry conversion (`ofDom?`) and the
membership/fit bridges are proved in this module (N3).
-/
import LeanFzn.Engine.Bits
import LeanFzn.Engine.Types
import LeanFzn.Solver.Propagation.EngineCore

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Basic bit helpers -/

/-! The set-bit scans `lowestBit`/`highestBit`, `u64bit`, and their
specifications live in `LeanFzn.Engine.Bits`; this module re-exports them
through the import above. -/

/-- Population count of a 64-bit word (SWAR). -/
def popcount64 (x : UInt64) : Nat :=
  let x := x - ((x >>> (1 : UInt64)) &&& (0x5555555555555555 : UInt64))
  let x := (x &&& (0x3333333333333333 : UInt64)) +
    ((x >>> (2 : UInt64)) &&& (0x3333333333333333 : UInt64))
  let x := (x + (x >>> (4 : UInt64))) &&& (0x0F0F0F0F0F0F0F0F : UInt64)
  ((x * (0x0101010101010101 : UInt64)) >>> (56 : UInt64)).toNat

def u64maskLe (k : Nat) : UInt64 :=
  if k ≥ 63 then (0xFFFFFFFFFFFFFFFF : UInt64)
  else ((1 : UInt64) <<< (UInt64.ofNat (k + 1))) - 1

/-! ## Emptiness and canonical empty -/

/-- The canonical empty domain. -/
def DomC.empty : DomC := .bounds 1 0

def DomC.isEmpty : DomC → Bool
  | .bool bits => bits &&& 3 == 0
  | .bounds lo hi => decide (hi < lo)
  | .bitset _ words => words.all (fun w => w == 0)
  | .boundsHoles lo hi _ => decide (hi < lo)
  | .sparse values => values.isEmpty

/-! ## Membership -/

/-- Binary search over the index window `[lo, hi)` of a hole array, with an
    explicit fuel that bounds the window length.  `fuel` is always at least
    `hi - lo` at the initial call; the public `memHoleRange` passes
    `holes.size`.  Keeping the accumulation parameter separate lets the
    correctness proof be a plain structural induction on `fuel`. -/
private def memHoleRangeGo (holes : Array Int) (v : Int) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match holes[mid]? with
        | some h =>
            if h == v then true
            else if h < v then memHoleRangeGo holes v fuel (mid + 1) hi
            else memHoleRangeGo holes v fuel lo mid
        | none => false
      else false

/-- Binary search in the sorted hole array. -/
def memHoleRange (holes : Array Int) (v : Int) : Bool :=
  memHoleRangeGo holes v holes.size 0 holes.size

/-- Membership test of `n` in a little-endian array of 64-bit words:
    bit `64*w + k` of `words[w]` is bit `k` of word `w`.  The test uses a
    direct 64-bit mask (no `Nat.testBit` conversion) on the hot path. -/
def bitsetMem (words : Array UInt64) (n : Nat) : Bool :=
  match words[n / 64]? with
  | some word => (word &&& u64bit (n % 64)) != 0
  | none => false

/-- Integer membership of a compact domain. -/
def DomC.mem : DomC → Value → Bool
  | .bool bits, .bool b => (bits &&& (if b then 2 else 1)) != 0
  | .bounds lo hi, .int v => decide (lo ≤ v) && decide (v ≤ hi)
  | .bitset lo words, .int v =>
      let k := v - lo
      if k < 0 then false else bitsetMem words k.toNat
  | .boundsHoles lo hi holes, .int v =>
      decide (lo ≤ v) && decide (v ≤ hi) && !(memHoleRange holes v)
  | .sparse values, .int v => memHoleRange values v
  | _, _ => false

/-- Integer-view membership: Booleans count as 0/1, and no other integer
    belongs to a Boolean domain. -/
def DomC.memIntView (d : DomC) (v : Int) : Bool :=
  match d with
  | .bool _ =>
      if v == 0 then d.mem (.bool false)
      else if v == 1 then d.mem (.bool true)
      else false
  | _ => d.mem (.int v)

/-- `true` when the compact domain carries integer values rather than
Booleans.  Order literals are only used on these domains. -/
def DomC.intKindB : DomC → Bool
  | .bool _ => false
  | _ => true

/-- An integer-kind compact domain has only integer members.  This is the
kind bridge used by Hall-interval explanations. -/
theorem DomC.mem_int_of_intKindB {d : DomC} (hk : d.intKindB = true)
    {v : Value} (hm : d.mem v = true) : ∃ i, v = .int i := by
  cases d with
  | bool _ => simp [DomC.intKindB] at hk
  | bounds lo hi =>
      cases v with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt xs => simp [DomC.mem] at hm
      | array xs => simp [DomC.mem] at hm
  | bitset lo words =>
      cases v with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt xs => simp [DomC.mem] at hm
      | array xs => simp [DomC.mem] at hm
  | boundsHoles lo hi holes =>
      cases v with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt xs => simp [DomC.mem] at hm
      | array xs => simp [DomC.mem] at hm
  | sparse values =>
      cases v with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt xs => simp [DomC.mem] at hm
      | array xs => simp [DomC.mem] at hm

/-- First element of an array, if nonempty. -/
def arrayHead? (a : Array Int) : Option Int :=
  if h : 0 < a.size then some (a[0]'h) else none

/-- Last element of an array, if nonempty. -/
def arrayLast? (a : Array Int) : Option Int :=
  if h : 0 < a.size then some (a[a.size - 1]'(by omega)) else none

/-! ## Lo/hi and fixed values -/

def DomC.lo? : DomC → Option Int
  | .bool bits =>
      if (bits &&& 1) != 0 then some 0
      else if (bits &&& 2) != 0 then some 1 else none
  | .bounds lo hi => if decide (hi < lo) then none else some lo
  | .bitset lo words =>
      let rec goLo (i : Nat) : Option Int :=
        if h : i < words.size then
          match words[i]? with
          | some w => if w == 0 then goLo (i + 1) else some (lo + (i * 64 + lowestBit w : Nat))
          | none => none
        else none
      termination_by words.size - i
      goLo 0
  | .boundsHoles lo hi holes =>
      if decide (hi < lo) then none
      else
        let rec goHoleLo (v : Int) (k : Nat) : Option Int :=
          if hk : k < holes.size then
            match holes[k]? with
            | some h => if h == v then goHoleLo (v + 1) (k + 1) else some v
            | none => some v
          else if v ≤ hi then some v else none
        termination_by holes.size - k
        goHoleLo lo 0
  | .sparse values => arrayHead? values

/-- Highest member of a bit-set domain, scanning the words from the top.
    The forward scan in `hi?` walks every word even when the top word is
    nonempty; this twin stops at the first nonzero word. -/
def bitsetHiGo (lo : Int) (words : Array UInt64) : Option Int :=
  match h : words.back? with
  | none => none
  | some w =>
      if w == 0 then bitsetHiGo lo words.pop
      else some (lo + (((words.size - 1) * 64 + highestBit w : Nat) : Int))
termination_by words.size
decreasing_by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 h
  simp [Array.size_pop]

def DomC.hi? : DomC → Option Int
  | .bool bits =>
      if (bits &&& 2) != 0 then some 1
      else if (bits &&& 1) != 0 then some 0 else none
  | .bounds lo hi => if decide (hi < lo) then none else some hi
  | .bitset lo words =>
      let rec goHi (i : Nat) (acc : Option Int) : Option Int :=
        if h : i < words.size then
          match words[i]? with
          | some w =>
              if w == 0 then goHi (i + 1) acc
              else goHi (i + 1) (some (lo + (i * 64 + highestBit w : Nat)))
          | none => acc
        else acc
      termination_by words.size - i
      goHi 0 none
  | .boundsHoles lo hi holes =>
      if decide (hi < lo) then none
      else
        let rec goHoleHi (v : Int) (k : Nat) : Option Int :=
          if hk : k < holes.size then
            match holes[holes.size - 1 - k]? with
            | some h => if h == v then goHoleHi (v - 1) (k + 1) else some v
            | none => some v
          else if lo ≤ v then some v else none
        termination_by holes.size - k
        goHoleHi hi 0
  | .sparse values => arrayLast? values

private theorem goHi_push (lo : Int) (xs : Array UInt64) (w : UInt64) :
    ∀ (i : Nat) (acc : Option Int), i ≤ xs.size →
      DomC.hi?.goHi lo (xs.push w) i acc =
        if w == 0 then DomC.hi?.goHi lo xs i acc
        else some (lo + (((xs.size * 64 + highestBit w : Nat)) : Int)) := by
  intro i
  induction h : (xs.size - i) using Nat.strongRecOn generalizing i with
  | ind m ih =>
    intro acc hi
    by_cases hlt : i < xs.size
    · have hsize : i < (xs.push w).size := by simp [Array.size_push]; omega
      rw [DomC.hi?.goHi.eq_1, dif_pos hsize]
      rw [Array.getElem?_push_lt hlt]
      simp only
      by_cases hw : (xs[i]'hlt == 0) = true
      · simp only [if_pos hw]
        conv => rhs; rw [DomC.hi?.goHi.eq_1, dif_pos hlt,
          Array.getElem?_eq_some_getElem xs i hlt]
        simp only [if_pos hw]
        exact ih (xs.size - (i + 1)) (by omega) (i + 1) (by omega) acc (by omega)
      · simp only [if_neg hw]
        conv => rhs; rw [DomC.hi?.goHi.eq_1, dif_pos hlt,
          Array.getElem?_eq_some_getElem xs i hlt]
        simp only [if_neg hw]
        exact ih (xs.size - (i + 1)) (by omega) (i + 1) (by omega) _ (by omega)
    · have hieq : i = xs.size := by omega
      subst hieq
      have hsize : xs.size < (xs.push w).size := by simp [Array.size_push]
      conv => lhs; rw [DomC.hi?.goHi.eq_1, dif_pos hsize, Array.getElem?_push_size]
      simp only
      by_cases hw : (w == 0) = true
      · simp only [if_pos hw]
        conv => lhs; rw [DomC.hi?.goHi.eq_1, dif_neg (by simp [Array.size_push])]
        conv => rhs; rw [DomC.hi?.goHi.eq_1, dif_neg (by simp [Array.size_push])]
      · simp only [if_neg hw]
        conv => lhs; rw [DomC.hi?.goHi.eq_1, dif_neg (by simp [Array.size_push])]

private theorem bitsetHiGo_push (lo : Int) (xs : Array UInt64) (w : UInt64) :
    bitsetHiGo lo (xs.push w) =
      if w == 0 then bitsetHiGo lo xs
      else some (lo + (((xs.size * 64 + highestBit w : Nat)) : Int)) := by
  conv => lhs; rw [bitsetHiGo.eq_1]
  rw [Array.back?_push]
  simp only
  by_cases hw : (w == 0) = true
  · simp only [if_pos hw, Array.pop_push]
  · simp only [if_neg hw, Array.size_push, Nat.add_sub_cancel]

private theorem bitsetHiGo_eq_goHi (lo : Int) (words : Array UInt64) :
    bitsetHiGo lo words = DomC.hi?.goHi lo words 0 none := by
  let P (n : Nat) := ∀ (words : Array UInt64), words.size = n →
    bitsetHiGo lo words = DomC.hi?.goHi lo words 0 none
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro words hn
      by_cases h0 : words.size = 0
      · have hempty : words = #[] := Array.eq_empty_of_size_eq_zero h0
        subst hempty
        conv => lhs; rw [bitsetHiGo.eq_1]
        rw [DomC.hi?.goHi.eq_1, dif_neg (by simp)]
        rfl
      · obtain ⟨xs, w, rfl⟩ := Array.eq_push_of_size_ne_zero h0
        rw [bitsetHiGo_push, goHi_push lo xs w 0 none (by omega)]
        rw [ih xs.size (by simp [Array.size_push] at hn ⊢; omega) xs rfl]
  exact hP words.size words rfl

/-- Compiled-code twin of `hi?`: the bitset branch scans downward. -/
def DomC.hiFast (d : DomC) : Option Int :=
  match d with
  | .bitset lo words => bitsetHiGo lo words
  | _ => DomC.hi? d

theorem DomC.hiFast_eq (d : DomC) : d.hiFast = d.hi? := by
  cases d with
  | bool bits => rfl
  | bounds lo hi => rfl
  | bitset lo words => exact bitsetHiGo_eq_goHi lo words
  | boundsHoles lo hi holes => rfl
  | sparse values => rfl

@[csimp] theorem DomC.hi?_eq_fast : @DomC.hi? = @DomC.hiFast := by
  funext d
  exact (DomC.hiFast_eq d).symm

def DomC.fixedValue : DomC → Option Value
  | .bool bits =>
      match bits &&& 3 with
      | 1 => some (.bool false)
      | 2 => some (.bool true)
      | _ => none
  | .bounds lo hi => if lo == hi then some (.int lo) else none
  | .bitset lo words =>
      match DomC.lo? (.bitset lo words), DomC.hi? (.bitset lo words) with
      | some a, some b => if a == b then some (.int a) else none
      | _, _ => none
  | .boundsHoles lo hi holes =>
      match DomC.lo? (.boundsHoles lo hi holes),
            DomC.hi? (.boundsHoles lo hi holes) with
      | some a, some b => if a == b then some (.int a) else none
      | _, _ => none
  | .sparse values =>
      match arrayHead? values, arrayLast? values with
      | some lo, some hi => if lo == hi then some (.int lo) else none
      | _, _ => none

/-! ## Size -/

def DomC.size : DomC → Nat
  | .bool bits => popcount64 (UInt64.ofNat (bits &&& 3).toNat)
  | .bounds lo hi => if hi < lo then 0 else (hi - lo + 1).toNat
  | .bitset _ words => words.foldl (fun acc w => acc + popcount64 w) 0
  | .boundsHoles lo hi holes =>
      if hi < lo then 0
      else ((hi - lo + 1).toNat - holes.size)
  | .sparse values => values.size

def DomC.isFixed (d : DomC) : Bool := d.size == 1

/-! ## Restriction operations -/

def DomC.setLe : DomC → Int → DomC
  | .bool bits, k =>
      if k < 0 then .bool 0
      else if k == 0 then .bool (bits &&& 1)
      else .bool (bits &&& 3)
  | .bounds lo hi, k => .bounds lo (if k < hi then k else hi)
  | .bitset lo words, k =>
      if k < lo then .bounds 1 0
      else
        let width := (k - lo).toNat
        let wi := width / 64
        let bi := width % 64
        let kept := words.extract 0 (if wi < words.size then wi + 1 else words.size)
        if kept.isEmpty then .bounds 1 0
        else
          let last := if wi < kept.size then kept[wi]! &&& u64maskLe bi else kept[kept.size - 1]!
          let kept := if wi < kept.size then kept.set! wi last else kept
          if kept.isEmpty then .bounds 1 0 else .bitset lo kept
  | .boundsHoles lo hi holes, k =>
      let hi' := if k < hi then k else hi
      if hi' < lo then .bounds 1 0
      else .boundsHoles lo hi' (holes.filter (fun h => decide (h ≤ hi')))
  | .sparse values, k =>
      .sparse (values.filter (fun v => decide (v ≤ k)))

def DomC.setGe : DomC → Int → DomC
  | .bool bits, k =>
      if k > 1 then .bool 0
      else if k == 1 then .bool (bits &&& 2)
      else .bool (bits &&& 3)
  | .bounds lo hi, k => .bounds (if lo < k then k else lo) hi
  | .bitset lo words, k =>
      if (DomC.hi? (.bitset lo words)).isNone then .bounds 1 0
      else
        let lo' := if lo < k then k else lo
        let diff := (lo' - lo).toNat
        let wi := diff / 64
        let bi := diff % 64
        let kept :=
          if wi ≥ words.size then #[] else words.extract wi words.size
        if kept.isEmpty then .bounds 1 0
        else
          let first := kept[0]! &&& (if bi == 0 then (0xFFFFFFFFFFFFFFFF : UInt64)
            else (0xFFFFFFFFFFFFFFFF : UInt64) <<< (UInt64.ofNat bi))
          let kept := kept.set! 0 first
          -- Dropping the leading words moves the window start to the
          -- 64-bit boundary below `k`; keep that as the new offset so the
          -- remaining bit positions still denote their original values.
          let base := lo + (wi * 64 : Nat)
          if kept.all (fun w => w == 0) then .bounds 1 0 else .bitset base kept
  | .boundsHoles lo hi holes, k =>
      let lo' := if lo < k then k else lo
      if hi < lo' then .bounds 1 0
      else .boundsHoles lo' hi (holes.filter (fun h => decide (lo' ≤ h)))
  | .sparse values, k =>
      .sparse (values.filter (fun v => decide (k ≤ v)))

/-- Insert `v` into a sorted hole array. -/
def insertHole (holes : Array Int) (v : Int) : Array Int :=
  let rec go (i : Nat) (acc : Array Int) : Array Int :=
    if h : i < holes.size then
      match holes[i]? with
      | some hval =>
          if hval == v then acc ++ holes.extract i holes.size
          else if v < hval then acc ++ #[v] ++ holes.extract i holes.size
          else go (i + 1) (acc.push hval)
      | none => acc
    else acc.push v
  termination_by holes.size - i
  go 0 #[]

def DomC.remove : DomC → Value → DomC
  | .bool bits, .bool b =>
      let mask : UInt8 := if b then 0xFD else 0xFE
      .bool (bits &&& mask)
  | .bounds lo hi, .int v =>
      if v < lo || hi < v then .bounds lo hi
      else if v == lo then .bounds (lo + 1) hi
      else if v == hi then .bounds lo (hi - 1)
      else .boundsHoles lo hi #[v]
  | .bitset lo words, .int v =>
      let k := v - lo
      if k < 0 then .bitset lo words
      else
        let n := k.toNat
        let wi := n / 64
        let bi := n % 64
        match words[wi]? with
        | some w => .bitset lo (words.set! wi (w &&& ~~~(u64bit bi)))
        | none => .bitset lo words
  | .boundsHoles lo hi holes, .int v =>
      if v < lo || hi < v then .boundsHoles lo hi holes
      else if memHoleRange holes v then .boundsHoles lo hi holes
      else if v == lo then .boundsHoles (lo + 1) hi holes
      else if v == hi then .boundsHoles lo (hi - 1) holes
      else .boundsHoles lo hi (insertHole holes v)
  | .sparse values, .int v =>
      .sparse (values.filter (fun x => decide (x ≠ v)))
  | d, _ => d

def DomC.removeIntView (d : DomC) (v : Int) : DomC :=
  match d with
  | .bool _ =>
      if v == 0 then d.remove (.bool false)
      else if v == 1 then d.remove (.bool true)
      else d
  | _ => d.remove (.int v)

def DomC.fix : DomC → Value → DomC
  | d, v =>
      if d.mem v then
        match v with
        | .bool b => .bool (if b then 2 else 1)
        | .int i => .bounds i i
        | _ => .bounds 1 0
      else .bounds 1 0

def DomC.fixIntView (d : DomC) (v : Int) : DomC :=
  match d with
  | .bool _ =>
      if v == 0 then d.fix (.bool false)
      else if v == 1 then d.fix (.bool true)
      else .bounds 1 0
  | _ => d.fix (.int v)

/-! ## Literal evaluation and application -/

/-- The value of a literal on a compact domain: `some true` when the
    literal holds on every value, `some false` when it holds on none, and
    `none` when the domain straddles it.  The sign of the atom matters:
    `negLe k` is `x > k`, `negNe v` is `x = v`, and a negated Boolean pin
    is the opposite pin. -/
def DomC.evalLit (d : DomC) (l : Literal) : Option Bool :=
  match l.atom with
  | .intNe _ v =>
      if d.fixedValue.isSome then
        some (if l.positive then !(d.memIntView v) else d.memIntView v)
      else if !(d.memIntView v) then some l.positive
      else none
  | .intLe _ k =>
      match DomC.lo? d, DomC.hi? d with
      | some lo, some hi =>
          if l.positive then
            if hi ≤ k then some true else if lo > k then some false else none
          else
            if lo > k then some true else if hi ≤ k then some false else none
      | _, _ => none
  | .boolEq _ b =>
      match d.fixedValue with
      | some (.bool actual) => some (if l.positive then actual == b else actual != b)
      | _ => none

/-- A cheap falsity test, equivalent to `evalLit l = some false` but
    computing only the endpoint that the literal needs: a positive
    `intLe` only reads the lower bound, a negative `intLe` only the upper
    bound, and a negative `intNe` only membership.  (A positive `intNe`
    needs to know whether the domain is fixed; it then reads membership.)
    This is the hot-path replacement for `evalLit` in explanation search,
    where the upper endpoint of a bitset would otherwise be scanned for
    every positive `posLe` literal. -/
def DomC.falsifiesLit (d : DomC) (l : Literal) : Bool :=
  match l.atom with
  | .intNe _ v =>
      if l.positive then
        match d.fixedValue with
        | some _ => d.memIntView v
        | none => false
      else !(d.memIntView v)
  | .intLe _ k =>
      if l.positive then
        match d.lo? with
        | some lo =>
            if k < lo then
              match d.hi? with
              | some hi => decide (k < hi)
              | none => false
            else false
        | none => false
      else
        match d.hi? with
        | some hi =>
            if hi ≤ k then
              match d.lo? with
              | some lo => decide (lo ≤ k)
              | none => false
            else false
        | none => false
  | .boolEq _ b =>
      match d.fixedValue with
      | some (.bool actual) =>
          !(if l.positive then actual == b else actual != b)
      | _ => false

/-- `falsifiesLit` is exactly the falsity case of `evalLit`.  The theorem
    is purely structural: it needs no well-formedness hypothesis, because
    both predicates read the same `lo?`/`hi?`/`fixedValue` results. -/
theorem DomC.falsifiesLit_eq (d : DomC) (l : Literal) :
    d.falsifiesLit l = true ↔ d.evalLit l = some false := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intNe s v =>
      cases pos <;>
        simp only [DomC.falsifiesLit, DomC.evalLit] <;>
        (cases hf : d.fixedValue <;> simp [hf])
  | intLe s k =>
      cases pos
      · simp only [DomC.falsifiesLit, DomC.evalLit]
        cases hlo : d.lo? with
        | none =>
            cases hhi : d.hi? <;> simp [hlo, hhi]
        | some lo =>
            cases hhi : d.hi? with
            | none => simp [hlo, hhi]
            | some hi =>
                by_cases hq : k < lo
                · by_cases hp : k < hi
                  · have h1 : ¬ hi ≤ k := by omega
                    have h2 : lo > k := by omega
                    simp [hlo, hhi, hq, hp, h1, h2]
                  · have h1 : hi ≤ k := by omega
                    simp [hlo, hhi, hq, hp, h1]
                · have h2 : ¬ lo > k := by omega
                  by_cases hp : hi ≤ k <;> simp [hlo, hhi, hq, h2, hp] <;> omega
      · simp only [DomC.falsifiesLit, DomC.evalLit]
        cases hlo : d.lo? with
        | none =>
            cases hhi : d.hi? <;> simp [hlo, hhi]
        | some lo =>
            cases hhi : d.hi? with
            | none => simp [hlo, hhi]
            | some hi =>
                by_cases h1 : hi ≤ k
                · by_cases h2 : lo ≤ k
                  · have h3 : ¬ lo > k := by omega
                    simp [hlo, hhi, h1, h2, h3]
                  · have h3 : lo > k := by omega
                    simp [hlo, hhi, h1, h2, h3]
                · have h1' : ¬ hi ≤ k := by omega
                  by_cases h3 : lo > k <;> simp [hlo, hhi, h1, h1', h3] <;> omega
  | boolEq s b =>
      cases pos
      · simp only [DomC.falsifiesLit, DomC.evalLit]
        cases hf : d.fixedValue with
        | none => simp [hf]
        | some v =>
            cases v with
            | bool actual => simp [hf]
            | int i => simp [hf]
            | setOfInt xs => simp [hf]
            | array xs => simp [hf]
      · simp only [DomC.falsifiesLit, DomC.evalLit]
        cases hf : d.fixedValue with
        | none => simp [hf]
        | some v =>
            cases v with
            | bool actual => simp [hf]
            | int i => simp [hf]
            | setOfInt xs => simp [hf]
            | array xs => simp [hf]

/-- Apply a literal to a compact domain.  The result may be empty. -/
def DomC.applyLit (d : DomC) (l : Literal) : DomC :=
  match l.atom with
  | .intNe _ v => if l.positive then d.removeIntView v else d.fixIntView v
  | .intLe _ k => if l.positive then d.setLe k else d.setGe (k + 1)
  | .boolEq _ b => d.fix (.bool (if l.positive then b else !b))

/-! ## Entry conversion -/

/-- Insert `v` into a strictly ascending list, keeping it strictly ascending
    and dropping the duplicate when `v` is already present.  Membership of
    other values is unchanged. -/
def insertSortedInt (v : Int) : List Int → List Int
  | [] => [v]
  | x :: xs =>
      if v == x then x :: xs
      else if v < x then v :: x :: xs
      else x :: insertSortedInt v xs

/-- Verified insertion sort with duplicate removal.  Entry-only; the
    standard library has no membership lemmas for `Array.qsort`, so the
    entry conversion uses this definition instead. -/
def sortUniqueInts : List Int → List Int
  | [] => []
  | x :: xs => insertSortedInt x (sortUniqueInts xs)

/-- Sorted, duplicate-free form of an integer array (entry only). -/
def sortedUniqueInts (a : Array Int) : Array Int := (sortUniqueInts a.toList).toArray

/-- The complement of `vs` inside `[lo, hi]`, ascending.  `vs` is expected
    strictly ascending with all elements in `[lo, hi]`; the result is exactly
    the set of values of `[lo, hi]` missing from `vs`.  Entry only: the scan
    is guarded by the caller so the span stays small. -/
def complementHoles (lo hi : Int) (vs : Array Int) : Array Int :=
  ((List.range (hi - lo + 1).toNat).filterMap (fun (k : Nat) =>
    if memHoleRange vs (lo + (k : Int)) then none
    else some (lo + (k : Int)))).toArray

/-! ### Multi-word bitset construction (entry only) -/

/-- Number of 64-bit words needed for `span` bits. -/
def bitsetWordCount (span : Nat) : Nat := (span + 63) / 64

/-- Set bit `k` in a little-endian word array, when its word exists. -/
def setBitWord (words : Array UInt64) (k : Nat) : Array UInt64 :=
  let wi := k / 64
  if h : wi < words.size then
    words.set! wi (words[wi]! ||| u64bit (k % 64))
  else words

/-- Multi-word bitset for the given values relative to `lo`.  The array has
    `nwords` words; values outside the represented window are ignored. -/
def bitsetOfValues (lo : Int) (nwords : Nat) (vs : List Int) : Array UInt64 :=
  vs.foldl (fun a v => setBitWord a (v - lo).toNat) (Array.replicate nwords 0)

/-- Multi-word bitset for the interval `[lo, hi]` minus `holes`.  The scan
    runs over the (at most 4096) interval values, so this is entry-only. -/
def bitsetOfHoles (lo hi : Int) (holes : Array Int) : Array UInt64 :=
  bitsetOfValues lo (bitsetWordCount (hi - lo + 1).toNat)
    (complementHoles lo hi holes).toList

/-- Bits of a Boolean domain assembled from a value list: bit 0 for
    `.bool false`, bit 1 for `.bool true`.  Non-Boolean values are ignored
    (the `.general` branch checks the shape separately). -/
def boolFold : List Value → UInt8
  | [] => 0
  | .bool b :: rest => boolFold rest ||| (if b then 2 else 1)
  | _ :: rest => boolFold rest

/-- The integer payload of an all-`.int` value list. -/
def intValues (vs : List Value) : Array Int :=
  vs.toArray.filterMap fun v => match v with | .int i => some i | _ => none

/-- Convert a compiled domain to the compact Core representation.  Entry
    only: it may traverse a `.general` domain's already materialized list.

    The `.general` integer case materializes the domain's distinct integers
    and represents them as the interval `[min, max]` minus the complement of
    the set.  The guards keep the result complement small (at most 4096
    holes): either the span itself is at most 4096, or the complement inside
    the span is.  Wider sparse sets keep their sorted values in `.sparse`, so
    entry conversion never materializes a wide complement and never allocates
    storage proportional to the span.  A wide dense input is still scanned in
    time proportional to its already-materialized list, which the entry
    conversion is allowed to traverse. -/
def DomC.ofDom? (d : Dom) : Option DomC :=
  match d.rep with
  | .small true _ bits => some (.bool (UInt8.ofNat (bits.toNat &&& 3)))
  | .small false off bits => some (.bitset off #[bits])
  | .holes lo hi hs =>
      let arr := hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi))
      let holes := sortedUniqueInts arr
      if _ : 0 < hi - lo + 1 ∧ hi - lo + 1 ≤ 4096 then
        some (.bitset lo (bitsetOfHoles lo hi holes))
      else some (.boundsHoles lo hi holes)
  | .general vs =>
      match vs with
      | [] => none
      | .bool _ :: _ =>
          if vs.all (fun v => match v with | .bool _ => true | _ => false) then
            some (.bool (boolFold vs))
          else none
      | .int _ :: _ =>
          if vs.all (fun v => match v with | .int _ => true | _ => false) then
            let uq := sortedUniqueInts (intValues vs)
            match arrayHead? uq, arrayLast? uq with
            | some lo, some hi =>
                let span := hi - lo + 1
                if span ≤ 4096 then
                  some (.bitset lo
                    (bitsetOfValues lo (bitsetWordCount span.toNat) uq.toList))
                else if span.toNat - uq.size ≤ 4096 then
                  some (.boundsHoles lo hi (complementHoles lo hi uq))
                else some (.sparse uq)
            | _, _ => none
          else none
      | _ => none

/-! ## Test-only enumeration -/

def DomC.toValueList : DomC → List Value
  | .bool bits =>
      ((List.range 2).filterMap fun k => if (bits &&& UInt8.ofNat (1 <<< k)) != 0
        then some (.bool (k == 1)) else none)
  | .bounds lo hi =>
      (List.range (if hi < lo then 0 else (hi - lo + 1).toNat)).map (fun (k : Nat) => Value.int (lo + (k : Int)))
  | .bitset lo words =>
      let rec wordVals (i : Nat) (w : UInt64) (acc : List Value) : List Value :=
        if i ≥ 64 then acc
        else if w.toNat.testBit i then wordVals (i + 1) w (.int (lo + (i : Int)) :: acc)
        else wordVals (i + 1) w acc
      termination_by 64 - i
      let rec goWords (i : Nat) (acc : List Value) : List Value :=
        if h : i < words.size then
          match words[i]? with
          | some w => goWords (i + 1) (wordVals 0 w acc)
          | none => acc
        else acc
      termination_by words.size - i
      (goWords 0 []).reverse
  | .boundsHoles lo hi holes =>
      let rec go (v : Int) (acc : List Value) : List Value :=
        if v > hi then acc
        else if memHoleRange holes v then go (v + 1) acc
        else go (v + 1) (.int v :: acc)
      termination_by (hi - v + 1).toNat
      (go lo []).reverse
  | .sparse values => values.toList.map (fun v => .int v)

/-! ## Well-formedness (runtime predicate; N3 proves the bridge) -/

def DomC.WF : DomC → Prop
  | .bool bits => bits &&& 3 = bits
  | .bounds _ _ => True
  | .bitset _ _ => True
  | .boundsHoles lo hi holes =>
      holes.toList.Pairwise (fun a b => a < b) ∧
        ∀ h ∈ holes.toList, lo ≤ h ∧ h ≤ hi
  | .sparse values => values.toList.Pairwise (fun a b => a < b)

/-! ## Proof lemmas for the entry conversion -/

/-! ### Insertion sort -/

theorem mem_insertSortedInt {v x : Int} {xs : List Int} :
    x ∈ insertSortedInt v xs ↔ x = v ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insertSortedInt]
  | cons y ys ih =>
      simp only [insertSortedInt]
      by_cases h1 : v == y
      · rw [if_pos h1]
        rw [beq_iff_eq] at h1
        subst h1
        simp
      · rw [if_neg h1]
        by_cases h2 : v < y
        · rw [if_pos h2]
          simp [List.mem_cons]
        · rw [if_neg h2]
          simp [List.mem_cons, ih]
          grind

theorem pairwise_insertSortedInt {v : Int} {xs : List Int}
    (h : xs.Pairwise (fun a b => a < b)) :
    (insertSortedInt v xs).Pairwise (fun a b => a < b) := by
  induction xs with
  | nil => simp [insertSortedInt]
  | cons y ys ih =>
      simp only [insertSortedInt]
      by_cases h1 : v == y
      · rw [if_pos h1]
        exact h
      · rw [if_neg h1]
        by_cases h2 : v < y
        · rw [if_pos h2]
          rw [List.pairwise_cons]
          refine ⟨?_, h⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact h2
          · have hyz : y < z := (List.pairwise_cons.mp h).1 z hz'
            omega
        · rw [if_neg h2]
          rw [List.pairwise_cons]
          have hne : ¬(v = y) := by
            intro he
            exact h1 (by simpa [he])
          have hyv : y < v := by omega
          refine ⟨?_, ih (List.pairwise_cons.mp h).2⟩
          intro z hz
          rw [mem_insertSortedInt] at hz
          rcases hz with rfl | hz'
          · exact hyv
          · exact (List.pairwise_cons.mp h).1 z hz'

theorem pairwise_sortUniqueInts (xs : List Int) :
    (sortUniqueInts xs).Pairwise (fun a b => a < b) := by
  induction xs with
  | nil => simp [sortUniqueInts]
  | cons x xs ih => simpa [sortUniqueInts] using pairwise_insertSortedInt (v := x) ih

theorem mem_sortUniqueInts {x : Int} {xs : List Int} :
    x ∈ sortUniqueInts xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [sortUniqueInts]
  | cons y ys ih =>
      simp [sortUniqueInts, mem_insertSortedInt, ih, List.mem_cons]

theorem pairwise_sortedUniqueInts (a : Array Int) :
    (sortedUniqueInts a).toList.Pairwise (fun x y => x < y) := by
  simpa [sortedUniqueInts] using pairwise_sortUniqueInts a.toList

theorem mem_sortedUniqueInts {a : Array Int} {x : Int} :
    x ∈ (sortedUniqueInts a).toList ↔ x ∈ a.toList := by
  simpa [sortedUniqueInts] using mem_sortUniqueInts (xs := a.toList)

/-! ### Strictly ascending arrays -/

theorem array_lt_of_pairwise {a : Array Int}
    (hs : a.toList.Pairwise (fun x y => x < y))
    {i j : Nat} (hi : i < a.size) (hj : j < a.size) (hij : i < j) :
    a[i] < a[j] := by
  have h := List.pairwise_iff_getElem.mp hs i j (by simpa using hi) (by simpa using hj) hij
  simpa using h

theorem arrayHead?_eq_some {a : Array Int} {x : Int} (h : arrayHead? a = some x) :
    ∃ hpos : 0 < a.size, a[0]'hpos = x := by
  unfold arrayHead? at h
  by_cases hpos : 0 < a.size
  · rw [dif_pos hpos] at h
    exact ⟨hpos, Option.some.inj h⟩
  · rw [dif_neg hpos] at h
    cases h

theorem arrayLast?_eq_some {a : Array Int} {x : Int} (h : arrayLast? a = some x) :
    ∃ hpos : a.size - 1 < a.size, a[a.size - 1]'hpos = x := by
  unfold arrayLast? at h
  by_cases hpos : 0 < a.size
  · rw [dif_pos hpos] at h
    exact ⟨by omega, Option.some.inj h⟩
  · rw [dif_neg hpos] at h
    cases h

theorem arrayHead?_le {a : Array Int} {x : Int} (hx : arrayHead? a = some x)
    (hs : a.toList.Pairwise (fun u v => u < v)) {y : Int} (hy : y ∈ a.toList) :
    x ≤ y := by
  obtain ⟨hpos, hx0⟩ := arrayHead?_eq_some hx
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  have hsize : i < a.size := by simpa using hi
  have hget : a.toList[i] = a[i] := by simp
  rw [hget] at hiy
  rw [← hiy, ← hx0]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    exact Int.le_refl _
  · exact Int.le_of_lt (array_lt_of_pairwise hs hpos hsize hipos)

theorem le_arrayLast? {a : Array Int} {x : Int} (hx : arrayLast? a = some x)
    (hs : a.toList.Pairwise (fun u v => u < v)) {y : Int} (hy : y ∈ a.toList) :
    y ≤ x := by
  obtain ⟨hpos, hx0⟩ := arrayLast?_eq_some hx
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  have hsize : i < a.size := by simpa using hi
  have hget : a.toList[i] = a[i] := by simp
  rw [hget] at hiy
  rw [← hiy, ← hx0]
  by_cases hlast : i = a.size - 1
  · subst hlast
    exact Int.le_refl _
  · have hilt : i < a.size - 1 := by omega
    exact Int.le_of_lt (array_lt_of_pairwise hs (by omega) hpos (by omega))

/-! ### 64-bit membership -/

theorem nat_testBit_and_three (n j : Nat) (hj : j < 2) :
    (n &&& 3).testBit j = n.testBit j := by
  have h3 : Nat.testBit 3 j = true := by
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide
  rw [Nat.testBit_and, h3, Bool.and_true]

theorem bitsetMem_singleton (bits : UInt64) (n : Nat) :
    bitsetMem #[bits] n = (if n < 64 then bits.toNat.testBit n else false) := by
  unfold bitsetMem
  by_cases hn : n < 64
  · have hw : n / 64 = 0 := by omega
    have hm : n % 64 = n := Nat.mod_eq_of_lt hn
    rw [hw, hm]
    simpa [hn] using Bool.eq_iff_iff.mpr (uint64_and_u64bit_ne_zero_iff bits hn)
  · have hnone : #[bits][n / 64]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simp
      omega
    rw [hnone]
    simp [hn]

theorem uint8_ne_zero_iff_toNat_ne_zero (x : UInt8) : x ≠ 0 ↔ x.toNat ≠ 0 := by
  constructor
  · intro h hz
    exact h (UInt8.toNat_inj.mp (by simpa using hz))
  · intro h hz
    exact h (by rw [hz]; rfl)

theorem uint8_toNat_ofNat_and_three (n : Nat) :
    (UInt8.ofNat (n &&& 3)).toNat = n &&& 3 := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := Nat.and_le_right (n := n) (m := 3); omega)

theorem uint8_ofNat_and_one_ne (n : Nat) :
    ((UInt8.ofNat (n &&& 3) &&& (1 : UInt8)) != 0) = true ↔ n.testBit 0 = true := by
  rw [bne_iff_ne, uint8_ne_zero_iff_toNat_ne_zero,
    UInt8.toNat_and, uint8_toNat_ofNat_and_three]
  have h1 : (1 : UInt8).toNat = 1 := rfl
  rw [h1]
  have hkey := nat_and_two_pow_ne_zero (n := n &&& 3) (k := 0)
  rw [Nat.pow_zero] at hkey
  rw [hkey]
  rw [nat_testBit_and_three n 0 (by omega)]

theorem uint8_ofNat_and_two_ne (n : Nat) :
    ((UInt8.ofNat (n &&& 3) &&& (2 : UInt8)) != 0) = true ↔ n.testBit 1 = true := by
  rw [bne_iff_ne, uint8_ne_zero_iff_toNat_ne_zero,
    UInt8.toNat_and, uint8_toNat_ofNat_and_three]
  have h2 : (2 : UInt8).toNat = 2 := rfl
  rw [h2]
  have hkey := nat_and_two_pow_ne_zero (n := n &&& 3) (k := 1)
  have hpow : (2 : Nat) = 2 ^ 1 := by decide
  rw [hpow] at hkey
  rw [hkey]
  rw [nat_testBit_and_three n 1 (by omega)]

theorem uint8_ofNat_and_ite_ne (n : Nat) (b : Bool) :
    ((UInt8.ofNat (n &&& 3) &&& (if b then 2 else 1)) != 0) = true ↔
      n.testBit (if b then 1 else 0) = true := by
  cases b
  · simpa using uint8_ofNat_and_one_ne n
  · simpa using uint8_ofNat_and_two_ne n

theorem uint8_and_bit_ne_zero_iff (x : UInt8) (b : Bool) :
    ((x &&& (if b then 2 else 1)) != 0) = true ↔
      x.toNat.testBit (if b then 1 else 0) = true := by
  rw [bne_iff_ne, uint8_ne_zero_iff_toNat_ne_zero, UInt8.toNat_and]
  have hbit : ((if b then 2 else 1) : UInt8).toNat =
      2 ^ (if b then 1 else 0) := by
    cases b <;> decide
  rw [hbit]
  exact nat_and_two_pow_ne_zero

/-- Correctness of the fuelled binary search: it finds exactly the values
    stored in the window `[lo, hi)`, provided the hole array is strictly
    ascending. -/
private theorem memHoleRangeGo_spec {holes : Array Int} {v : Int}
    (hs : holes.toList.Pairwise (fun a b => a < b)) :
    ∀ (fuel lo hi : Nat), hi - lo ≤ fuel → hi ≤ holes.size →
      (memHoleRangeGo holes v fuel lo hi = true ↔
        ∃ j, lo ≤ j ∧ j < hi ∧ holes[j]? = some v) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hfuel hhi
      simp only [memHoleRangeGo, Bool.false_eq_true, false_iff]
      rintro ⟨j, hjlo, hjhi, hjv⟩
      omega
  | succ fuel ih =>
      intro lo hi hfuel hhi
      simp only [memHoleRangeGo]
      by_cases hlt : lo < hi
      · rw [if_pos hlt]
        have hmid_lt : (lo + hi) / 2 < hi := by omega
        have hmid_ge : lo ≤ (lo + hi) / 2 := by omega
        have hmid_size : (lo + hi) / 2 < holes.size := by omega
        rw [Array.getElem?_eq_getElem hmid_size]
        dsimp only
        by_cases heq : holes[(lo + hi) / 2] == v
        · rw [if_pos heq]
          constructor
          · intro _
            refine ⟨(lo + hi) / 2, hmid_ge, hmid_lt, ?_⟩
            rw [Array.getElem?_eq_getElem hmid_size, beq_iff_eq.mp heq]
          · intro _
            rfl
        · rw [if_neg heq]
          have hne : holes[(lo + hi) / 2] ≠ v := fun h => heq (beq_iff_eq.mpr h)
          by_cases hltv : holes[(lo + hi) / 2] < v
          · rw [if_pos hltv]
            have hfuel' : hi - ((lo + hi) / 2 + 1) ≤ fuel := by omega
            rw [ih ((lo + hi) / 2 + 1) hi hfuel' hhi]
            constructor
            · rintro ⟨j, hjlo, hjhi, hjv⟩
              exact ⟨j, by omega, hjhi, hjv⟩
            · rintro ⟨j, hjlo, hjhi, hjv⟩
              have hj_size : j < holes.size := by
                by_cases h : j < holes.size
                · exact h
                · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hjv
                  cases hjv
              have hj_eq : holes[j] = v := by
                rw [Array.getElem?_eq_getElem hj_size] at hjv
                exact Option.some.inj hjv
              have hgt : (lo + hi) / 2 < j := by
                by_cases hcon : (lo + hi) / 2 < j
                · exact hcon
                · have hle : j ≤ (lo + hi) / 2 := by omega
                  rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
                  · have hltv' := array_lt_of_pairwise hs hj_size hmid_size hlt'
                    omega
                  · subst heq'
                    omega
              exact ⟨j, by omega, hjhi, hjv⟩
          · rw [if_neg hltv]
            have hvlt : v < holes[(lo + hi) / 2] := by omega
            have hfuel' : (lo + hi) / 2 - lo ≤ fuel := by omega
            rw [ih lo ((lo + hi) / 2) hfuel' (by omega)]
            constructor
            · rintro ⟨j, hjlo, hjhi, hjv⟩
              exact ⟨j, hjlo, by omega, hjv⟩
            · rintro ⟨j, hjlo, hjhi, hjv⟩
              have hj_size : j < holes.size := by
                by_cases h : j < holes.size
                · exact h
                · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hjv
                  cases hjv
              have hj_eq : holes[j] = v := by
                rw [Array.getElem?_eq_getElem hj_size] at hjv
                exact Option.some.inj hjv
              have hlt' : j < (lo + hi) / 2 := by
                by_cases hcon : j < (lo + hi) / 2
                · exact hcon
                · have hle : (lo + hi) / 2 ≤ j := by omega
                  rcases Nat.lt_or_eq_of_le hle with hlt'' | heq'
                  · have hltv' := array_lt_of_pairwise hs hmid_size hj_size hlt''
                    omega
                  · subst heq'
                    omega
              exact ⟨j, hjlo, hlt', hjv⟩
      · rw [if_neg hlt]
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨j, hjlo, hjhi, hjv⟩
        omega

/-- The public binary search finds exactly the members of the hole array. -/
theorem memHoleRange_eq_true_iff {holes : Array Int} {v : Int}
    (hs : holes.toList.Pairwise (fun a b => a < b)) :
    memHoleRange holes v = true ↔ v ∈ holes.toList := by
  unfold memHoleRange
  rw [memHoleRangeGo_spec hs holes.size 0 holes.size (by omega) (by omega)]
  constructor
  · rintro ⟨j, -, hjhi, hjv⟩
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hjv)
  · intro hv
    obtain ⟨j, hjv⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hv)
    refine ⟨j, by omega, ?_, hjv⟩
    by_cases h : j < holes.size
    · exact h
    · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hjv
      cases hjv

/-- Negative form of `memHoleRange_eq_true_iff`. -/
theorem memHoleRange_eq_false_iff {holes : Array Int} {v : Int}
    (hs : holes.toList.Pairwise (fun a b => a < b)) :
    memHoleRange holes v = false ↔ v ∉ holes.toList := by
  constructor
  · intro h hv
    have := (memHoleRange_eq_true_iff hs).mpr hv
    rw [h] at this
    cases this
  · intro h
    cases hb : memHoleRange holes v
    · rfl
    · exact absurd ((memHoleRange_eq_true_iff hs).mp hb) h

/-- Membership in the interval complement enumeration. -/
theorem mem_complementHoles {lo hi : Int} {vs : Array Int} {v : Int}
    (hs : vs.toList.Pairwise (fun a b => a < b)) :
    v ∈ (complementHoles lo hi vs).toList ↔ lo ≤ v ∧ v ≤ hi ∧ v ∉ vs.toList := by
  unfold complementHoles
  rw [Array.mem_toList_iff, List.mem_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxm⟩
    rw [List.mem_range] at hx
    by_cases h : memHoleRange vs (lo + (x : Int)) = true
    · rw [if_pos h] at hxm
      cases hxm
    · rw [if_neg h] at hxm
      have hxv : lo + (x : Int) = v := Option.some.inj hxm
      subst hxv
      have hklt : (x : Int) < hi - lo + 1 := by
        rw [Int.lt_toNat] at hx
        exact hx
      refine ⟨by omega, by omega, ?_⟩
      rintro hv
      exact h ((memHoleRange_eq_true_iff hs).mpr hv)
  · rintro ⟨hlo, hhi, hnot⟩
    have hk : ((v - lo).toNat) < (hi - lo + 1).toNat := by
      rw [Int.toNat_lt' (by omega : 0 < (hi - lo + 1).toNat)]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
      omega
    have hkval : lo + ((v - lo).toNat : Int) = v := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ v - lo)]
      omega
    refine ⟨(v - lo).toNat, List.mem_range.mpr hk, ?_⟩
    have hcond : memHoleRange vs (lo + ((v - lo).toNat : Int)) = false := by
      rw [hkval]
      exact (memHoleRange_eq_false_iff hs).mpr hnot
    have hcond' : ¬(memHoleRange vs (lo + ((v - lo).toNat : Int)) = true) := by
      rw [hcond]
      simp
    rw [if_neg hcond']
    rw [hkval]

/-- Membership of the integer payload of an all-integer value list. -/
theorem mem_intValues {vs : List Value} {x : Int} :
    x ∈ (intValues vs).toList ↔ .int x ∈ vs := by
  unfold intValues
  rw [Array.mem_toList_iff, Array.mem_filterMap]
  simp only [List.mem_toArray]
  constructor
  · rintro ⟨v, hv, hf⟩
    cases v with
    | int i =>
        simp only [Option.some.injEq] at hf
        subst hf
        exact hv
    | bool b => simp at hf
    | setOfInt s => simp at hf
    | array a => simp at hf
  · intro h
    exact ⟨.int x, h, rfl⟩

/-- Filtering a hole list to the window keeps exactly the in-window holes. -/
theorem mem_filter_window {lo hi : Int} {hs : List Int} {x : Int} :
    x ∈ (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi))).toList ↔
      x ∈ hs ∧ lo ≤ x ∧ x ≤ hi := by
  rw [Array.toList_filter, List.mem_filter, Array.mem_toList_iff]
  constructor
  · rintro ⟨hx, hd⟩
    rw [Bool.and_eq_true] at hd
    exact ⟨hx, of_decide_eq_true hd.1, of_decide_eq_true hd.2⟩
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by simp [decide_eq_true hlo, decide_eq_true hhi]⟩

theorem boolFold_zero : boolFold [] = 0 := rfl

/-- Boolean-fold membership: on an all-Boolean list, the folded bit for `b`
    is set exactly when `.bool b` occurs. -/
theorem boolFold_testBit {vs : List Value} {b : Bool}
    (hshape : vs.all (fun v => match v with | .bool _ => true | _ => false) = true) :
    (boolFold vs).toNat.testBit (if b then 1 else 0) = true ↔ .bool b ∈ vs := by
  induction vs with
  | nil => simp [boolFold]
  | cons v rest ih =>
      have hshape' : rest.all (fun v => match v with | .bool _ => true | _ => false) = true := by
        rw [List.all_eq_true] at hshape ⊢
        intro x hx
        exact hshape x (by simp [hx])
      cases v with
      | bool b0 =>
          have hbit : (((if b0 then 2 else 1) : UInt8).toNat.testBit
              (if b then 1 else 0) = true) ↔ b = b0 := by
            cases b <;> cases b0 <;> decide
          simp only [boolFold, UInt8.toNat_or, Nat.testBit_or, ih hshape', List.mem_cons,
            Value.bool.injEq, hbit]
          grind
      | int i =>
          have hv := (List.all_eq_true.mp hshape) (.int i) (by simp)
          exact absurd hv (by simp)
      | setOfInt s =>
          have hv := (List.all_eq_true.mp hshape) (.setOfInt s) (by simp)
          exact absurd hv (by simp)
      | array a =>
          have hv := (List.all_eq_true.mp hshape) (.array a) (by simp)
          exact absurd hv (by simp)

/-- The Boolean fold only sets bits 0 and 1. -/
theorem boolFold_and_three (vs : List Value) : boolFold vs &&& 3 = boolFold vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      cases v with
      | bool b =>
          have ih' : (boolFold rest).toNat &&& 3 = (boolFold rest).toNat := by
            have := congrArg UInt8.toNat ih
            rwa [UInt8.toNat_and] at this
          have hbit : ((if b then 2 else 1) : UInt8).toNat &&& 3 =
              ((if b then 2 else 1) : UInt8).toNat := by
            cases b <;> decide
          apply UInt8.toNat_inj.mp
          simp only [boolFold]
          have h3 : (3 : UInt8).toNat = 3 := rfl
          rw [UInt8.toNat_and, UInt8.toNat_or, h3]
          rw [Nat.and_or_distrib_right, ih', hbit]
      | int i => exact ih
      | setOfInt s => exact ih
      | array a => exact ih

/-- Every in-window integer is either listed or a hole. -/
theorem mem_or_mem_complementHoles {lo hi : Int} {vs : Array Int} {v : Int}
    (hs : vs.toList.Pairwise (fun a b => a < b)) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    v ∈ vs.toList ∨ v ∈ (complementHoles lo hi vs).toList := by
  by_cases h : v ∈ vs.toList
  · exact Or.inl h
  · exact Or.inr ((mem_complementHoles hs).mpr ⟨hlo, hhi, h⟩)

/-- Exactly one of listed/hole holds inside the window. -/
theorem not_mem_complementHoles_iff {lo hi : Int} {vs : Array Int} {v : Int}
    (hs : vs.toList.Pairwise (fun a b => a < b)) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    v ∉ (complementHoles lo hi vs).toList ↔ v ∈ vs.toList := by
  constructor
  · intro h
    rcases mem_or_mem_complementHoles hs hlo hhi with hv | hc
    · exact hv
    · exact absurd hc h
  · intro hv hc
    exact ((mem_complementHoles hs).mp hc).2.2 hv

/-- Boolean values are exactly the `.bool` constructor applications. -/
theorem eq_bool_of_mem_all_bool {vs : List Value} {v : Value}
    (hshape : vs.all (fun v => match v with | .bool _ => true | _ => false) = true)
    (hv : v ∈ vs) : ∃ b : Bool, v = .bool b := by
  have h := (List.all_eq_true.mp hshape) v hv
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | int i => simp at h
  | setOfInt s => simp at h
  | array a => simp at h

/-- Integer values are exactly the `.int` constructor applications. -/
theorem eq_int_of_mem_all_int {vs : List Value} {v : Value}
    (hshape : vs.all (fun v => match v with | .int _ => true | _ => false) = true)
    (hv : v ∈ vs) : ∃ i : Int, v = .int i := by
  have h := (List.all_eq_true.mp hshape) v hv
  cases v with
  | int i => exact ⟨i, rfl⟩
  | bool b => simp at h
  | setOfInt s => simp at h
  | array a => simp at h

theorem uint8_ofNat_and_three_and_three (n : Nat) :
    (UInt8.ofNat (n &&& 3) &&& 3) = UInt8.ofNat (n &&& 3) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, uint8_toNat_ofNat_and_three]
  have h3 : (3 : UInt8).toNat = 3 := rfl
  rw [h3, Nat.and_assoc, Nat.and_self]

theorem mem_small_true {off : Int} {bits : UInt64} {v : Value} :
    (DomC.bool (UInt8.ofNat (bits.toNat &&& 3))).mem v = true ↔
      v ∈ Dom.enum ⟨.small true off bits⟩ := by
  cases v with
  | bool b =>
      simp only [DomC.mem, Dom.enum]
      rw [uint8_ofNat_and_ite_ne]
      exact (Dom.mem_smallBools_bool bits b).symm
  | int i =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := Dom.eq_bool_of_mem_smallBools (v := .int i) h
        cases hb
  | setOfInt s =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := Dom.eq_bool_of_mem_smallBools (v := .setOfInt s) h
        cases hb
  | array a =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := Dom.eq_bool_of_mem_smallBools (v := .array a) h
        cases hb

theorem mem_small_false {off : Int} {bits : UInt64} {i : Int} :
    (DomC.bitset off #[bits]).mem (.int i) = true ↔
      .int i ∈ Dom.enum ⟨.small false off bits⟩ := by
  simp only [DomC.mem, Dom.enum]
  rw [Dom.mem_smallInts_map_int, Dom.mem_smallInts_int]
  by_cases hk : i - off < 0
  · have hoff : ¬ off ≤ i := by omega
    simp [hk, hoff]
  · have hoff : off ≤ i := by omega
    rw [bitsetMem_singleton]
    by_cases h64 : (i - off).toNat < 64
    · have h64' : i - off < 64 :=
        (Int.toNat_lt (by omega : 0 ≤ i - off)).mp h64
      simp [hk, hoff, h64, h64']
    · have h64' : ¬ i - off < 64 := fun h =>
        h64 ((Int.toNat_lt (by omega : 0 ≤ i - off)).mpr h)
      simp [hk, hoff, h64, h64']

theorem mem_holes_ofDom {lo hi : Int} {hs : List Int} {v : Value} :
    (DomC.boundsHoles lo hi
      (sortedUniqueInts (hs.toArray.filter
        (fun h => decide (lo ≤ h) && decide (h ≤ hi))))).mem v = true ↔
      v ∈ Dom.enum ⟨.holes lo hi hs⟩ := by
  have hpair : (sortedUniqueInts (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)))).toList.Pairwise (fun a b => a < b) :=
    pairwise_sortedUniqueInts _
  have hmem : ∀ x : Int, x ∈ (sortedUniqueInts (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)))).toList ↔ x ∈ hs ∧ lo ≤ x ∧ x ≤ hi := by
    intro x
    rw [mem_sortedUniqueInts, mem_filter_window]
  cases v with
  | int i =>
      simp only [DomC.mem]
      rw [Dom.mem_holes_enum_int, Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨hlo, hhi⟩, hnot⟩
        have hlodec := of_decide_eq_true hlo
        have hhidec := of_decide_eq_true hhi
        have hmr : memHoleRange (sortedUniqueInts (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)))) i = false := by
          simpa using hnot
        refine ⟨hlodec, hhidec, ?_⟩
        intro hinh
        have hin : i ∈ (sortedUniqueInts (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)))).toList :=
          (hmem i).mpr ⟨hinh, hlodec, hhidec⟩
        have htrue := (memHoleRange_eq_true_iff hpair).mpr hin
        rw [htrue] at hmr
        cases hmr
      · rintro ⟨hlo, hhi, hnot⟩
        refine ⟨⟨decide_eq_true hlo, decide_eq_true hhi⟩, ?_⟩
        have hmr : memHoleRange (sortedUniqueInts (hs.toArray.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)))) i = false := by
          rw [memHoleRange_eq_false_iff hpair]
          intro hin
          exact hnot ((hmem i).mp hin).1
        have hmr' : memHoleRange (sortedUniqueInts (List.filter (fun h => decide (lo ≤ h) && decide (h ≤ hi)) hs).toArray) i = false := by
          simpa using hmr
        simp [hmr']
  | bool b =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .bool b) h
        cases hi
  | setOfInt s =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .setOfInt s) h
        cases hi
  | array a =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .array a) h
        cases hi

/-! ### Multi-word bitset membership -/

theorem bitsetMem_replicate_zero (nwords n : Nat) :
    bitsetMem (Array.replicate nwords (0 : UInt64)) n = false := by
  unfold bitsetMem
  rw [Array.getElem?_replicate]
  by_cases h : n / 64 < nwords <;> simp [h]

/-- Membership in a word array written through `get!`. -/
theorem bitsetMem_eq_getWord (words : Array UInt64) (n : Nat) :
    bitsetMem words n =
      bne ((words[n / 64]!) &&& u64bit (n % 64)) 0 := by
  unfold bitsetMem
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  cases h : words[n / 64]?
  · have hge : ¬ n / 64 < words.size := by
      intro hlt
      have hsome := Array.getElem?_eq_getElem hlt
      rw [h] at hsome
      cases hsome
    simp [hge]
    change ((0 : UInt64) &&& u64bit (n % 64)) = 0
    simp
  · obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp h
    rw [dif_pos hlt]
    rw [Array.getInternal_eq_getElem]
    rw [heq]

theorem bitsetMem_set!_local {words : Array UInt64} {wi : Nat} (hwi : wi < words.size)
    (w : UInt64) (n : Nat) :
    bitsetMem (words.set! wi w) n =
      if n / 64 = wi then (w &&& u64bit (n % 64)) != 0 else bitsetMem words n := by
  unfold bitsetMem
  rw [Array.set!_eq_setIfInBounds]
  rw [Array.getElem?_setIfInBounds]
  by_cases h : wi = n / 64
  · rw [if_pos h, if_pos hwi, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hn => h hn.symm)]

theorem uint64_or_u64bit_and_u64bit_ne_zero_iff (w : UInt64) {k n : Nat}
    (hk : k < 64) (hn : n < 64) :
    ((w ||| u64bit k) &&& u64bit n) != 0 ↔ k = n ∨ (w &&& u64bit n) != 0 := by
  rw [uint64_and_u64bit_ne_zero_iff _ hn, UInt64.toNat_or, Nat.testBit_or,
      u64bit_toNat hk, Nat.testBit_two_pow, uint64_and_u64bit_ne_zero_iff w hn]
  by_cases h : k = n
  · subst h; simp
  · simp [h]

theorem bitsetMem_setBit_iff {words : Array UInt64} {k n : Nat}
    (hk : k / 64 < words.size) :
    bitsetMem (setBitWord words k) n = true ↔ n = k ∨ bitsetMem words n = true := by
  unfold setBitWord
  rw [dif_pos hk]
  rw [bitsetMem_set!_local hk]
  by_cases hb : n / 64 = k / 64
  · rw [if_pos hb]
    rw [uint64_or_u64bit_and_u64bit_ne_zero_iff _ (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))]
    rw [bitsetMem_eq_getWord words n]
    have hword : (words[k / 64]!) = (words[n / 64]!) := by rw [hb]
    rw [hword]
    constructor
    · rintro (hmod | hbit)
      · left
        have hn := Nat.div_add_mod n 64
        have hk' := Nat.div_add_mod k 64
        omega
      · right; exact hbit
    · rintro (hkn | hbit)
      · subst hkn; left; simp
      · right; exact hbit
  · rw [if_neg hb]
    constructor
    · intro h; exact Or.inr h
    · rintro (hkn | h)
      · subst hkn; exact absurd rfl hb
      · exact h

/-- Folding `setBitWord` over a value list sets exactly those bits.  The
    `hsize`/`hb` hypotheses keep every written word inside the array. -/
theorem bitsetMem_foldl_setBit {lo : Int} {nwords : Nat} (vs : List Int)
    (init : Array UInt64) (hsize : init.size = nwords)
    (hb : ∀ v ∈ vs, (v - lo).toNat / 64 < nwords) (n : Nat) :
    bitsetMem (vs.foldl (fun a v => setBitWord a (v - lo).toNat) init) n = true ↔
      (∃ v ∈ vs, (v - lo).toNat = n) ∨ bitsetMem init n = true := by
  induction vs generalizing init with
  | nil => simp
  | cons v rest ih =>
      rw [List.foldl_cons]
      have hb' : ∀ w ∈ rest, (w - lo).toNat / 64 < nwords :=
        fun w hw => hb w (by simp [hw])
      have hk : (v - lo).toNat / 64 < init.size := by
        rw [hsize]; exact hb v (by simp)
      have hsize' : (setBitWord init (v - lo).toNat).size = nwords := by
        unfold setBitWord
        rw [dif_pos hk, Array.size_set!]
        exact hsize
      rw [ih (setBitWord init (v - lo).toNat) hsize' hb']
      rw [bitsetMem_setBit_iff (words := init) (k := (v - lo).toNat) (n := n) ?_]
      · constructor
        · rintro (⟨w, hw, hwk⟩ | hvn | hinit)
          · exact Or.inl ⟨w, by simp [hw], hwk⟩
          · exact Or.inl ⟨v, by simp, hvn.symm⟩
          · exact Or.inr hinit
        · rintro (⟨w, hw, hwk⟩ | hinit)
          · rcases List.mem_cons.mp hw with rfl | hw'
            · exact Or.inr (Or.inl hwk.symm)
            · exact Or.inl ⟨w, hw', hwk⟩
          · exact Or.inr (Or.inr hinit)
      · rw [hsize]; exact hb v (by simp)

/-- Membership of the multi-word bitset conversion of a medium interval with
    holes.  This is the `bitset` counterpart of `mem_holes_ofDom`. -/
theorem mem_holes_bitset_ofDom {lo hi : Int} {hs : List Int} {v : Value}
    (hspanlo : 0 < hi - lo + 1) (hspanhi : hi - lo + 1 ≤ 4096) :
    (DomC.bitset lo (bitsetOfHoles lo hi
      (sortedUniqueInts (hs.toArray.filter
        (fun h => decide (lo ≤ h) && decide (h ≤ hi)))))).mem v = true ↔
      v ∈ Dom.enum ⟨.holes lo hi hs⟩ := by
  have hpair : (sortedUniqueInts (hs.toArray.filter
      (fun h => decide (lo ≤ h) && decide (h ≤ hi)))).toList.Pairwise
      (fun a b => a < b) := pairwise_sortedUniqueInts _
  have hmem : ∀ x : Int, x ∈ (sortedUniqueInts (hs.toArray.filter
      (fun h => decide (lo ≤ h) && decide (h ≤ hi)))).toList ↔
      x ∈ hs ∧ lo ≤ x ∧ x ≤ hi := by
    intro x
    rw [mem_sortedUniqueInts, mem_filter_window]
  have hcompmem : ∀ x : Int, x ∈ (complementHoles lo hi
      (sortedUniqueInts (hs.toArray.filter
        (fun h => decide (lo ≤ h) && decide (h ≤ hi))))).toList ↔
      lo ≤ x ∧ x ≤ hi ∧ x ∉ hs := by
    intro x
    rw [mem_complementHoles hpair]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun hx => h3 ((hmem x).mpr ⟨hx, h1, h2⟩)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun hx => h3 ((hmem x).mp hx).1⟩
  have hb : ∀ x ∈ (complementHoles lo hi
      (sortedUniqueInts (hs.toArray.filter
        (fun h => decide (lo ≤ h) && decide (h ≤ hi))))).toList,
      (x - lo).toNat / 64 < bitsetWordCount (hi - lo + 1).toNat := by
    intro x hx
    have hx' := (hcompmem x).mp hx
    have hklt : (x - lo).toNat < (hi - lo + 1).toNat :=
      (Int.toNat_lt_toNat hspanlo).mpr (by omega)
    have hdiv := Nat.div_add_mod ((hi - lo + 1).toNat + 63) 64
    have hmod := Nat.mod_lt ((hi - lo + 1).toNat + 63) (by decide : 0 < 64)
    have hle : (hi - lo + 1).toNat ≤ bitsetWordCount (hi - lo + 1).toNat * 64 := by
      unfold bitsetWordCount
      omega
    exact Nat.div_lt_of_lt_mul (by omega)
  cases v with
  | int i =>
      by_cases hlt : i - lo < 0
      · have hlt' : i < lo := by omega
        simp only [DomC.mem]
        rw [if_pos hlt, Dom.mem_holes_enum_int]
        simp only [Bool.false_eq_true, false_iff]
        intro hcon
        exact absurd hcon.1 (by omega)
      · simp only [DomC.mem]
        rw [if_neg hlt]
        rw [Dom.mem_holes_enum_int]
        have hfold := bitsetMem_foldl_setBit (lo := lo)
          (nwords := bitsetWordCount (hi - lo + 1).toNat)
          (complementHoles lo hi (sortedUniqueInts (hs.toArray.filter
            (fun h => decide (lo ≤ h) && decide (h ≤ hi))))).toList
          (Array.replicate (bitsetWordCount (hi - lo + 1).toNat) 0) (by simp) hb
          (i - lo).toNat
        rw [bitsetMem_replicate_zero] at hfold
        simp only [or_false, Bool.false_eq_true] at hfold
        have hge : lo ≤ i := by omega
        have hwords : bitsetMem (bitsetOfHoles lo hi
            (sortedUniqueInts (hs.toArray.filter
              (fun h => decide (lo ≤ h) && decide (h ≤ hi))))) (i - lo).toNat =
            bitsetMem ((complementHoles lo hi (sortedUniqueInts (hs.toArray.filter
              (fun h => decide (lo ≤ h) && decide (h ≤ hi))))).toList.foldl
              (fun a v => setBitWord a (v - lo).toNat)
              (Array.replicate (bitsetWordCount (hi - lo + 1).toNat) 0))
              (i - lo).toNat := by
          unfold bitsetOfHoles bitsetOfValues
          rfl
        rw [hwords, hfold]
        constructor
        · rintro ⟨x, hx, hxeq⟩
          have hx' := (hcompmem x).mp hx
          have heq : x = i := by
            have h1 : ((x - lo).toNat : Int) = x - lo :=
              Int.toNat_of_nonneg (by omega)
            have h2 : ((i - lo).toNat : Int) = i - lo :=
              Int.toNat_of_nonneg (by omega)
            omega
          subst heq
          exact ⟨hx'.1, hx'.2.1, hx'.2.2⟩
        · rintro ⟨hli, hhi, hnot⟩
          exact ⟨i, (hcompmem i).mpr ⟨hli, hhi, hnot⟩, rfl⟩
  | bool b =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .bool b) h
        cases hi
  | setOfInt s =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .setOfInt s) h
        cases hi
  | array a =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨i, hi⟩ := Dom.eq_int_of_mem_holes_enum (v := .array a) h
        cases hi

theorem pairwise_complementHoles (lo hi : Int) (vs : Array Int) :
    (complementHoles lo hi vs).toList.Pairwise (fun a b => a < b) := by
  unfold complementHoles
  refine List.Pairwise.filterMap _ (fun a a' ha b hb b' hb' => ?_) (pairwise_range _)
  by_cases h : memHoleRange vs (lo + (a : Int)) = true
  · rw [if_pos h] at hb
    cases hb
  · rw [if_neg h] at hb
    obtain rfl := Option.some.inj hb
    by_cases h' : memHoleRange vs (lo + (a' : Int)) = true
    · rw [if_pos h'] at hb'
      cases hb'
    · rw [if_neg h'] at hb'
      obtain rfl := Option.some.inj hb'
      have : (a : Int) < (a' : Int) := by exact_mod_cast ha
      omega

theorem mem_general_bool {vs : List Value} {v : Value}
    (hshape : vs.all (fun v => match v with | .bool _ => true | _ => false) = true) :
    (DomC.bool (boolFold vs)).mem v = true ↔
      v ∈ Dom.enum ⟨.general vs⟩ := by
  cases v with
  | bool b =>
      simp only [DomC.mem, Dom.enum]
      rw [uint8_and_bit_ne_zero_iff, boolFold_testBit hshape]
  | int i =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := eq_bool_of_mem_all_bool hshape h
        cases hb
  | setOfInt s =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := eq_bool_of_mem_all_bool hshape h
        cases hb
  | array a =>
      constructor
      · intro h; simp [DomC.mem] at h
      · intro h
        obtain ⟨b, hb⟩ := eq_bool_of_mem_all_bool hshape h
        cases hb

theorem mem_general_int {vs : List Value} {i : Int} {lo hi : Int}
    (hlo : arrayHead? (sortedUniqueInts (intValues vs)) = some lo)
    (hhi : arrayLast? (sortedUniqueInts (intValues vs)) = some hi) :
    (DomC.boundsHoles lo hi
      (complementHoles lo hi (sortedUniqueInts (intValues vs)))).mem (.int i) = true ↔
      .int i ∈ Dom.enum ⟨.general vs⟩ := by
  have hpair : (sortedUniqueInts (intValues vs)).toList.Pairwise (fun a b => a < b) :=
    pairwise_sortedUniqueInts _
  have hmem : ∀ x : Int, x ∈ (sortedUniqueInts (intValues vs)).toList ↔ .int x ∈ vs := by
    intro x
    rw [mem_sortedUniqueInts]
    exact mem_intValues
  have hbounds : ∀ x : Int, .int x ∈ vs → lo ≤ x ∧ x ≤ hi := by
    intro x hx
    have hxq : x ∈ (sortedUniqueInts (intValues vs)).toList := (hmem x).mpr hx
    exact ⟨arrayHead?_le hlo hpair hxq, le_arrayLast? hhi hpair hxq⟩
  have hcomp_pair : (complementHoles lo hi (sortedUniqueInts (intValues vs))).toList.Pairwise
      (fun a b => a < b) := pairwise_complementHoles _ _ _
  simp only [DomC.mem, Dom.enum]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hlo', hhi'⟩, hnot⟩
    have hlodec := of_decide_eq_true hlo'
    have hhidec := of_decide_eq_true hhi'
    have hmr : memHoleRange
        (complementHoles lo hi (sortedUniqueInts (intValues vs))) i = false := by
      simpa using hnot
    have hcomp : i ∉ (complementHoles lo hi
        (sortedUniqueInts (intValues vs))).toList := by
      intro hin
      have htrue := (memHoleRange_eq_true_iff hcomp_pair).mpr hin
      rw [htrue] at hmr
      cases hmr
    have hinq := (not_mem_complementHoles_iff hpair hlodec hhidec).mp hcomp
    exact (hmem i).mp hinq
  · intro hv
    obtain ⟨hlo', hhi'⟩ := hbounds i hv
    have hinq := (hmem i).mpr hv
    have hcomp := (not_mem_complementHoles_iff hpair hlo' hhi').mpr hinq
    refine ⟨⟨decide_eq_true hlo', decide_eq_true hhi'⟩, ?_⟩
    have hmr : memHoleRange
        (complementHoles lo hi (sortedUniqueInts (intValues vs))) i = false :=
      (memHoleRange_eq_false_iff hcomp_pair).mpr hcomp
    simp [hmr]

/-- Membership of the sorted sparse conversion of a wide integer
enumeration.  This is the span-independent counterpart of `mem_general_int`. -/
theorem mem_general_sparse {vs : List Value} {i : Int} :
    (DomC.sparse (sortedUniqueInts (intValues vs))).mem (.int i) = true ↔
      .int i ∈ Dom.enum ⟨.general vs⟩ := by
  have hpair : (sortedUniqueInts (intValues vs)).toList.Pairwise (fun a b => a < b) :=
    pairwise_sortedUniqueInts _
  have hmem : ∀ x : Int, x ∈ (sortedUniqueInts (intValues vs)).toList ↔ .int x ∈ vs := by
    intro x
    rw [mem_sortedUniqueInts]
    exact mem_intValues
  simp only [DomC.mem, Dom.enum]
  rw [memHoleRange_eq_true_iff hpair]
  exact hmem i

/-- Membership of the multi-word bitset conversion of a dense integer
enumeration.  This is the `bitset` counterpart of `mem_general_int`. -/
theorem mem_general_bitset {vs : List Value} {i : Int} {lo hi : Int}
    (hshape : vs.all (fun v => match v with | .int _ => true | _ => false) = true)
    (hhead : arrayHead? (sortedUniqueInts (intValues vs)) = some lo)
    (hlast : arrayLast? (sortedUniqueInts (intValues vs)) = some hi)
    (hspan : hi - lo + 1 ≤ 4096) :
    (DomC.bitset lo
      (bitsetOfValues lo (bitsetWordCount (hi - lo + 1).toNat)
        (sortedUniqueInts (intValues vs)).toList)).mem (.int i) = true ↔
      .int i ∈ Dom.enum ⟨.general vs⟩ := by
  have hpair : (sortedUniqueInts (intValues vs)).toList.Pairwise (fun a b => a < b) :=
    pairwise_sortedUniqueInts _
  have hmem : ∀ x : Int, x ∈ (sortedUniqueInts (intValues vs)).toList ↔ .int x ∈ vs := by
    intro x
    rw [mem_sortedUniqueInts]
    exact mem_intValues
  have hbounds : ∀ x : Int, .int x ∈ vs → lo ≤ x ∧ x ≤ hi := by
    intro x hx
    have hxq : x ∈ (sortedUniqueInts (intValues vs)).toList := (hmem x).mpr hx
    exact ⟨arrayHead?_le hhead hpair hxq, le_arrayLast? hlast hpair hxq⟩
  have hhi_mem : hi ∈ (sortedUniqueInts (intValues vs)).toList := by
    obtain ⟨hpos, hlast0⟩ := arrayLast?_eq_some hlast
    refine List.mem_iff_getElem.mpr ⟨(sortedUniqueInts (intValues vs)).size - 1, ?_, ?_⟩
    · simp
      omega
    · rw [Array.getElem_toList]
      exact hlast0
  have hlo_le_hi : lo ≤ hi :=
    arrayHead?_le hhead hpair hhi_mem
  have hspanpos : 0 < hi - lo + 1 := by omega
  have hnatpos : 0 < (hi - lo + 1).toNat := by
    have hcast : ((hi - lo + 1).toNat : Int) = hi - lo + 1 :=
      Int.toNat_of_nonneg (by omega)
    omega
  have hb : ∀ x ∈ (sortedUniqueInts (intValues vs)).toList,
      (x - lo).toNat / 64 < bitsetWordCount (hi - lo + 1).toNat := by
    intro x hx
    have hxmem := hmem x |>.mp hx
    obtain ⟨hxlo, hxhi⟩ := hbounds x hxmem
    have hklt : (x - lo).toNat < (hi - lo + 1).toNat :=
      (Int.toNat_lt_toNat hspanpos).mpr (by omega)
    have hle : (hi - lo + 1).toNat ≤ bitsetWordCount (hi - lo + 1).toNat * 64 := by
      unfold bitsetWordCount
      omega
    exact Nat.div_lt_of_lt_mul (by omega)
  by_cases hlt : i - lo < 0
  · simp only [DomC.mem]
    rw [if_pos hlt, Dom.enum]
    simp only [Bool.false_eq_true, false_iff]
    intro hv
    exact absurd (hbounds i hv).1 (by omega)
  · simp only [DomC.mem]
    rw [if_neg hlt, Dom.enum]
    have hfold := bitsetMem_foldl_setBit (lo := lo)
      (nwords := bitsetWordCount (hi - lo + 1).toNat)
      (sortedUniqueInts (intValues vs)).toList
      (Array.replicate (bitsetWordCount (hi - lo + 1).toNat) 0) (by simp) hb
      (i - lo).toNat
    rw [bitsetMem_replicate_zero] at hfold
    simp only [or_false, Bool.false_eq_true] at hfold
    have hwords : bitsetMem (bitsetOfValues lo
        (bitsetWordCount (hi - lo + 1).toNat)
        (sortedUniqueInts (intValues vs)).toList) (i - lo).toNat =
        bitsetMem ((sortedUniqueInts (intValues vs)).toList.foldl
          (fun a v => setBitWord a (v - lo).toNat)
          (Array.replicate (bitsetWordCount (hi - lo + 1).toNat) 0))
          (i - lo).toNat := rfl
    rw [hwords, hfold]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hxlo : lo ≤ x := (hbounds x (hmem x |>.mp hx)).1
      have heq : x = i := by
        have h1 : ((x - lo).toNat : Int) = x - lo :=
          Int.toNat_of_nonneg (by omega)
        have h2 : ((i - lo).toNat : Int) = i - lo :=
          Int.toNat_of_nonneg (by omega)
        omega
      simpa [heq] using (hmem x).mp hx
    · intro hv
      exact ⟨i, (hmem i).mpr hv, rfl⟩

theorem ofDom?_general_bool_eq {vs : List Value} {c : DomC}
    (hshape : vs.all (fun v => match v with | .bool _ => true | _ => false) = true)
    (h : DomC.ofDom? ⟨.general vs⟩ = some c) :
    c = .bool (boolFold vs) := by
  cases vs with
  | nil => simp [DomC.ofDom?] at h
  | cons v0 rest =>
      cases v0 with
      | bool b =>
          simp only [DomC.ofDom?] at h
          split at h
          · cases h
            rfl
          · rename_i hneg
            exact absurd hshape hneg
      | int i =>
          have hv0 : (match Value.int i with | .bool _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.int i) (by simp)
          simp at hv0
      | setOfInt s =>
          have hv0 : (match Value.setOfInt s with | .bool _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.setOfInt s) (by simp)
          simp at hv0
      | array a =>
          have hv0 : (match Value.array a with | .bool _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.array a) (by simp)
          simp at hv0

/-- Shape of the conversion of an all-integer enumeration: the head and last
values, plus the two possible compact representations (a medium-span bitset
or a wide interval minus its complement holes). -/
theorem ofDom?_general_int_cases {vs : List Value} {c : DomC}
    (hshape : vs.all (fun v => match v with | .int _ => true | _ => false) = true)
    (h : DomC.ofDom? ⟨.general vs⟩ = some c) :
    ∃ lo hi, arrayHead? (sortedUniqueInts (intValues vs)) = some lo
      ∧ arrayLast? (sortedUniqueInts (intValues vs)) = some hi
      ∧ ((hi - lo + 1 ≤ 4096 ∧ c = .bitset lo
            (bitsetOfValues lo
              (bitsetWordCount (hi - lo + 1).toNat)
              (sortedUniqueInts (intValues vs)).toList))
         ∨ c = .boundsHoles lo hi
            (complementHoles lo hi (sortedUniqueInts (intValues vs)))
         ∨ c = .sparse (sortedUniqueInts (intValues vs))) := by
  cases vs with
  | nil => simp [DomC.ofDom?] at h
  | cons v0 rest =>
      cases v0 with
      | int i0 =>
          simp only [DomC.ofDom?] at h
          split at h
          · rename_i hhall
            split at h
            · rename_i hx1 hx2 a b hhead hlast
              by_cases hspan : b - a + 1 ≤ 4096
              · rw [if_pos hspan] at h
                cases h
                exact ⟨a, b, hhead, hlast, Or.inl ⟨hspan, rfl⟩⟩
              · rw [if_neg hspan] at h
                by_cases hdense :
                    (b - a + 1).toNat -
                      (sortedUniqueInts (intValues (Value.int i0 :: rest))).size ≤ 4096
                · rw [if_pos hdense] at h
                  cases h
                  exact ⟨a, b, hhead, hlast, Or.inr (Or.inl rfl)⟩
                · rw [if_neg hdense] at h
                  cases h
                  exact ⟨a, b, hhead, hlast, Or.inr (Or.inr rfl)⟩
            · simp at h
          · rename_i hneg
            exact absurd hshape hneg
      | bool b =>
          have hv0 : (match Value.bool b with | .int _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.bool b) (by simp)
          simp at hv0
      | setOfInt s =>
          have hv0 : (match Value.setOfInt s with | .int _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.setOfInt s) (by simp)
          simp at hv0
      | array a =>
          have hv0 : (match Value.array a with | .int _ => true | _ => false) = true :=
            (List.all_eq_true.mp hshape) (.array a) (by simp)
          simp at hv0

theorem DomC.mem_iff (d : Dom) (c : DomC) (h : DomC.ofDom? d = some c) (v : Value) :
    c.mem v = true ↔ v ∈ d := by
  rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum]
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
        cases isBool with
        | true =>
            simp only [DomC.ofDom?] at h
            cases h
            exact mem_small_true
        | false =>
            simp only [DomC.ofDom?] at h
            cases h
            cases v with
            | int i => exact mem_small_false
            | bool b =>
                constructor
                · intro hh; simp [DomC.mem] at hh
                · intro hh
                  simp only [Dom.enum] at hh
                  rw [List.mem_map] at hh
                  obtain ⟨x, -, hx⟩ := hh
                  cases hx
            | setOfInt s =>
                constructor
                · intro hh; simp [DomC.mem] at hh
                · intro hh
                  simp only [Dom.enum] at hh
                  rw [List.mem_map] at hh
                  obtain ⟨x, -, hx⟩ := hh
                  cases hx
            | array a =>
                constructor
                · intro hh; simp [DomC.mem] at hh
                · intro hh
                  simp only [Dom.enum] at hh
                  rw [List.mem_map] at hh
                  obtain ⟨x, -, hx⟩ := hh
                  cases hx
    | holes lo hi hs =>
        simp only [DomC.ofDom?] at h
        split at h
        · rename_i hspan
          cases h
          exact mem_holes_bitset_ofDom hspan.1 hspan.2
        · cases h
          exact mem_holes_ofDom
    | general vs =>
        cases vs with
        | nil =>
            simp only [DomC.ofDom?] at h
            cases h
        | cons v0 rest =>
            cases v0 with
            | bool b =>
                by_cases hall : (Value.bool b :: rest).all
                    (fun v => match v with | .bool _ => true | _ => false) = true
                · have hc := ofDom?_general_bool_eq hall h
                  rw [hc]
                  exact mem_general_bool hall
                · simp only [DomC.ofDom?] at h
                  split at h
                  · rename_i hhall
                    exact absurd hhall hall
                  · cases h
            | int i0 =>
                by_cases hall : (Value.int i0 :: rest).all
                    (fun v => match v with | .int _ => true | _ => false) = true
                · obtain ⟨lo, hi, hhead, hlast, hc | hc | hc⟩ :=
                    ofDom?_general_int_cases hall h
                  · obtain ⟨hspan, hc⟩ := hc
                    rw [hc]
                    cases v with
                    | int i => exact mem_general_bitset hall hhead hlast hspan
                    | bool b =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | setOfInt s =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | array a =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                  · rw [hc]
                    cases v with
                    | int i => exact mem_general_int hhead hlast
                    | bool b =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | setOfInt s =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | array a =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                  · rw [hc]
                    cases v with
                    | int i => exact mem_general_sparse
                    | bool b =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | setOfInt s =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                    | array a =>
                        constructor
                        · intro hh; simp [DomC.mem] at hh
                        · intro hh
                          obtain ⟨i, hi'⟩ := eq_int_of_mem_all_int hall hh
                          cases hi'
                · simp only [DomC.ofDom?] at h
                  split at h
                  · rename_i hhall
                    exact absurd hhall hall
                  · cases h
            | setOfInt s =>
                simp only [DomC.ofDom?] at h
                cases h
            | array a =>
                simp only [DomC.ofDom?] at h
                cases h

theorem DomC.ofDom?_wf (d : Dom) (c : DomC) (h : DomC.ofDom? d = some c) :
    c.WF := by
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
        cases isBool with
        | true =>
            simp only [DomC.ofDom?] at h
            cases h
            simp only [DomC.WF]
            exact uint8_ofNat_and_three_and_three _
        | false =>
            simp only [DomC.ofDom?] at h
            cases h
            simp [DomC.WF]
    | holes lo hi hs =>
        simp only [DomC.ofDom?] at h
        split at h
        · cases h
          simp [DomC.WF]
        · cases h
          refine ⟨pairwise_sortedUniqueInts _, ?_⟩
          intro x hx
          have hx' : x ∈ (hs.toArray.filter
              (fun h => decide (lo ≤ h) && decide (h ≤ hi))).toList :=
            (mem_sortedUniqueInts).mp hx
          exact (mem_filter_window.mp hx').2
    | general vs =>
        cases vs with
        | nil =>
            simp only [DomC.ofDom?] at h
            cases h
        | cons v0 rest =>
            cases v0 with
            | bool b =>
                by_cases hall : (Value.bool b :: rest).all
                    (fun v => match v with | .bool _ => true | _ => false) = true
                · have hc := ofDom?_general_bool_eq hall h
                  rw [hc]
                  simp only [DomC.WF]
                  exact boolFold_and_three _
                · simp only [DomC.ofDom?] at h
                  split at h
                  · rename_i hhall
                    exact absurd hhall hall
                  · cases h
            | int i0 =>
                by_cases hall : (Value.int i0 :: rest).all
                    (fun v => match v with | .int _ => true | _ => false) = true
                · obtain ⟨lo, hi, -, -, hc | hc | hc⟩ := ofDom?_general_int_cases hall h
                  · obtain ⟨-, hc⟩ := hc
                    rw [hc]
                    simp [DomC.WF]
                  · rw [hc]
                    refine ⟨pairwise_complementHoles lo hi _, ?_⟩
                    intro x hx
                    have hx' := (mem_complementHoles (lo := lo) (hi := hi)
                      (vs := sortedUniqueInts (intValues (Value.int i0 :: rest)))
                      (hs := pairwise_sortedUniqueInts _)).mp hx
                    exact ⟨hx'.1, hx'.2.1⟩
                  · rw [hc]
                    exact pairwise_sortedUniqueInts _
                · simp only [DomC.ofDom?] at h
                  split at h
                  · rename_i hhall
                    exact absurd hhall hall
                  · cases h
            | setOfInt s =>
                simp only [DomC.ofDom?] at h
                cases h
            | array a =>
                simp only [DomC.ofDom?] at h
                cases h

/-! ## Assignment fit at the compiled problem -/

/-- The `Solver.Propagation.Problem` view of a compiled problem used by
    `fitsB`.  Fit reads only `domains`; the clause database is irrelevant
    here (the search loop reconstructs the seed clauses separately in
    `Engine.Search.propagationProblem`). -/
def domProblem (p : CompiledProblem DomConstraint) :
    Solver.Propagation.Problem DomConstraint Unit :=
  { names := p.names
    domains := p.domains
    constraints := p.constraints
    objective := ()
    clauses := [] }

/-- Every enumerated assignment fits its domain box.  This is the local
    form of `Solver.Propagation.allAssigns_fits`, restated for the compact
    carrier so the domain module does not import the frame-filter layer. -/
theorem allAssigns_fits_dom : ∀ (ds : List Dom) (a : Assignment),
    a ∈ allAssigns ds → Assignment.Fits ds a := by
  intro ds
  induction ds with
  | nil =>
      intro a ha
      have he : a = [] := by simpa [allAssigns] using ha
      subst he
      exact ⟨rfl, by simp⟩
  | cons d rest ih =>
      intro a ha
      cases hd : DomainElems.elems d with
      | nil =>
          have hnil : allAssigns (d :: rest) = [] := by
            simp only [allAssigns, hd]
          rw [hnil] at ha
          exact absurd ha (by simp)
      | cons v vs =>
          obtain ⟨w, hw, suffix, hs, rfl⟩ :=
            (mem_allAssigns_cons hd rest a).mp ha
          obtain ⟨hlen, hmem⟩ := ih suffix hs
          refine ⟨by simp [hlen], ?_⟩
          intro i w' hw'
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hw'
              subst hw'
              simpa using (DomainLike.mem_iff d w).mpr (by simpa [hd] using hw)
          | succ i =>
              exact hmem i w' (by simpa using hw')

/-- `fitsB` decides the semantic fit relation on any Core/Propagation
    problem. -/
theorem fitsB_iff_mem_allAssigns_problem {Constraint Objective : Type}
    (p : Solver.Propagation.Problem Constraint Objective) (a : List Value) :
    fitsB p a = true ↔ a ∈ allAssigns p.domains := by
  rw [fitsB_iff]
  exact ⟨fun h => mem_allAssigns_of_getElem? p.domains a h.1 h.2,
    allAssigns_fits_dom p.domains a⟩

/-- `fitsB` on the compiled problem decides membership in the enumerated
    assignment set of its compiled domains. -/
theorem fitsB_iff_mem_allAssigns (p : CompiledProblem DomConstraint)
    (a : List Value) :
    fitsB (domProblem p) a = true ↔ a ∈ allAssigns p.domains := by
  simpa only [domProblem] using
    fitsB_iff_mem_allAssigns_problem (domProblem p) a


end LeanFzn.Engine

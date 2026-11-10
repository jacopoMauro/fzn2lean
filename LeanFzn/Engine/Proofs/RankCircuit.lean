/-
File: LeanFzn/Engine/Proofs/RankCircuit.lean

Purpose:
  Soundness of the T2 verified rank-decomposition checker (PLAN.md
  phase 5).  The untrusted recognizer and its verified checker live in
  `LeanFzn.Compiler.RankCircuit`; this file proves that every clause
  emitted by `rankCircuitClauses` is entailed by any problem whose
  recognizer proposal passes the checker.

  The mathematical content is the 2-cycle exclusion: the reified rows of
  a Gecode rank decomposition force `rank[pred_i] = nextVal (rank i)`,
  where `nextVal` increments modulo `n` (1..n with `n + 1 = 1`).  If two
  distinct nodes were mutual predecessors, both ranks would be one step
  ahead of each other, which is impossible for `n > 2`.

Dependencies:
  - LeanFzn.Engine.Analyze: `allAssigns`, `accepts`, slot membership.
  - LeanFzn.Engine.Props.Linear: `accepts_satisfiedB`.
  - LeanFzn.Compiler.RankCircuit: checker and certificate.

DAG:
  Engine.Analyze + Compiler.RankCircuit -> Engine.Proofs.RankCircuit
  (T2 evidence; the runtime search does not import this module)
-/
import LeanFzn.Engine.Analyze
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Linear
import LeanFzn.Compiler.RankCircuit

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## §0 Slot and arithmetic helpers -/

/-- The rank successor: `1, 2, ..., n, 1, ...`. -/
def nextVal (n : Nat) (r : Int) : Int :=
  if r = (n : Int) then 1 else r + 1

/-- A slot whose value is `v` has that value in the problem's domain. -/
theorem mem_domains_getD_of_getElem? {p : CompiledProblem DomConstraint}
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    {k : Nat} {v : Value} (hk : a[k]? = some v) :
    v ∈ p.domains.getD k Dom.empty := by
  have hlen : a.length = p.domains.length := allAssigns_length_eq ha
  have hklt : k < p.domains.length := by
    have hka : k < a.length := (List.getElem?_eq_some_iff).mp hk |>.1
    omega
  obtain ⟨w, hw, hmem⟩ := mem_allAssigns_getElem_mem ha hklt
  rw [hw] at hk
  have hwv : w = v := Option.some.inj hk
  subst hwv
  simpa [domEmpty_eq] using hmem

/-- The integer view of a slot read. -/
theorem slot_int_of_getElem? {a : Assignment} {s : Nat} {x : Int}
    (h : a[s]? = some (.int x)) : slotInt a s = some x := by
  simp [slotInt, h, Value.intView]

/-- A `getElem?` read determines the bang read. -/
theorem getElem!_eq_of_getElem? {a : Assignment} {s : Nat} {v : Value}
    (h : a[s]? = some v) : a[s]! = v := by
  rw [List.getElem!_eq_getElem?_getD, h]
  rfl

/-- `valuesGet1` at a positive natural index is the corresponding list
    `getElem?`. -/
theorem valuesGet1_succ_eq_getElem? {xs : List Value} {i : Nat} {v : Value}
    (h : valuesGet1 xs (((i + 1 : Nat) : Int)) = some v) : xs[i]? = some v := by
  unfold valuesGet1 at h
  split at h
  · rename_i hi
    have hsub : ((((i + 1 : Nat) : Int)).toNat - 1) = i := by
      simp
    simpa [hsub] using h
  · simp at h

/-- A slot whose domain is contained in `1..n` reads an integer in that
    range. -/
theorem slot_int_range {p : CompiledProblem DomConstraint} {n : Nat}
    {a : Assignment} (ha : a ∈ allAssigns p.domains) {s : Nat}
    (hs : s < p.domains.length)
    (hrange : domInRange1B n (p.domains.getD s Dom.empty) = true) :
    ∃ x : Int, a[s]? = some (.int x) ∧ 1 ≤ x ∧ x ≤ (n : Int) := by
  obtain ⟨v, hv, hmem⟩ := mem_allAssigns_getElem_mem ha hs
  obtain ⟨x, rfl, h1, hn⟩ := domInRange1B_spec hrange hmem
  exact ⟨x, hv, h1, hn⟩

/-- A slot whose domain is the singleton `{k}` reads `k`. -/
theorem slot_int_singleton {p : CompiledProblem DomConstraint}
    {a : Assignment} (ha : a ∈ allAssigns p.domains) {s : Nat}
    (hs : s < p.domains.length) {k : Int}
    (h : domIsIntB (p.domains.getD s Dom.empty) k = true) :
    a[s]? = some (.int k) := by
  obtain ⟨v, hv, hmem⟩ := mem_allAssigns_getElem_mem ha hs
  have hvk : v = .int k := domIsIntB_spec h hmem
  simpa [hvk] using hv

/-- Two successor steps do not return to the start for `n > 2`. -/
theorem nextVal_nextVal_ne {n : Nat} (hn : 2 < n) {r : Int}
    (_h1 : 1 ≤ r) (_hr : r ≤ (n : Int)) :
    nextVal n (nextVal n r) ≠ r := by
  by_cases hrn : r = (n : Int)
  · have h1n : (1 : Int) ≠ (n : Int) := by omega
    simp [nextVal, hrn, h1n]
    omega
  · have hstep : nextVal n r = r + 1 := by simp [nextVal, hrn]
    rw [hstep]
    by_cases h2n : r + 1 = (n : Int)
    · have hstep2 : nextVal n (r + 1) = 1 := by simp [nextVal, h2n]
      rw [hstep2]
      omega
    · have hstep2 : nextVal n (r + 1) = r + 1 + 1 := by simp [nextVal, h2n]
      rw [hstep2]
      omega

/-! ## §1 Flat linear rows over singleton/pair coefficient lists -/

theorem dotProduct_single_one (x : Int) :
    dotProduct (intVals [1]) [.int x] = some x := by
  simp [dotProduct, intVals]

theorem dotProduct_pair_one_neg (x y : Int) :
    dotProduct (intVals [1, -1]) [.int x, .int y] = some (x - y) := by
  rw [Int.sub_eq_add_neg]
  simp [dotProduct, intVals]

/-- The three reified rows of one non-folded unit force the rank
    recurrence `y = nextVal n x`. -/
theorem recurrence_of_reif {p : CompiledProblem DomConstraint} {n : Nat}
    {a : Assignment} {rank y b1 b2 b3 : Nat} {x e : Int}
    (hacc : accepts p a = true)
    (hrank : a[rank]? = some (.int x))
    (hy : a[y]? = some (.int e))
    (hb1row : DomConstraint.linEqReif [1] [rank] (n : Int) b1 ∈ p.constraints)
    (hb2row : DomConstraint.linEqReif [1] [y] 1 b2 ∈ p.constraints)
    (hb3row : DomConstraint.linEqReif [1, -1] [y, rank] 1 b3 ∈ p.constraints)
    (hc1row : DomConstraint.boolClauseSlot [b2] [b1] ∈ p.constraints)
    (hc2row : DomConstraint.boolClauseSlot [b1, b3] [] ∈ p.constraints) :
    e = nextVal n x := by
  have hrank_bang : a[rank]! = .int x := getElem!_eq_of_getElem? hrank
  have hy_bang : a[y]! = .int e := getElem!_eq_of_getElem? hy
  have h1 : (DomConstraint.linEqReif [1] [rank] (n : Int) b1).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hb1row)
  obtain ⟨rb1, hb1val, hb1iff⟩ := h1
  have hb1eq : rb1 = true ↔ x = (n : Int) := by
    rw [hb1iff]
    have hmap : (List.map (fun i => a[i]!) [rank]) = [Value.int x] := by
      simp [List.getElem!_eq_getElem?_getD, hrank]
    rw [hmap]
    simp [dotProduct_single_one]
  have h2 : (DomConstraint.linEqReif [1] [y] 1 b2).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hb2row)
  obtain ⟨rb2, hb2val, hb2iff⟩ := h2
  have hb2eq : rb2 = true ↔ e = 1 := by
    rw [hb2iff]
    have hmap : (List.map (fun i => a[i]!) [y]) = [Value.int e] := by
      simp [List.getElem!_eq_getElem?_getD, hy]
    rw [hmap]
    simp [dotProduct_single_one]
  have h3 : (DomConstraint.linEqReif [1, -1] [y, rank] 1 b3).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hb3row)
  obtain ⟨rb3, hb3val, hb3iff⟩ := h3
  have hb3eq : rb3 = true ↔ e - x = 1 := by
    rw [hb3iff]
    have hmap : (List.map (fun i => a[i]!) [y, rank]) =
        [Value.int e, Value.int x] := by
      simp [List.getElem!_eq_getElem?_getD, hy, hrank]
    rw [hmap]
    simp [dotProduct_pair_one_neg]
  have hc1 : (DomConstraint.boolClauseSlot [b2] [b1]).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hc1row)
  have hc1' : slotIsBoolB a b2 true = true ∨ slotIsBoolB a b1 false = true := by
    simpa [DomConstraint.SatisfiedBy] using hc1
  have hb2_or : rb2 = true ∨ rb1 = false := by
    rcases hc1' with h | h
    · left
      have hs := slotIsBoolB_some h
      rw [hb2val] at hs
      simpa using Option.some.inj hs
    · right
      have hs := slotIsBoolB_some h
      rw [hb1val] at hs
      simpa using Option.some.inj hs
  have hc2 : (DomConstraint.boolClauseSlot [b1, b3] []).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hc2row)
  have hc2' : slotIsBoolB a b1 true = true ∨ slotIsBoolB a b3 true = true := by
    simpa [DomConstraint.SatisfiedBy] using hc2
  have hb13_or : rb1 = true ∨ rb3 = true := by
    rcases hc2' with h | h
    · left
      have hs := slotIsBoolB_some h
      rw [hb1val] at hs
      simpa using Option.some.inj hs
    · right
      have hs := slotIsBoolB_some h
      rw [hb3val] at hs
      simpa using Option.some.inj hs
  by_cases hb1 : rb1 = true
  · have hx : x = (n : Int) := hb1eq.mp hb1
    have hrb2 : rb2 = true := by
      rcases hb2_or with h | h
      · exact h
      · rw [hb1] at h
        simp at h
    have he1 : e = 1 := hb2eq.mp hrb2
    rw [he1, hx]
    simp [nextVal]
  · have hxne : x ≠ (n : Int) := fun hx => hb1 (hb1eq.mpr hx)
    have hrb3 : rb3 = true := by
      rcases hb13_or with h | h
      · exact absurd h hb1
      · exact h
    have he : e - x = 1 := hb3eq.mp hrb3
    have he' : e = x + 1 := by omega
    rw [he']
    simp [nextVal, hxne]

/-! ## §2 Domain facts for one checked unit -/

/-- The rank slot of a checked unit reads an integer in `1..n`. -/
theorem unit_rank_range {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) :
    ∃ r : Int, a[c.ranks[i]!]? = some (.int r) ∧
      1 ≤ r ∧ r ≤ (c.n : Int) := by
  have hok := checkRankCircuit_unit hchk hi
  obtain ⟨hbr, _, _, _, hrange, _, _, _, _⟩ := hok
  exact slot_int_range ha hbr hrange

/-- The pinned head slot of a checked unit reads `1`. -/
theorem unit_pin_value {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) :
    a[(c.units[i]!).pin]? = some (.int 1) := by
  have hok := checkRankCircuit_unit hchk hi
  obtain ⟨_, _, hbpin, _, _, hpin, _, _, _⟩ := hok
  exact slot_int_singleton ha hbpin hpin

/-- The folded unit reads rank `1` and result `2`. -/
theorem unit_folded_values {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains)
    (hfold : (c.units[i]!).folded = true) :
    a[c.ranks[i]!]? = some (.int 1) ∧
      a[(c.units[i]!).y]? = some (.int 2) := by
  have hok := checkRankCircuit_unit hchk hi
  obtain ⟨hbr, _, _, hby, _, _, _, hfoldImp, _⟩ := hok
  obtain ⟨hrdom, hydom⟩ := hfoldImp hfold
  exact ⟨slot_int_singleton ha hbr hrdom, slot_int_singleton ha hby hydom⟩

/-- The element row of a checked unit, unpacked. -/
theorem unit_element_sat {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (_ha : a ∈ allAssigns p.domains) (hacc : accepts p a = true) :
    ∃ idx e : Int, a[(c.units[i]!).pred]? = some (.int idx) ∧
      a[(c.units[i]!).y]? = some (.int e) ∧
      valuesGet1 (((c.units[i]!).pin :: c.ranks.tail).map (fun s => a[s]!))
        idx = some (.int e) := by
  have hok := checkRankCircuit_unit hchk hi
  obtain ⟨_, _, _, _, _, _, helem, _, _⟩ := hok
  have hsat : (DomConstraint.arrayVarIntElementSlot
      ((c.units[i]!).pin :: c.ranks.tail) (c.units[i]!).pred
      (c.units[i]!).y).SatisfiedBy a :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc helem)
  obtain ⟨idx, e, hpred, hy, _, hget⟩ := hsat
  exact ⟨idx, e, hpred, hy, hget⟩

/-- Every checked unit satisfies the rank recurrence at its own rank slot. -/
theorem unit_y_eq_nextVal {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) (hacc : accepts p a = true) :
    ∃ r e : Int, a[c.ranks[i]!]? = some (.int r) ∧
      a[(c.units[i]!).y]? = some (.int e) ∧
      e = nextVal c.n r ∧ 1 ≤ r ∧ r ≤ (c.n : Int) := by
  obtain ⟨r, hr, hr1, hrn⟩ := unit_rank_range hchk hi ha
  obtain ⟨_, e, _, hy, _⟩ := unit_element_sat hchk hi ha hacc
  have hok := checkRankCircuit_unit hchk hi
  obtain ⟨hbr, _, _, hby, _, _, _, hfoldImp, hnfoldImp⟩ := hok
  by_cases hf : (c.units[i]!).folded = true
  · obtain ⟨hr1v, hy2v⟩ := hfoldImp hf
    have hrv : a[c.ranks[i]!]? = some (.int 1) := slot_int_singleton ha hbr hr1v
    have hev : a[(c.units[i]!).y]? = some (.int 2) := slot_int_singleton ha hby hy2v
    have hr_eq : r = 1 := by
      have h : some (Value.int r) = some (Value.int 1) := by rw [← hr, hrv]
      simpa using h
    have he_eq : e = 2 := by
      have h : some (Value.int e) = some (Value.int 2) := by rw [← hy, hev]
      simpa using h
    subst hr_eq
    subst he_eq
    refine ⟨1, 2, hrv, hev, ?_, by omega, ?_⟩
    · have hn := checkRankCircuit_n hchk
      have h1n : (1 : Int) ≠ (c.n : Int) := by omega
      simp [nextVal, h1n]
    · have hn := checkRankCircuit_n hchk
      omega
  · have hf' : (c.units[i]!).folded = false := by
      cases h : (c.units[i]!).folded <;> simp_all
    obtain ⟨hb1row, hb2row, hb3row, hc1row, hc2row⟩ := hnfoldImp hf'
    have heq : e = nextVal c.n r :=
      recurrence_of_reif hacc hr hy hb1row hb2row hb3row hc1row hc2row
    exact ⟨r, e, hr, hy, heq, hr1, hrn⟩

/-- Array entry `j` of a unit's element row is the value of rank slot `j`.
    The head slot differs per row, but every row's head pins the same
    `rank[1] = 1` and `ranks[0]` is the first row's head. -/
theorem array_entry_rank {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) {j : Nat} (hj : j < c.n) {e : Int}
    (hget : valuesGet1
      (((c.units[i]!).pin :: c.ranks.tail).map (fun s => a[s]!))
      (((j + 1 : Nat) : Int)) = some (.int e)) :
    a[c.ranks[j]!]? = some (.int e) := by
  have hstep := valuesGet1_succ_eq_getElem? (i := j) hget
  cases j with
  | zero =>
      have h0 : ((c.units[i]!).pin :: c.ranks.tail).map (fun s => a[s]!) =
          a[(c.units[i]!).pin]! :: (c.ranks.tail.map (fun s => a[s]!)) := rfl
      rw [h0] at hstep
      have hhead : (a[(c.units[i]!).pin]! ::
          (c.ranks.tail.map (fun s => a[s]!)))[0]? =
          some (a[(c.units[i]!).pin]!) := rfl
      rw [hhead] at hstep
      have hbang : a[(c.units[i]!).pin]! = .int e :=
        Option.some.inj hstep
      have hpin := unit_pin_value hchk hi ha
      have hpin1 : a[(c.units[i]!).pin]! = .int 1 := getElem!_eq_of_getElem? hpin
      have he1 : e = 1 := by
        have h : (Value.int 1) = Value.int e := by rw [← hpin1, hbang]
        have h' : (1 : Int) = e := by simpa using h
        exact h'.symm
      rw [he1]
      have h0mem : (0 : Nat) ∈ List.range c.n := by
        apply List.mem_range.mpr
        have := checkRankCircuit_n hchk
        omega
      have halign := checkRankCircuit_align hchk
      have hpin0 : a[(c.units[0]!).pin]? = some (.int 1) :=
        unit_pin_value hchk h0mem ha
      rw [halign]
      exact hpin0
  | succ k =>
      obtain ⟨r0, tail, hrfl⟩ : ∃ r0 tail, c.ranks = r0 :: tail := by
        cases h : c.ranks with
        | nil =>
            have := checkRankCircuit_ranks_length hchk
            simp [h] at this
            omega
        | cons r0 tail => exact ⟨r0, tail, rfl⟩
      have htail : c.ranks.tail = tail := by simp [hrfl]
      have htlen : tail.length + 1 = c.n := by
        have := checkRankCircuit_ranks_length hchk
        simp [hrfl] at this
        omega
      have hklt : k < tail.length := by omega
      have hb2 : tail[k]! = tail[k] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
        rfl
      have harr : ((c.units[i]!).pin :: c.ranks.tail).map (fun s => a[s]!) =
          a[(c.units[i]!).pin]! :: (tail.map (fun s => a[s]!)) := by
        simp [htail]
      rw [harr] at hstep
      simp only [List.getElem?_cons_succ, List.getElem?_map] at hstep
      have h1 : tail[k]? = some tail[k] := List.getElem?_eq_getElem hklt
      rw [h1] at hstep
      simp only [Option.map_some] at hstep
      have hbang : a[tail[k]!]! = .int e := by
        have hb : tail[k]! = tail[k] := hb2
        rw [hb]
        exact Option.some.inj hstep
      have hbnd : c.ranks[k + 1]! < a.length := by
        have hokj := checkRankCircuit_unit hchk (List.mem_range.mpr (by simpa using hj))
        obtain ⟨hbrj, _, _, _, _, _, _, _, _⟩ := hokj
        have := allAssigns_length_eq ha
        omega
      have hcoord : c.ranks[k + 1]! = tail[k]! := by simp [hrfl]
      have hs : a[c.ranks[k + 1]!]? = some (a[c.ranks[k + 1]!]) :=
        List.getElem?_eq_getElem hbnd
      have hbang' : a[c.ranks[k + 1]!]! = .int e := by
        rw [hcoord]
        exact hbang
      have hval : a[c.ranks[k + 1]!] = .int e := by
        have htmp := hbang'
        rw [List.getElem!_eq_getElem?_getD, hs] at htmp
        simpa using htmp
      rw [hs]
      exact congrArg some hval

/-- The element row of a checked unit reads rank slot `j` when the unit's
    predecessor value is `j + 1`. -/
theorem unit_y_eq_rank_at {p : CompiledProblem DomConstraint} {c : RankCert}
    (hchk : checkRankCircuit p c = true) {i : Nat}
    (hi : i ∈ List.range c.n) {j : Nat} (hj : j < c.n) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) (hacc : accepts p a = true)
    {pv : Int} (hpred : a[(c.units[i]!).pred]? = some (.int pv))
    (hpv : pv = ((j + 1 : Nat) : Int)) :
    ∃ e : Int, a[(c.units[i]!).y]? = some (.int e) ∧
      a[c.ranks[j]!]? = some (.int e) := by
  obtain ⟨idx, e, hpred', hy, hget⟩ := unit_element_sat hchk hi ha hacc
  have hidx : idx = ((j + 1 : Nat) : Int) := by
    have h : some (Value.int idx) = some (Value.int pv) := hpred'.symm.trans hpred
    have hidxpv : idx = pv := by simpa using Option.some.inj h
    rw [hidxpv, hpv]
  rw [hidx] at hget
  exact ⟨e, hy, array_entry_rank hchk hi ha hj hget⟩

/-! ## §3 The 2-cycle exclusion -/

/-- Every clause of a checked rank decomposition is entailed. -/
theorem rankCircuitClauses_entailed {p : CompiledProblem DomConstraint}
    {c : RankCert} (hchk : checkRankCircuit p c = true)
    {cl : Clause} (hcl : cl ∈ rankCircuitClauses c) : Entailed p cl := by
  intro a ha hacc
  obtain ⟨i, j, hi, hj, hij, rfl⟩ := rankCircuitClauses_mem_inv hcl
  have hj' : j < c.n := List.mem_range.mp hj
  apply Classical.byContradiction
  intro hnot
  have hl1 : posNe (c.units[i]!).pred ((j : Int) + 1) ∈
      [posNe (c.units[i]!).pred ((j : Int) + 1),
       posNe (c.units[j]!).pred ((i : Int) + 1)] := by simp
  have hnot1 : (posNe (c.units[i]!).pred ((j : Int) + 1)).eval a ≠ some true :=
    fun h => hnot ⟨_, hl1, h⟩
  have hl2 : posNe (c.units[j]!).pred ((i : Int) + 1) ∈
      [posNe (c.units[i]!).pred ((j : Int) + 1),
       posNe (c.units[j]!).pred ((i : Int) + 1)] := by simp
  have hnot2 : (posNe (c.units[j]!).pred ((i : Int) + 1)).eval a ≠ some true :=
    fun h => hnot ⟨_, hl2, h⟩
  obtain ⟨pvi, _, hpvi, _, _⟩ := unit_element_sat hchk hi ha hacc
  have hpvi_eq : pvi = (j : Int) + 1 := by
    apply Classical.byContradiction
    intro hne
    have htrue : (posNe (c.units[i]!).pred ((j : Int) + 1)).eval a =
        some true :=
      (eval_posNe_iff a _ _).mpr ⟨pvi, slot_int_of_getElem? hpvi, hne⟩
    exact hnot1 htrue
  obtain ⟨pvj, _, hpvj, _, _⟩ := unit_element_sat hchk hj ha hacc
  have hpvj_eq : pvj = (i : Int) + 1 := by
    apply Classical.byContradiction
    intro hne
    have htrue : (posNe (c.units[j]!).pred ((i : Int) + 1)).eval a =
        some true :=
      (eval_posNe_iff a _ _).mpr ⟨pvj, slot_int_of_getElem? hpvj, hne⟩
    exact hnot2 htrue
  have hpvi_nat : pvi = ((j + 1 : Nat) : Int) := by
    rw [hpvi_eq]
    simp
  have hpvj_nat : pvj = ((i + 1 : Nat) : Int) := by
    rw [hpvj_eq]
    simp
  obtain ⟨ri, ei, hri, hyi, hei, hri1, hrin⟩ :=
    unit_y_eq_nextVal hchk hi ha hacc
  obtain ⟨eij, hyi2, hrj⟩ :=
    unit_y_eq_rank_at hchk hi hj' ha hacc hpvi hpvi_nat
  have heij : eij = ei := by
    have h : some (Value.int eij) = some (Value.int ei) := by rw [← hyi2, ← hyi]
    simpa using h
  have hrj_ei : a[c.ranks[j]!]? = some (.int ei) := by
    rw [hrj]
    simpa using congrArg (fun z : Int => some (Value.int z)) heij
  obtain ⟨rj, ej, hrjv, hyj, hej, hrj1, hrjn⟩ :=
    unit_y_eq_nextVal hchk hj ha hacc
  have hrj_eq_ei : rj = ei := by
    have h : some (Value.int rj) = some (Value.int ei) := by rw [← hrjv, hrj_ei]
    simpa using h
  obtain ⟨eji, hyj2, hri2⟩ :=
    unit_y_eq_rank_at hchk hj (List.mem_range.mp hi) ha hacc hpvj hpvj_nat
  have heji : eji = ej := by
    have h : some (Value.int eji) = some (Value.int ej) := by rw [← hyj2, ← hyj]
    simpa using h
  have hri_ej : a[c.ranks[i]!]? = some (.int ej) := by
    rw [hri2]
    simpa using congrArg (fun z : Int => some (Value.int z)) heji
  have hri_eq_ej : ri = ej := by
    have h : some (Value.int ri) = some (Value.int ej) := by rw [← hri, hri_ej]
    simpa using h
  have hcontra : nextVal c.n (nextVal c.n ri) = ri := by
    calc
      nextVal c.n (nextVal c.n ri) = nextVal c.n ei := by rw [← hei]
      _ = nextVal c.n rj := by rw [← hrj_eq_ei]
      _ = ej := by rw [← hej]
      _ = ri := by rw [hri_eq_ej]
  exact nextVal_nextVal_ne (checkRankCircuit_n hchk) hri1 hrin hcontra

/-- **THE ENTAILMENT HALF**: every seed clause of a checked rank
    decomposition is entailed by the compiled problem. -/
theorem rankCircuitSeeds_entailed {p : CompiledProblem DomConstraint}
    {cl : Clause} (h : cl ∈ rankCircuitSeeds p) : Entailed p cl := by
  obtain ⟨c, _, hchk, hcl⟩ := rankCircuitSeeds_mem_inv h
  exact rankCircuitClauses_entailed hchk hcl

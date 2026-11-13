/-
File: LeanFzn/Engine/Props/Element.lean

Dedicated `PropV2` propagators for the three element families:

* `arrayIntElementSlot xs i k` (constant integer table),
* `arrayVarIntElementSlot is i k` (variable integer table),
* `arrayVarBoolElementSlot is i k` (variable Boolean table).

Every emitted clause is an `EClause.ofLiterals` with a proved `Entailed p`
fact.  The propagators follow the output contracts of
`Props/Ne.lean` and `Props/Linear.lean`: conflict literals are false on
the current view, a prune pivot is unassigned, and every other literal
of its reason is false.  Prunes are only emitted when they keep the
pruned domain non-empty; a batch that would remove every value is
replaced by `.fix` (or by a provable conflict).
-/
import LeanFzn.Engine.Prop
import LeanFzn.Engine.Props.Linear
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.Order
import LeanFzn.Solver.Propagation.Proofs.Fam.Element
import LeanFzn.Solver.Propagation.Proofs.Fam.VarElement
import LeanFzn.Solver.Propagation.Proofs.Fam.BoolElement

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Shared helpers -/

/-- The four integer hull endpoints of the index and result slots. -/
def intPairBounds (d₁ d₂ : DomC) : Option (Int × Int × Int × Int) :=
  match d₁.lo?, d₁.hi?, d₂.lo?, d₂.hi? with
  | some a, some b, some c, some d => some (a, b, c, d)
  | _, _, _, _ => none

/-- Integer candidates of a compact domain: the members of its hull, in
ascending order, capped at 4097 values.  A cap hit yields the empty list
(no propagation), never an incomplete list that a proof could mistake
for the whole domain. -/
def intCandidatesAux (d : DomC) (lo : Int) : List Nat → List Int
  | [] => []
  | n :: ns =>
      if d.mem (.int (lo + (n : Int))) then
        (lo + (n : Int)) :: intCandidatesAux d lo ns
      else intCandidatesAux d lo ns

/-- Set-bit scan of one 64-bit word: values `base + i` for the set bits
`i`, accumulated in reverse order (newest first). -/
def intCandidatesWordGo (base : Int) (w : UInt64) : Nat → Nat → List Int → List Int
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
      if (w &&& u64bit i) != 0 then
        intCandidatesWordGo base w fuel (i + 1) ((base + (i : Int)) :: acc)
      else intCandidatesWordGo base w fuel (i + 1) acc

/-- Scan the words of a bit-set domain in ascending order, accumulating
values in reverse order. -/
def intCandidatesBitsetGo (base : Int) (words : Array UInt64) :
    Nat → Nat → List Int → List Int
  | 0, _, acc => acc
  | fuel + 1, wi, acc =>
      match words[wi]? with
      | some w =>
          intCandidatesBitsetGo base words fuel (wi + 1)
            (intCandidatesWordGo (base + ((wi * 64 : Nat) : Int)) w 64 0 acc)
      | none => acc

/-- The integer members of a bit-set domain, in ascending order. -/
def intCandidatesBitset (lo : Int) (words : Array UInt64) : List Int :=
  (intCandidatesBitsetGo lo words words.size 0 []).reverse

/-- Integer members of the hull of `d`, capped at 4097 values.  Bit-set
domains walk their set bits directly; the other representations keep the
hull scan. -/
def intCandidates (d : DomC) : List Int :=
  match d with
  | .bitset lo words =>
      match (DomC.bitset lo words).lo?, (DomC.bitset lo words).hi? with
      | some a, some b =>
          if b - a + 1 > 4097 then [] else intCandidatesBitset lo words
      | _, _ => []
  | _ =>
      match d.lo?, d.hi? with
      | some lo, some hi =>
          if hi - lo + 1 > 4097 then []
          else intCandidatesAux d lo (List.range (hi - lo + 1).toNat)
      | _, _ => []

theorem mem_intCandidatesAux {d : DomC} {lo : Int} {ns : List Nat} {v : Int}
    (h : v ∈ intCandidatesAux d lo ns) : d.mem (.int v) = true := by
  induction ns with
  | nil => simp [intCandidatesAux] at h
  | cons n ns ih =>
      simp only [intCandidatesAux] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | htail
        · assumption
        · exact ih htail
      · exact ih h

theorem mem_intCandidatesWordGo {w : UInt64} {P : Int → Prop} {wbase : Int} :
    ∀ (fuel i : Nat) (acc : List Int), i + fuel = 64 →
      (∀ j, j < 64 → w.toNat.testBit j = true → P (wbase + (j : Int))) →
      (∀ v ∈ acc, P v) →
      ∀ v ∈ intCandidatesWordGo wbase w fuel i acc, P v := by
  intro fuel
  induction fuel with
  | zero =>
      intro i acc hinv hP hacc v hv
      rw [intCandidatesWordGo.eq_1] at hv
      exact hacc v hv
  | succ fuel ih =>
      intro i acc hinv hP hacc v hv
      have hi : i < 64 := by omega
      rw [intCandidatesWordGo.eq_2] at hv
      by_cases hbit : (w &&& u64bit i) != 0
      · rw [if_pos hbit] at hv
        apply ih (i + 1) ((wbase + (i : Int)) :: acc) (by omega) hP ?_ v hv
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hP i hi ((uint64_and_u64bit_ne_zero_iff w hi).mp hbit)
        · exact hacc u hu
      · rw [if_neg hbit] at hv
        exact ih (i + 1) acc (by omega) hP hacc v hv

/-- A set bit in a stored word is a member of the bit-set array. -/
theorem bitsetMem_eq_true_of_getElem?_testBit {words : Array UInt64} {wi j : Nat}
    {w : UInt64} (h : words[wi]? = some w) (hj : j < 64)
    (hb : w.toNat.testBit j = true) :
    bitsetMem words (wi * 64 + j) = true := by
  rw [bitsetMem_eq_true_iff]
  refine ⟨w, ?_, ?_⟩
  · have hdiv : (wi * 64 + j) / 64 = wi := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · omega
      · rw [Nat.succ_mul]
        omega
    rw [hdiv]
    exact h
  · have hmod : (wi * 64 + j) % 64 = j := by
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hmod]
    exact hb

theorem mem_intCandidatesBitsetGo {base : Int} {words : Array UInt64} :
    ∀ (fuel wi : Nat) (acc : List Int), wi + fuel ≤ words.size →
      (∀ v ∈ acc, ∃ n : Nat, v = base + (n : Int) ∧ bitsetMem words n = true) →
      ∀ v ∈ intCandidatesBitsetGo base words fuel wi acc,
        ∃ n : Nat, v = base + (n : Int) ∧ bitsetMem words n = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro wi acc hbound hacc v hv
      rw [intCandidatesBitsetGo.eq_1] at hv
      exact hacc v hv
  | succ fuel ih =>
      intro wi acc hbound hacc v hv
      rw [intCandidatesBitsetGo.eq_2] at hv
      split at hv
      · rename_i w hw
        apply ih (wi + 1) _ (by omega) ?_ v hv
        intro u hu
        refine mem_intCandidatesWordGo (P := fun u =>
            ∃ n : Nat, u = base + (n : Int) ∧ bitsetMem words n = true)
          (wbase := base + ((wi * 64 : Nat) : Int)) 64 0 acc (by omega) ?_ hacc u hu
        intro j hj hbit
        refine ⟨wi * 64 + j, ?_, ?_⟩
        · push_cast
          omega
        · exact bitsetMem_eq_true_of_getElem?_testBit hw hj hbit
      · exact hacc v hv

theorem mem_intCandidatesBitset {lo : Int} {words : Array UInt64} {v : Int}
    (h : v ∈ intCandidatesBitset lo words) :
    (DomC.bitset lo words).mem (.int v) = true := by
  unfold intCandidatesBitset at h
  rw [List.mem_reverse] at h
  obtain ⟨n, hv, hmem⟩ := mem_intCandidatesBitsetGo words.size 0 []
    (by omega) (by intro u hu; simp at hu) v h
  subst hv
  have hsub : lo + (n : Int) - lo = (n : Int) := by omega
  simp [DomC.mem, hsub, hmem]

theorem mem_intCandidates {d : DomC} {v : Int}
    (h : v ∈ intCandidates d) : d.mem (.int v) = true := by
  unfold intCandidates at h
  split at h
  · split at h
    · rename_i a b hlo hhi
      split at h
      · simp at h
      · exact mem_intCandidatesBitset h
    · simp at h
  · split at h
    · rename_i lo hi hlo hhi
      split at h
      · simp at h
      · exact mem_intCandidatesAux h
    · simp at h

/-- Keep a prune batch only when it leaves at least one value in the
domain being pruned. -/
def safePrunes (d : DomC) (ps : List (Literal × Clause)) :
    List (Literal × Clause) :=
  if ps.length < d.size then ps else []

/-- Stripping the safety guard from a prune batch. -/
theorem mem_safePrunes {d : DomC} {ps : List (Literal × Clause)}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ safePrunes d ps) : (l, reason) ∈ ps := by
  unfold safePrunes at h
  split at h
  · exact h
  · simp at h

/-- When an integer value is absent from `memIntView`, the literal
`x ≠ v` evaluates to `false` on the compact domain. -/
theorem DomC.evalLit_negNe_false_of_not_memIntView (d : DomC) (s : Nat) {v : Int}
    (h : d.memIntView v = false) : d.evalLit (negNe s v) = some false := by
  unfold DomC.evalLit negNe
  dsimp only
  by_cases hfix : d.fixedValue.isSome = true
  · simp [hfix, h]
  · simp [hfix, h]

/-- When a domain is fixed to the integer `v`, `x ≠ v` evaluates to
`false`. -/
theorem DomC.evalLit_posNe_false_of_fixed_int {d : DomC} {s : Nat} {v : Int}
    (h : d.fixedValue = some (.int v)) (hm : d.mem (.int v) = true) :
    d.evalLit (posNe s v) = some false :=
  DomC.evalLit_posNe_of_fixed h hm

/-- A pruned literal batch is built from an attached list of pure pairs,
so every emitted clause carries a proof of entailment. -/
def mkElemPruneArray (p : CompiledProblem DomConstraint) (T : LitTable)
    (pairs : List (Literal × Clause))
    (H : ∀ (l : Literal) (reason : Clause), (l, reason) ∈ pairs → Entailed p reason) :
    Array (PLit × EClause p T) :=
  (pairs.attach.map fun x =>
    (pLit x.1.1, EClause.ofLiterals p T x.1.2 (H x.1.1 x.1.2 x.2))).toArray

theorem mkElemPruneArray_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (pairs : List (Literal × Clause))
    (H : ∀ (l : Literal) (reason : Clause), (l, reason) ∈ pairs → Entailed p reason)
    {q : PLit × EClause p T} (hq : q ∈ (mkElemPruneArray p T pairs H).toList) :
    ∃ (l : Literal) (reason : Clause), (l, reason) ∈ pairs ∧
      q.1.lit = l ∧ T.decodeClause q.2.lits = reason := by
  unfold mkElemPruneArray at hq
  rw [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  refine ⟨x.1.1, x.1.2, x.2, rfl, ?_⟩
  exact LitTable.decodeClause_map_pLit T x.1.2

/-! ## Stage 1: the constant-table element -/

/-- The pure decision of the constant-table propagator. -/
inductive AieOut where
  | fix
  | conflict (ls : List Literal)
  | prune (pairs : List (Literal × Clause))

/-- The fixed-index result-bounds prunes.  Both pivots preserve the
entry value `v`, and both reasons are entailed by the pin
`i = idx` together with the table read. -/
def aieFixedPrunes (dk : DomC) (i k : Nat) (idx v : Int) :
    List (Literal × Clause) :=
  (if dk.evalLit (posLe k v) = none then
      [(posLe k v, [posLe k v, posNe i idx])]
    else []) ++
  (if dk.evalLit (negLe k (v - 1)) = none then
      [(negLe k (v - 1), [negLe k (v - 1), posNe i idx])]
    else [])

/-- Does the current index domain contain a value whose entry lies in
the result domain? -/
def aieHasGood (di dk : DomC) (xs : List Int) : Bool :=
  (intCandidates di).any fun v =>
    match valuesGet1 (xs.map Value.int) v with
    | some (.int w) => dk.memIntView w
    | _ => false

/-- Unsupported index-value prunes in the general branch: out-of-range
values get the unit clause; an in-range entry outside the result domain
gets the escape literal `k ≠ entry`.  The size guard ensures the batch
leaves at least one value when a good candidate exists. -/
def aieBadIndexPrunes (di dk : DomC) (xs : List Int) (i k : Nat) :
    List (Literal × Clause) :=
  (intCandidates di).filterMap fun v =>
    match valuesGet1 (xs.map Value.int) v with
    | none =>
        if 1 < di.size then some (posNe i v, [posNe i v]) else none
    | some (.int w) =>
        if dk.memIntView w then none
        else if 1 < di.size then some (posNe i v, [posNe i v, negNe k w])
        else none
    | some _ => none

/-- The integer table entries at the hull positions `lo..hi`.  The
caller caps the span; a non-positive span gives the empty list.  The
array projection is hoisted so the scan is linear in the table size. -/
def aieEntries (xs : List Int) (lo hi : Int) : List Int :=
  let xa := (xs.map Value.int).toArray
  (List.range (hi - lo + 1).toNat).filterMap fun n =>
    match valuesGet1A xa (lo + Int.ofNat n) with
    | some (.int v) => some v
    | _ => none

/-- `aieEntries` with the table array already hoisted by the caller. -/
def aieEntriesA (xa : Array Value) (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).filterMap fun n =>
    match valuesGet1A xa (lo + Int.ofNat n) with
    | some (.int v) => some v
    | _ => none

theorem aieEntriesA_eq (xs : List Int) (lo hi : Int) :
    aieEntriesA (xs.map Value.int).toArray lo hi = aieEntries xs lo hi := by
  unfold aieEntriesA aieEntries
  rfl

/-- Every in-range table read belongs to the segment entry list. -/
theorem mem_aieEntries {xs : List Int} {lo hi idx v : Int}
    (hlo : lo ≤ idx) (hhi : idx ≤ hi)
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v)) :
    v ∈ aieEntries xs lo hi := by
  unfold aieEntries
  dsimp only
  rw [List.mem_filterMap]
  refine ⟨(idx - lo).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    have hpos : (0 : Int) ≤ idx - lo := by omega
    rw [Int.toNat_lt hpos]
    have hwidth : (0 : Int) ≤ hi - lo + 1 := by omega
    rw [Int.toNat_of_nonneg hwidth]
    omega
  · have hidx : lo + max (idx - lo) 0 = idx := by omega
    have hget : valuesGet1A (xs.map Value.int).toArray idx = some (.int v) := by
      rw [valuesGet1A_toArray]
      exact hent
    simp [hidx, hget]

/-- The minimum of a nonempty entry list is below each of its members. -/
theorem aieEntries_min_le {es : List Int} {m v : Int}
    (hmin : es.min? = some m) (hv : v ∈ es) : m ≤ v :=
  (List.le_min?_iff hmin).1 (Int.le_refl m) v hv

/-- The maximum of a nonempty entry list is above each of its members. -/
theorem aieEntries_le_max {es : List Int} {M v : Int}
    (hmax : es.max? = some M) (hv : v ∈ es) : v ≤ M :=
  (List.max?_le_iff hmax).1 (Int.le_refl M) v hv

/-- Width of the whole table image. -/
def aieTableSpan (xs : List Int) : Int :=
  match xs.min?, xs.max? with
  | some a, some b => b - a + 1
  | _, _ => 0

/-- Hull-bounds prunes: the table image over the current index hull
bounds the result.  The batch is scoped to small, narrow-image tables
and to a full index interval: the wide tdtsp table shapes and index
domains with holes are left to the other element rules, since their
bounds batches change the search trajectory without a measured win.
Both reasons carry the two falsified index-hull escape literals. -/
def aieHullBoundsPrunes (di : DomC) (xs : List Int) (lo hi m M : Int)
    (dk : DomC) (i k : Nat) : List (Literal × Clause) :=
  if 256 < xs.length || 192 < aieTableSpan xs ||
      di.size < (hi - lo + 1).toNat then []
  else
    (if dk.evalLit (negLe k (m - 1)) = none then
        [(negLe k (m - 1), [negLe k (m - 1), posLe i (lo - 1), negLe i hi])]
      else []) ++
    (if dk.evalLit (posLe k M) = none then
        [(posLe k M, [posLe k M, posLe i (lo - 1), negLe i hi])]
      else [])

/-- Result values inside the image hull but absent from the image are
removed; the reason names the two index-hull escape literals. -/
def aieHullValueCandidates (lo hi m M : Int) (es : List Int)
    (dk : DomC) (i k : Nat) : List (Literal × Clause) :=
  (intCandidates dk).filterMap fun w =>
    if w < m || M < w then none
    else if es.contains w then none
    else if dk.evalLit (posNe k w) = none then
      some (posNe k w, [posNe k w, posLe i (lo - 1), negLe i hi])
    else none

/-- The guarded result-value batch.  The size guards keep the
membership scan small; wider tables or results are left unchanged.
The caps bound the batch: an image wider than 192 values (the tdtsp
constant-table shape) is left to bounds, since its value batch changes
the search trajectory without a measured win, and a current result
domain above 192 values is skipped for cost. -/
def aieHullValuePrunes (lo hi m M : Int) (es : List Int)
    (dk : DomC) (i k : Nat) : List (Literal × Clause) :=
  if 64 < es.length || 192 < dk.size || 192 < M - m + 1 then []
  else safePrunes dk (aieHullValueCandidates lo hi m M es dk i k)

/-- The index hull, its table-image bounds, and the image entries.  The
span cap keeps the per-call scan bounded. -/
def aieHullBase (di : DomC) (xs : List Int) :
    Option (Int × Int × Int × Int × List Int) :=
  di.lo?.bind fun lo =>
    di.hi?.bind fun hi =>
      if hi - lo + 1 ≤ 0 || 256 < hi - lo + 1 then none
      else
        let es := aieEntries xs lo hi
        es.min?.bind fun m =>
          es.max?.map fun M => (lo, hi, m, M, es)

/-- Result-side hull prunes for the constant-table element.  A fixed
result cannot be pruned, so its scan is skipped; the combined batch is
size-guarded so it never empties the result domain.  For a small table
whose value batch is active, the bounds batch is logically subsumed by
the value batch and is omitted: the two together change the tower
optimum trajectory, while the value batch alone keeps the measured win. -/
def aieHullPrunes (di dk : DomC) (xs : List Int) (i k : Nat) :
    List (Literal × Clause) :=
  match dk.fixedValue with
  | some _ => []
  | none =>
      match aieHullBase di xs with
      | none => []
      | some (lo, hi, m, M, es) =>
          let vps := aieHullValuePrunes lo hi m M es dk i k
          let bps := aieHullBoundsPrunes di xs lo hi m M dk i k
          safePrunes dk
            (if xs.length ≤ 16 ∧ 0 < vps.length then vps else bps ++ vps)

/-- `aieHullBase` with the table array hoisted. -/
def aieHullBaseA (xa : Array Value) (di : DomC) :
    Option (Int × Int × Int × Int × List Int) :=
  di.lo?.bind fun lo =>
    di.hi?.bind fun hi =>
      if hi - lo + 1 ≤ 0 || 256 < hi - lo + 1 then none
      else
        let es := aieEntriesA xa lo hi
        es.min?.bind fun m =>
          es.max?.map fun M => (lo, hi, m, M, es)

theorem aieHullBaseA_eq (xs : List Int) (di : DomC) :
    aieHullBaseA (xs.map Value.int).toArray di = aieHullBase di xs := by
  unfold aieHullBaseA aieHullBase
  simp only [aieEntriesA_eq]

/-- `aieHullPrunes` with the table array hoisted. -/
def aieHullPrunesA (xa : Array Value) (xs : List Int) (di dk : DomC)
    (i k : Nat) : List (Literal × Clause) :=
  match dk.fixedValue with
  | some _ => []
  | none =>
      match aieHullBaseA xa di with
      | none => []
      | some (lo, hi, m, M, es) =>
          let vps := aieHullValuePrunes lo hi m M es dk i k
          let bps := aieHullBoundsPrunes di xs lo hi m M dk i k
          safePrunes dk
            (if xs.length ≤ 16 ∧ 0 < vps.length then vps else bps ++ vps)

theorem aieHullPrunesA_eq (xs : List Int) (di dk : DomC) (i k : Nat) :
    aieHullPrunesA (xs.map Value.int).toArray xs di dk i k =
      aieHullPrunes di dk xs i k := by
  unfold aieHullPrunesA aieHullPrunes
  simp only [aieHullBaseA_eq]

/-- The base computation exposes the hull endpoints, image bounds, and
entry list it used. -/
theorem aieHullBase_spec {di : DomC} {xs : List Int}
    {lo hi m M : Int} {es : List Int}
    (h : aieHullBase di xs = some (lo, hi, m, M, es)) :
    di.lo? = some lo ∧ di.hi? = some hi ∧ es = aieEntries xs lo hi ∧
      es.min? = some m ∧ es.max? = some M := by
  unfold aieHullBase at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨lo', hlo, h⟩ := h
  obtain ⟨hi', hhi, h⟩ := h
  split at h
  · simp at h
  · rename_i hwidth
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨m', hmin, h⟩ := h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨M', hmax, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨hlo, hhi, rfl, hmin, hmax⟩

/-- Membership decomposition of the hull batch. -/
theorem aieHullPrunes_mem {di dk : DomC} {xs : List Int} {i k : Nat}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aieHullPrunes di dk xs i k) :
    ∃ lo hi m M es, aieHullBase di xs = some (lo, hi, m, M, es) ∧
      ((l, reason) ∈ aieHullBoundsPrunes di xs lo hi m M dk i k ∨
       (l, reason) ∈ aieHullValuePrunes lo hi m M es dk i k) := by
  unfold aieHullPrunes at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i lo hi m M es hbase
      have h' := mem_safePrunes (d := dk)
        (ps := (let vps := aieHullValuePrunes lo hi m M es dk i k
                let bps := aieHullBoundsPrunes di xs lo hi m M dk i k
                if xs.length ≤ 16 ∧ 0 < vps.length then vps
                else bps ++ vps)) h
      dsimp only at h'
      split at h'
      · exact ⟨lo, hi, m, M, es, hbase, Or.inr h'⟩
      · rw [List.mem_append] at h'
        exact ⟨lo, hi, m, M, es, hbase, h'⟩

/-- Membership decomposition of the hull bounds batch, including the
unassigned-pivot side conditions. -/
theorem aieHullBoundsPrunes_mem {di : DomC} {xs : List Int} {lo hi m M : Int}
    {dk : DomC} {i k : Nat} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aieHullBoundsPrunes di xs lo hi m M dk i k) :
    (l = negLe k (m - 1) ∧ dk.evalLit (negLe k (m - 1)) = none ∧
        reason = [negLe k (m - 1), posLe i (lo - 1), negLe i hi]) ∨
      (l = posLe k M ∧ dk.evalLit (posLe k M) = none ∧
        reason = [posLe k M, posLe i (lo - 1), negLe i hi]) := by
  unfold aieHullBoundsPrunes at h
  split at h
  · simp at h
  · rcases List.mem_append.mp h with h | h
    · split at h
      · rename_i heval
        have hp := List.mem_singleton.mp h
        injection hp with hl hr
        exact Or.inl ⟨hl, heval, hr⟩
      · simp at h
    · split at h
      · rename_i heval
        have hp := List.mem_singleton.mp h
        injection hp with hl hr
        exact Or.inr ⟨hl, heval, hr⟩
      · simp at h

/-- Membership decomposition of one value candidate. -/
theorem aieHullValueCandidates_mem {lo hi m M : Int} {es : List Int}
    {dk : DomC} {i k : Nat} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aieHullValueCandidates lo hi m M es dk i k) :
    ∃ w : Int, w ∈ intCandidates dk ∧ ¬ w < m ∧ ¬ M < w ∧
      es.contains w = false ∧ dk.evalLit (posNe k w) = none ∧
      l = posNe k w ∧
      reason = [posNe k w, posLe i (lo - 1), negLe i hi] := by
  unfold aieHullValueCandidates at h
  rw [List.mem_filterMap] at h
  obtain ⟨w, hw, hf⟩ := h
  split at hf
  · simp at hf
  · rename_i hnotout
    split at hf
    · simp at hf
    · rename_i hnotcontains
      split at hf
      · rename_i heval
        have hp := Option.some.inj hf
        injection hp with hl hr
        have hnot : ¬ (w < m ∨ M < w) := by simpa using hnotout
        exact ⟨w, hw, fun hwm => hnot (Or.inl hwm),
          fun hMw => hnot (Or.inr hMw), by simpa using hnotcontains,
          heval, hl.symm, hr.symm⟩
      · simp at hf

/-- Membership decomposition of the guarded value batch. -/
theorem aieHullValuePrunes_mem {lo hi m M : Int} {es : List Int}
    {dk : DomC} {i k : Nat} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aieHullValuePrunes lo hi m M es dk i k) :
    ∃ w : Int, w ∈ intCandidates dk ∧ ¬ w < m ∧ ¬ M < w ∧
      es.contains w = false ∧ dk.evalLit (posNe k w) = none ∧
      l = posNe k w ∧
      reason = [posNe k w, posLe i (lo - 1), negLe i hi] := by
  unfold aieHullValuePrunes at h
  split at h
  · simp at h
  · exact aieHullValueCandidates_mem (mem_safePrunes (d := dk)
      (ps := aieHullValueCandidates lo hi m M es dk i k) h)

/-- The pure prune list of the constant-table propagator. -/
def aiePrunePairs (di dk : DomC) (xs : List Int) (i k : Nat) :
    List (Literal × Clause) :=
  match di.fixedValue with
  | some (.int idx) =>
      match valuesGet1 (xs.map Value.int) idx with
      | some (.int v) =>
          if dk.memIntView v then aieFixedPrunes dk i k idx v else []
      | _ => []
  | some _ => []
  | none => aieBadIndexPrunes di dk xs i k ++ aieHullPrunes di dk xs i k

/-! ### Wipeout conflicts for the constant-table element

When every in-range index value still present in the index domain has a
defined table entry outside the result domain, the element row is
unsatisfiable on the current view.  The conflict clause is the
disjunction of `k = T[j]` for the present index values `j` and `i = j`
for the removed in-range values: the element row satisfies it for every
accepted assignment, and every literal is false on the view. -/

/-- The length bound of the wipeout scan.  Longer tables keep the no-op
path: their conflict clauses are expensive to learn and are the ones
observed to trigger late, non-asserting conflicts. -/
def aieWipeoutMaxLen : Nat := 64

/-- The guard of a genuine wipeout: every in-range index value still in
the index domain has a defined table entry outside the result domain.
Values outside `[1, length]` cannot satisfy the element and need no
literal. -/
def aieWipeoutOK (di dk : DomC) (xs : List Int) : Bool :=
  decide (xs.length ≤ aieWipeoutMaxLen) &&
    (List.range xs.length).all fun t =>
      let j : Int := Int.ofNat t + 1
      if di.memIntView j then
        match valuesGet1 (xs.map Value.int) j with
        | some (.int w) => !dk.memIntView w
        | _ => false
      else true

/-- The wipeout conflict clause: for a present index value the result
must equal its table entry; for a removed index value the index itself
is excluded. -/
def aieWipeoutClause (di dk : DomC) (xs : List Int) (i k : Nat) :
    List Literal :=
  (List.range xs.length).map fun t =>
    let j : Int := Int.ofNat t + 1
    if di.memIntView j then
      match valuesGet1 (xs.map Value.int) j with
      | some (.int w) => negNe k w
      | _ => negNe i j
    else negNe i j

/-- A wipeout conflict when the guard holds; an empty clause is never
emitted, so `.fix` is the conservative fallback. -/
def aieWipeout (di dk : DomC) (xs : List Int) (i k : Nat) :
    Option (List Literal) :=
  if aieWipeoutOK di dk xs then
    let ls := aieWipeoutClause di dk xs i k
    if ls.isEmpty then none else some ls
  else none

/-- Bounds of a successful `valuesGet1` read: FlatZinc tables are
1-based, so the index lies in `[1, length]`. -/
theorem valuesGet1_some_bounds {xs : List Value} {i : Int} {v : Value}
    (h : valuesGet1 xs i = some v) :
    1 ≤ i ∧ i ≤ (xs.length : Int) := by
  unfold valuesGet1 at h
  split at h
  · rename_i hpos
    have hsome : xs[i.toNat - 1]? = some v := h
    have hlt : i.toNat - 1 < xs.length :=
      (List.getElem?_eq_some_iff.mp hsome).1
    have hitoNat : (i.toNat : Int) = i := Int.toNat_of_nonneg (by omega)
    omega
  · cases h

/-- Every in-range index value still present in `di` has a defined
entry that is absent from `dk`, when the wipeout guard holds. -/
theorem aieWipeoutOK_spec {di dk : DomC} {xs : List Int}
    (h : aieWipeoutOK di dk xs = true) :
    xs.length ≤ aieWipeoutMaxLen ∧
      ∀ j : Int, 1 ≤ j → j ≤ (xs.length : Int) →
        di.memIntView j = true →
        ∃ w : Int, valuesGet1 (xs.map Value.int) j = some (.int w) ∧
          dk.memIntView w = false := by
  unfold aieWipeoutOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨of_decide_eq_true hlen, ?_⟩
  intro j hj1 hjn hmem
  have htoNat : (j.toNat : Int) = j := Int.toNat_of_nonneg (by omega)
  have ht : j.toNat - 1 < xs.length := by omega
  have hj_eq : Int.ofNat (j.toNat - 1) + 1 = j := by
    change ((j.toNat - 1 : Nat) : Int) + 1 = j
    have hm : 1 ≤ j.toNat := by omega
    rw [Int.ofNat_sub hm]
    omega
  have htj := List.all_eq_true.mp hall (j.toNat - 1)
    (List.mem_range.mpr ht)
  dsimp only at htj
  rw [hj_eq, if_pos hmem] at htj
  split at htj
  · rename_i w hent
    exact ⟨w, hent, by simpa using htj⟩
  · simp at htj

/-- A wipeout option exposes its guard and its clause. -/
theorem aieWipeout_spec {di dk : DomC} {xs : List Int} {i k : Nat}
    {ls : List Literal} (h : aieWipeout di dk xs i k = some ls) :
    aieWipeoutOK di dk xs = true ∧
      ls = aieWipeoutClause di dk xs i k := by
  unfold aieWipeout at h
  by_cases hOK : aieWipeoutOK di dk xs = true
  · rw [if_pos hOK] at h
    by_cases hemp : (aieWipeoutClause di dk xs i k).isEmpty = true
    · rw [if_pos hemp] at h
      simp at h
    · rw [if_neg hemp] at h
      refine ⟨hOK, ?_⟩
      injection h with hls
      exact hls.symm
  · rw [if_neg hOK] at h
    simp at h

/-- A present index value contributes its result equality to the
wipeout clause. -/
theorem aieWipeoutClause_mem_of_mem {di dk : DomC} {xs : List Int}
    {i k : Nat} {j w : Int} (hj1 : 1 ≤ j) (hjn : j ≤ (xs.length : Int))
    (hmem : di.memIntView j = true)
    (hent : valuesGet1 (xs.map Value.int) j = some (.int w)) :
    negNe k w ∈ aieWipeoutClause di dk xs i k := by
  unfold aieWipeoutClause
  rw [List.mem_map]
  refine ⟨j.toNat - 1, List.mem_range.mpr (by
    have htoNat : (j.toNat : Int) = j := Int.toNat_of_nonneg (by omega)
    omega), ?_⟩
  have hj_eq : Int.ofNat (j.toNat - 1) + 1 = j := by
    change ((j.toNat - 1 : Nat) : Int) + 1 = j
    have hm : 1 ≤ j.toNat := by omega
    rw [Int.ofNat_sub hm]
    have htoNat : (j.toNat : Int) = j := Int.toNat_of_nonneg (by omega)
    omega
  simp only [hj_eq, hmem, hent, if_pos]

/-- A removed index value contributes its own exclusion to the wipeout
clause. -/
theorem aieWipeoutClause_mem_of_not_mem {di dk : DomC} {xs : List Int}
    {i k : Nat} {j : Int} (hj1 : 1 ≤ j) (hjn : j ≤ (xs.length : Int))
    (hmem : di.memIntView j = false) :
    negNe i j ∈ aieWipeoutClause di dk xs i k := by
  unfold aieWipeoutClause
  rw [List.mem_map]
  refine ⟨j.toNat - 1, List.mem_range.mpr (by
    have htoNat : (j.toNat : Int) = j := Int.toNat_of_nonneg (by omega)
    omega), ?_⟩
  have hj_eq : Int.ofNat (j.toNat - 1) + 1 = j := by
    change ((j.toNat - 1 : Nat) : Int) + 1 = j
    have hm : 1 ≤ j.toNat := by omega
    rw [Int.ofNat_sub hm]
    have htoNat : (j.toNat : Int) = j := Int.toNat_of_nonneg (by omega)
    omega
  simp only [hj_eq, hmem]
  simp

/-- The pure decision function. -/
def aieOut (di dk : DomC) (xs : List Int) (i k : Nat) : AieOut :=
  match intPairBounds di dk with
  | none => .fix
  | some _ =>
      match di.fixedValue with
      | some (.int idx) =>
          match valuesGet1 (xs.map Value.int) idx with
          | none => .conflict [posNe i idx]
          | some (.int v) =>
              if dk.memIntView v then
                let ps := aieFixedPrunes dk i k idx v
                if ps.isEmpty then .fix else .prune ps
              else .conflict [posNe i idx, negNe k v]
          | some _ => .fix
      | some _ => .fix
      | none =>
          if aieHasGood di dk xs then
            let ps := aieBadIndexPrunes di dk xs i k ++
              aieHullPrunes di dk xs i k
            if ps.isEmpty then .fix else .prune ps
          else
            match aieWipeout di dk xs i k with
            | some ls => .conflict ls
            | none => .fix

/-! ### Array-indexed runtime twins for the constant-table scan

`valuesGet1` walks the table from the front, so calling it once per
candidate index makes `aieOut` quadratic in the table width.  The twins
below hoist `xs.map Value.int` to an `Array` once per propagator run and
then use O(1) `Array` lookups.  They are installed only in compiled code
by `@[csimp]`; every proof keeps using the list-based definitions. -/

/-- `aieHasGood` with the hoisted table array. -/
def aieHasGoodA (xa : Array Value) (di dk : DomC) : Bool :=
  (intCandidates di).any fun v =>
    match valuesGet1A xa v with
    | some (.int w) => dk.memIntView w
    | _ => false

theorem aieHasGoodA_eq (xs : List Int) (di dk : DomC) :
    aieHasGoodA (xs.map Value.int).toArray di dk = aieHasGood di dk xs := by
  unfold aieHasGoodA aieHasGood
  congr 1
  funext v
  rw [valuesGet1A_toArray]

/-- `aieBadIndexPrunes` with the hoisted table array. -/
def aieBadIndexPrunesA (xa : Array Value) (di dk : DomC) (i k : Nat) :
    List (Literal × Clause) :=
  (intCandidates di).filterMap fun v =>
    match valuesGet1A xa v with
    | none =>
        if 1 < di.size then some (posNe i v, [posNe i v]) else none
    | some (.int w) =>
        if dk.memIntView w then none
        else if 1 < di.size then some (posNe i v, [posNe i v, negNe k w])
        else none
    | some _ => none

theorem aieBadIndexPrunesA_eq (xs : List Int) (di dk : DomC) (i k : Nat) :
    aieBadIndexPrunesA (xs.map Value.int).toArray di dk i k =
      aieBadIndexPrunes di dk xs i k := by
  unfold aieBadIndexPrunesA aieBadIndexPrunes
  congr 1
  funext v
  rw [valuesGet1A_toArray]

/-- `aieWipeoutOK` with the hoisted table array. -/
def aieWipeoutOKA (xa : Array Value) (xs : List Int) (di dk : DomC) : Bool :=
  decide (xs.length ≤ aieWipeoutMaxLen) &&
    (List.range xs.length).all fun t =>
      let j : Int := Int.ofNat t + 1
      if di.memIntView j then
        match valuesGet1A xa j with
        | some (.int w) => !dk.memIntView w
        | _ => false
      else true

theorem aieWipeoutOKA_eq (xs : List Int) (di dk : DomC) :
    aieWipeoutOKA (xs.map Value.int).toArray xs di dk =
      aieWipeoutOK di dk xs := by
  unfold aieWipeoutOKA aieWipeoutOK
  simp only [valuesGet1A_toArray]

/-- `aieWipeoutClause` with the hoisted table array. -/
def aieWipeoutClauseA (xa : Array Value) (xs : List Int) (di dk : DomC)
    (i k : Nat) : List Literal :=
  (List.range xs.length).map fun t =>
    let j : Int := Int.ofNat t + 1
    if di.memIntView j then
      match valuesGet1A xa j with
      | some (.int w) => negNe k w
      | _ => negNe i j
    else negNe i j

theorem aieWipeoutClauseA_eq (xs : List Int) (di dk : DomC) (i k : Nat) :
    aieWipeoutClauseA (xs.map Value.int).toArray xs di dk i k =
      aieWipeoutClause di dk xs i k := by
  unfold aieWipeoutClauseA aieWipeoutClause
  simp only [valuesGet1A_toArray]

/-- `aieWipeout` with the hoisted table array. -/
def aieWipeoutA (xa : Array Value) (xs : List Int) (di dk : DomC)
    (i k : Nat) : Option (List Literal) :=
  if aieWipeoutOKA xa xs di dk then
    let ls := aieWipeoutClauseA xa xs di dk i k
    if ls.isEmpty then none else some ls
  else none

theorem aieWipeoutA_eq (xs : List Int) (di dk : DomC) (i k : Nat) :
    aieWipeoutA (xs.map Value.int).toArray xs di dk i k =
      aieWipeout di dk xs i k := by
  unfold aieWipeoutA aieWipeout
  simp only [aieWipeoutOKA_eq, aieWipeoutClauseA_eq]

/-- `aieOut` with the hoisted table array. -/
def aieOutA (xa : Array Value) (xs : List Int) (di dk : DomC) (i k : Nat) : AieOut :=
  match intPairBounds di dk with
  | none => .fix
  | some _ =>
      match di.fixedValue with
      | some (.int idx) =>
          match valuesGet1A xa idx with
          | none => .conflict [posNe i idx]
          | some (.int v) =>
              if dk.memIntView v then
                let ps := aieFixedPrunes dk i k idx v
                if ps.isEmpty then .fix else .prune ps
              else .conflict [posNe i idx, negNe k v]
          | some _ => .fix
      | some _ => .fix
      | none =>
          if aieHasGoodA xa di dk then
            let ps := aieBadIndexPrunesA xa di dk i k ++
              aieHullPrunesA xa xs di dk i k
            if ps.isEmpty then .fix else .prune ps
          else
            match aieWipeoutA xa xs di dk i k with
            | some ls => .conflict ls
            | none => .fix

theorem aieOutA_eq (xs : List Int) (di dk : DomC) (i k : Nat) :
    aieOutA (xs.map Value.int).toArray xs di dk i k = aieOut di dk xs i k := by
  unfold aieOutA aieOut
  simp only [aieHasGoodA_eq, aieBadIndexPrunesA_eq, aieHullPrunesA_eq,
    aieWipeoutA_eq, valuesGet1A_toArray]

/-- Runtime twin of `aieOut` used by compiled code only. -/
def aieOutFast (di dk : DomC) (xs : List Int) (i k : Nat) : AieOut :=
  aieOutA (xs.map Value.int).toArray xs di dk i k

@[csimp] theorem aieOut_eq_fast : @aieOut = @aieOutFast := by
  funext di dk xs i k
  exact (aieOutA_eq xs di dk i k).symm

/-! ### Entailment of the stage-1 clauses -/

/-- A satisfied constant-table constraint reads an integer index, an
integer result, and a defined table entry. -/
theorem aie_satisfied_views {b : Assignment} {xs : List Int} {i k : Nat}
    (h : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b) :
    ∃ idx e : Int, b[i]? = some (.int idx) ∧ b[k]? = some (.int e) ∧
      valuesGet1 (xs.map Value.int) idx = some (.int e) :=
  arrayIntElement_views h

/-- The wipeout clause is entailed by the element row alone.  An
accepted assignment reads an index in `[1, length]`; if that index is
still present in `di` the clause contains its result equality, and if
it was removed the clause contains its index exclusion. -/
theorem aie_entailed_wipeout (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {di dk : DomC}
    (hOK : aieWipeoutOK di dk xs = true) :
    Entailed p (aieWipeoutClause di dk xs i k) := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx, e, hi, hk, hent⟩ := aie_satisfied_views hs
  obtain ⟨hidx1, hidxn⟩ := valuesGet1_some_bounds hent
  have hidxn' : idx ≤ (xs.length : Int) := by simpa using hidxn
  by_cases hmemd : di.memIntView idx = true
  · obtain ⟨w, hw, -⟩ :=
      (aieWipeoutOK_spec hOK).2 idx hidx1 hidxn' hmemd
    have hwe : w = e := by
      have hsome : some (Value.int w) = some (Value.int e) := by
        rw [← hw, hent]
      exact Value.int.inj (Option.some.inj hsome)
    refine ⟨negNe k w,
      aieWipeoutClause_mem_of_mem hidx1 hidxn' hmemd hw, ?_⟩
    rw [eval_negNe_iff]
    exact ⟨e, slotInt_of_int_read hk, hwe.symm⟩
  · have hnot : di.memIntView idx = false := by simpa using hmemd
    refine ⟨negNe i idx,
      aieWipeoutClause_mem_of_not_mem hidx1 hidxn' hnot, ?_⟩
    rw [eval_negNe_iff]
    exact ⟨idx, slotInt_of_int_read hi, rfl⟩

/-- The out-of-range unit clause is entailed. -/
theorem aie_entailed_out (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {idx : Int} (hnone : valuesGet1 (xs.map Value.int) idx = none) :
    Entailed p [posNe i idx] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact aieResOut_entailed hs hnone

/-- The no-support clause `[i ≠ idx, k ≠ w]` is entailed. -/
theorem aie_entailed_noSupp (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {idx w : Int}
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int w)) :
    Entailed p [posNe i idx, negNe k w] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact aieResNoSupp_entailed hs hent

/-- The fixed-index upper-bound clause `[k ≤ v, i ≠ idx]` is entailed. -/
theorem aie_entailed_posLe (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {idx v : Int}
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v)) :
    Entailed p [posLe k v, posNe i idx] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views hs
  by_cases hidx : idx' = idx
  · subst hidx
    rw [hent] at hent'
    have hve : e = v := (Value.int.inj (Option.some.inj hent')).symm
    refine ⟨posLe k v, by simp, ?_⟩
    have hk' : slotInt b k = some v := by
      rw [slotInt_of_int_read hk, hve]
    exact avie_posLe_eval_true hk' (Int.le_refl v)
  · exact ⟨posNe i idx, by simp,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidx⟩

/-- The fixed-index lower-bound clause `[k > v - 1, i ≠ idx]` is
entailed. -/
theorem aie_entailed_negLe (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {idx v : Int}
    (hent : valuesGet1 (xs.map Value.int) idx = some (.int v)) :
    Entailed p [negLe k (v - 1), posNe i idx] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx', e, hi, hk, hent'⟩ := arrayIntElement_views hs
  by_cases hidx : idx' = idx
  · subst hidx
    rw [hent] at hent'
    have hve : e = v := (Value.int.inj (Option.some.inj hent')).symm
    refine ⟨negLe k (v - 1), by simp, ?_⟩
    have hk' : slotInt b k = some v := by
      rw [slotInt_of_int_read hk, hve]
    exact avie_negLe_eval_true hk' (by omega)
  · exact ⟨posNe i idx, by simp,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidx⟩

/-- The hull upper-bound clause `[k ≤ M, i ≤ lo - 1, i > hi]` is
entailed: an index in the hull has a table entry at most `M`, and an
index outside the hull satisfies one of the escape literals. -/
theorem aie_entailed_hull_posLe (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {lo hi M : Int}
    (hmax : (aieEntries xs lo hi).max? = some M) :
    Entailed p [posLe k M, posLe i (lo - 1), negLe i hi] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx, e, hi_read, hk, hent⟩ := aie_satisfied_views hs
  by_cases hlow : idx ≤ lo - 1
  · exact ⟨posLe i (lo - 1), by simp,
      avie_posLe_eval_true (slotInt_of_int_read hi_read) hlow⟩
  · by_cases hhigh : hi < idx
    · exact ⟨negLe i hi, by simp,
        avie_negLe_eval_true (slotInt_of_int_read hi_read) hhigh⟩
    · have hge : lo ≤ idx := by omega
      have hle : idx ≤ hi := by omega
      have hmemE : e ∈ aieEntries xs lo hi := mem_aieEntries hge hle hent
      have hMe : e ≤ M := aieEntries_le_max hmax hmemE
      exact ⟨posLe k M, by simp,
        avie_posLe_eval_true (slotInt_of_int_read hk) hMe⟩

/-- The hull lower-bound clause `[k > m - 1, i ≤ lo - 1, i > hi]` is
entailed. -/
theorem aie_entailed_hull_negLe (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {lo hi m : Int}
    (hmin : (aieEntries xs lo hi).min? = some m) :
    Entailed p [negLe k (m - 1), posLe i (lo - 1), negLe i hi] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx, e, hi_read, hk, hent⟩ := aie_satisfied_views hs
  by_cases hlow : idx ≤ lo - 1
  · exact ⟨posLe i (lo - 1), by simp,
      avie_posLe_eval_true (slotInt_of_int_read hi_read) hlow⟩
  · by_cases hhigh : hi < idx
    · exact ⟨negLe i hi, by simp,
        avie_negLe_eval_true (slotInt_of_int_read hi_read) hhigh⟩
    · have hge : lo ≤ idx := by omega
      have hle : idx ≤ hi := by omega
      have hmemE : e ∈ aieEntries xs lo hi := mem_aieEntries hge hle hent
      have hme : m ≤ e := aieEntries_min_le hmin hmemE
      exact ⟨negLe k (m - 1), by simp,
        avie_negLe_eval_true (slotInt_of_int_read hk) (by omega)⟩

/-- The hull unsupported-value clause `[k ≠ w, i ≤ lo - 1, i > hi]` is
entailed when `w` is absent from the hull image. -/
theorem aie_entailed_hull_ne (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    {lo hi w : Int}
    (hnot : w ∉ aieEntries xs lo hi) :
    Entailed p [posNe k w, posLe i (lo - 1), negLe i hi] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayIntElementSlot xs i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  obtain ⟨idx, e, hi_read, hk, hent⟩ := aie_satisfied_views hs
  by_cases hlow : idx ≤ lo - 1
  · exact ⟨posLe i (lo - 1), by simp,
      avie_posLe_eval_true (slotInt_of_int_read hi_read) hlow⟩
  · by_cases hhigh : hi < idx
    · exact ⟨negLe i hi, by simp,
        avie_negLe_eval_true (slotInt_of_int_read hi_read) hhigh⟩
    · have hge : lo ≤ idx := by omega
      have hle : idx ≤ hi := by omega
      have hmemE : e ∈ aieEntries xs lo hi := mem_aieEntries hge hle hent
      have hew : e ≠ w := by
        intro heq
        exact hnot (heq ▸ hmemE)
      exact ⟨posNe k w, by simp,
        aie_posNe_eval_true (slotInt_of_int_read hk) hew⟩

theorem aiePrunePairs_entailed (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (di dk : DomC)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aiePrunePairs di dk xs i k) : Entailed p reason := by
  unfold aiePrunePairs at h
  split at h
  · rename_i idx hfix
    split at h
    · rename_i v hent
      split at h
      · rename_i hmemv
        unfold aieFixedPrunes at h
        rcases List.mem_append.mp h with h1 | h2
        · split at h1
          · rename_i heval
            have hpair := List.mem_singleton.mp h1
            injection hpair with hl hr
            subst hl
            subst hr
            exact aie_entailed_posLe p xs i k hmem hent
          · simp at h1
        · split at h2
          · rename_i heval
            have hpair := List.mem_singleton.mp h2
            injection hpair with hl hr
            subst hl
            subst hr
            exact aie_entailed_negLe p xs i k hmem hent
          · simp at h2
      · simp at h
    · simp at h
  · simp at h
  · rename_i hfix
    rw [List.mem_append] at h
    rcases h with h | h
    · unfold aieBadIndexPrunes at h
      rw [List.mem_filterMap] at h
      obtain ⟨v, hv, hf⟩ := h
      have hmemv := mem_intCandidates hv
      split at hf
      · rename_i hnone
        split at hf
        · rename_i hsize
          have hpair := Option.some.inj hf
          injection hpair with hl hr
          subst hl
          subst hr
          exact aie_entailed_out p xs i k hmem hnone
        · simp at hf
      · rename_i w hent
        split at hf
        · rename_i hgood
          simp at hf
        · split at hf
          · rename_i hsize
            have hpair := Option.some.inj hf
            injection hpair with hl hr
            subst hl
            subst hr
            exact aie_entailed_noSupp p xs i k hmem hent
          · simp at hf
      · simp at hf
    · rcases aieHullPrunes_mem h with ⟨lo, hi, m, M, es, hbase, hp⟩
      obtain ⟨hlo, hhi, hes, hmin, hmax⟩ := aieHullBase_spec hbase
      subst es
      rcases hp with hb | hv
      · rcases aieHullBoundsPrunes_mem (di := di) (xs := xs) hb with ⟨hl, heval, hr⟩ |
          ⟨hl, heval, hr⟩
        · subst hl
          subst hr
          exact aie_entailed_hull_negLe p xs i k hmem hmin
        · subst hl
          subst hr
          exact aie_entailed_hull_posLe p xs i k hmem hmax
      · rcases aieHullValuePrunes_mem hv with
          ⟨w, hwmem, hltlo, hlthi, hnot, heval, hl, hr⟩
        subst hl
        subst hr
        exact aie_entailed_hull_ne p xs i k hmem (by
          intro hmemE
          have hcontains : (aieEntries xs lo hi).contains w = true :=
            List.contains_iff_mem.mpr hmemE
          rw [hnot] at hcontains
          cases hcontains)

theorem aiePrunePairs_eval (p : CompiledProblem DomConstraint)
    (xs : List Int) (i k : Nat) (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView) (hWF : ViewWF view #[i, k])
    (di dk : DomC)
    (hdi : view.doms.getD i DomC.empty = di)
    (hdk : view.doms.getD k DomC.empty = dk)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aiePrunePairs di dk xs i k) :
    (view.doms.getD l.atom.slot DomC.empty).evalLit l = none ∧
      ∀ q ∈ reason, q ≠ l →
        (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  unfold aiePrunePairs at h
  split at h
  · rename_i idx hfix
    split at h
    · rename_i v hent
      split at h
      · rename_i hmemv
        unfold aieFixedPrunes at h
        have hWFi : di.WF := by
          have := hWF.dom_wf (s := i) (by simp)
          simpa [hdi] using this
        have hmemd : di.mem (.int idx) = true :=
          (DomC.fixedValue_sound di hWFi hfix).1
        have hipos : di.evalLit (posNe i idx) = some false :=
          DomC.evalLit_posNe_of_fixed hfix hmemd
        rcases List.mem_append.mp h with h1 | h2
        · split at h1
          · rename_i heval
            have hpair := List.mem_singleton.mp h1
            injection hpair with hl hr
            subst hl
            subst hr
            refine ⟨?_, ?_⟩
            · simpa [hdk, posLe, Atom.slot] using heval
            · intro q hq hne
              rw [List.mem_cons] at hq
              rcases hq with hq | hq
              · exact absurd hq hne
              · rw [List.mem_singleton] at hq
                subst hq
                simpa [hdi, posNe, Atom.slot] using hipos
          · simp at h1
        · split at h2
          · rename_i heval
            have hpair := List.mem_singleton.mp h2
            injection hpair with hl hr
            subst hl
            subst hr
            refine ⟨?_, ?_⟩
            · simpa [hdk, negLe, Atom.slot] using heval
            · intro q hq hne
              rw [List.mem_cons] at hq
              rcases hq with hq | hq
              · exact absurd hq hne
              · rw [List.mem_singleton] at hq
                subst hq
                simpa [hdi, posNe, Atom.slot] using hipos
          · simp at h2
      · simp at h
    · simp at h
  · simp at h
  · rename_i hfix
    rw [List.mem_append] at h
    rcases h with h | h
    · unfold aieBadIndexPrunes at h
      rw [List.mem_filterMap] at h
      obtain ⟨v, hv, hf⟩ := h
      have hmemv : di.mem (.int v) = true := mem_intCandidates hv
      have hnone : di.evalLit (posNe i v) = none := by
        have := DomC.evalLit_neLit_none_of_not_fixed (d := di) (s := i) (v := .int v)
          hfix hmemv
        simpa [neLit] using this
      split at hf
      · rename_i hentry
        split at hf
        · rename_i hsize
          have hpair := Option.some.inj hf
          injection hpair with hl hr
          subst hl
          subst hr
          refine ⟨?_, ?_⟩
          · simpa [hdi, posNe, Atom.slot] using hnone
          · intro q hq hne
            rw [List.mem_cons] at hq
            rcases hq with hq | hq
            · exact absurd hq hne
            · simp at hq
        · simp at hf
      · rename_i w hentry
        split at hf
        · rename_i hgood
          simp at hf
        · rename_i hbad
          split at hf
          · rename_i hsize
            have hpair := Option.some.inj hf
            injection hpair with hl hr
            subst hl
            subst hr
            have hkfalse : dk.evalLit (negNe k w) = some false :=
              DomC.evalLit_negNe_false_of_not_memIntView dk k (by simpa using hbad)
            refine ⟨?_, ?_⟩
            · simpa [hdi, posNe, Atom.slot] using hnone
            · intro q hq hne
              rw [List.mem_cons] at hq
              rcases hq with hq | hq
              · exact absurd hq hne
              · rw [List.mem_singleton] at hq
                subst hq
                simpa [hdk, negNe, Atom.slot] using hkfalse
          · simp at hf
      · simp at hf
    · have hWFi : di.WF := by
        have := hWF.dom_wf (s := i) (by simp)
        simpa [hdi] using this
      rcases aieHullPrunes_mem h with ⟨lo, hi, m, M, es, hbase, hp⟩
      obtain ⟨hlo, hhi, hes, hmin, hmax⟩ := aieHullBase_spec hbase
      have hle : lo ≤ hi := DomC.lo?_le_hi? di hWFi hlo hhi
      subst es
      rcases hp with hb | hv
      · rcases aieHullBoundsPrunes_mem (di := di) (xs := xs) hb with ⟨hl, heval, hr⟩ |
          ⟨hl, heval, hr⟩
        · subst hl
          subst hr
          refine ⟨?_, ?_⟩
          · simpa [hdk, negLe, Atom.slot] using heval
          · intro q hq hne
            rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · exact absurd rfl hne
            · simpa [hdi, posLe, Atom.slot] using
                evalLit_posLe_false_of_lo_gt hlo hhi (by omega) (by omega)
            · simpa [hdi, negLe, Atom.slot] using
                evalLit_negLe_false_of_hi_le hlo hhi (by omega) (by omega)
        · subst hl
          subst hr
          refine ⟨?_, ?_⟩
          · simpa [hdk, posLe, Atom.slot] using heval
          · intro q hq hne
            rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · exact absurd rfl hne
            · simpa [hdi, posLe, Atom.slot] using
                evalLit_posLe_false_of_lo_gt hlo hhi (by omega) (by omega)
            · simpa [hdi, negLe, Atom.slot] using
                evalLit_negLe_false_of_hi_le hlo hhi (by omega) (by omega)
      · rcases aieHullValuePrunes_mem hv with
          ⟨w, hwmem, hltlo, hlthi, hnot, heval, hl, hr⟩
        subst hl
        subst hr
        refine ⟨?_, ?_⟩
        · simpa [hdk, posNe, Atom.slot] using heval
        · intro q hq hne
          rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · exact absurd rfl hne
          · simpa [hdi, posLe, Atom.slot] using
              evalLit_posLe_false_of_lo_gt hlo hhi (by omega) (by omega)
          · simpa [hdi, negLe, Atom.slot] using
              evalLit_negLe_false_of_hi_le hlo hhi (by omega) (by omega)

/-! ### The stage-1 decision analysis -/

theorem aieOut_conflict_cases {di dk : DomC} {xs : List Int} {i k : Nat}
    {ls : List Literal} (h : aieOut di dk xs i k = .conflict ls) :
    (∃ idx : Int, di.fixedValue = some (.int idx) ∧
        valuesGet1 (xs.map Value.int) idx = none ∧ ls = [posNe i idx]) ∨
    (∃ idx v : Int, di.fixedValue = some (.int idx) ∧
        valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
        dk.memIntView v = false ∧ ls = [posNe i idx, negNe k v]) ∨
    (aieWipeout di dk xs i k = some ls) := by
  unfold aieOut at h
  split at h
  · cases h
  · rename_i bounds
    split at h
    · rename_i idx hfix
      split at h
      · rename_i hnone
        exact Or.inl ⟨idx, hfix, hnone, by injection h with hls; exact hls.symm⟩
      · rename_i v hent
        by_cases hgood : dk.memIntView v = true
        · by_cases hemp : (aieFixedPrunes dk i k idx v).isEmpty = true
          · simp [hfix, hent, hgood, hemp] at h
          · simp [hfix, hent, hgood, hemp] at h
        · have hls : ls = [posNe i idx, negNe k v] := by
            have hh := h
            rw [if_neg hgood] at hh
            injection hh with h
            exact h.symm
          exact Or.inr (Or.inl ⟨idx, v, hfix, hent,
            by simpa using hgood, hls⟩)
      · cases h
    · cases h
    · rename_i hfix
      by_cases hgood : aieHasGood di dk xs = true
      · by_cases hemp : (aieBadIndexPrunes di dk xs i k ++
            aieHullPrunes di dk xs i k).isEmpty = true
        · simp [hfix, hgood, hemp] at h
        · simp [hfix, hgood, hemp] at h
      · cases hw : aieWipeout di dk xs i k with
        | none => simp [hfix, hgood, hw] at h
        | some ls0 =>
            have hls : ls0 = ls := by
              simpa [hfix, hgood, hw] using h
            exact Or.inr (Or.inr (by simpa [hls] using hw))

theorem aieOut_prune_cases {di dk : DomC} {xs : List Int} {i k : Nat}
    {pairs : List (Literal × Clause)}
    (h : aieOut di dk xs i k = .prune pairs) :
    pairs = aiePrunePairs di dk xs i k ∧
      ((∃ idx v : Int, di.fixedValue = some (.int idx) ∧
          valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
          dk.memIntView v = true) ∨
       (di.fixedValue = none ∧ aieHasGood di dk xs = true)) := by
  unfold aieOut at h
  split at h
  · cases h
  · rename_i bounds
    split at h
    · rename_i idx hfix
      split at h
      · cases h
      · rename_i v hent
        by_cases hgood : dk.memIntView v = true
        · by_cases hemp : (aieFixedPrunes dk i k idx v).isEmpty = true
          · simp [hfix, hent, hgood, hemp] at h
          · have hraw : aieFixedPrunes dk i k idx v = pairs := by
              simpa [hfix, hent, hgood, hemp] using h
            have hpairs : pairs = aieFixedPrunes dk i k idx v := hraw.symm
            refine ⟨?_, Or.inl ⟨idx, v, hfix, hent, hgood⟩⟩
            rw [hpairs]
            unfold aiePrunePairs
            rw [hfix]
            dsimp only
            rw [hent]
            dsimp only
            rw [if_pos hgood]
        · simp [hfix, hent, hgood] at h
      · cases h
    · cases h
    · rename_i hfix
      by_cases hgood : aieHasGood di dk xs = true
      · by_cases hemp : (aieBadIndexPrunes di dk xs i k ++
            aieHullPrunes di dk xs i k).isEmpty = true
        · simp [hfix, hgood, hemp] at h
        · have hraw : aieBadIndexPrunes di dk xs i k ++
              aieHullPrunes di dk xs i k = pairs := by
            simpa [hfix, hgood, hemp] using h
          have hpairs : pairs = aieBadIndexPrunes di dk xs i k ++
              aieHullPrunes di dk xs i k := hraw.symm
          refine ⟨?_, Or.inr ⟨hfix, hgood⟩⟩
          rw [hpairs]
          unfold aiePrunePairs
          rw [hfix]
      · cases hw : aieWipeout di dk xs i k with
        | none => simp [hfix, hgood, hw] at h
        | some ls0 => simp [hfix, hgood, hw] at h

/-! ### The stage-1 builder -/

/-- The constant-table element propagator. -/
def arrayIntElementPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints) : PropV2 p T :=
  let xa := (xs.map Value.int).toArray
  { vars := (dcSlotsFull (.arrayIntElementSlot xs i k)).toArray
    events := #[(i, .bounds), (k, .bounds), (i, .fix), (k, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dk := view.doms.getD k DomC.empty
      match hout : aieOutA xa xs di dk i k with
      | .fix => .fix
      | .conflict ls =>
          .conflict (EClause.ofLiterals p T ls (by
            have hout' : aieOut di dk xs i k = .conflict ls := by
              rw [← aieOutA_eq]
              exact hout
            rcases aieOut_conflict_cases hout' with
              ⟨idx, hfix, hnone, rfl⟩ | ⟨idx, v, hfix, hent, hbad, rfl⟩ | hw
            · exact aie_entailed_out p xs i k hmem hnone
            · exact aie_entailed_noSupp p xs i k hmem hent
            · obtain ⟨hOK, hls⟩ := aieWipeout_spec hw
              rw [hls]
              exact aie_entailed_wipeout p xs i k hmem hOK))
      | .prune pairs =>
          .prune (mkElemPruneArray p T pairs
            (fun l reason hlr =>
              aiePrunePairs_entailed p xs i k hmem di dk (by
                have hout' : aieOut di dk xs i k = .prune pairs := by
                  rw [← aieOutA_eq]
                  exact hout
                have hp := (aieOut_prune_cases hout').1
                rwa [hp] at hlr))) }

theorem arrayIntElementPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .conflict ec) :
    (∃ idx : Int,
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        valuesGet1 (xs.map Value.int) idx = none ∧
        T.decodeClause ec.lits = [posNe i idx]) ∨
    (∃ idx v : Int,
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
        (view.doms.getD k DomC.empty).memIntView v = false ∧
        T.decodeClause ec.lits = [posNe i idx, negNe k v]) ∨
    (∃ ls : List Literal,
        aieWipeout (view.doms.getD i DomC.empty)
          (view.doms.getD k DomC.empty) xs i k = some ls ∧
        T.decodeClause ec.lits = ls) := by
  dsimp only [arrayIntElementPropWith] at h
  split at h
  · cases h
  · rename_i ls hout
    injection h with hec
    subst hec
    have hout' : aieOut (view.doms.getD i DomC.empty)
        (view.doms.getD k DomC.empty) xs i k = .conflict ls := by
      rw [← aieOutA_eq]
      exact hout
    rcases aieOut_conflict_cases hout' with
      ⟨idx, hfix, hnone, rfl⟩ | ⟨idx, v, hfix, hent, hbad, rfl⟩ | hw
    · exact Or.inl ⟨idx, hfix, hnone, LitTable.decodeClause_map_pLit T _⟩
    · exact Or.inr (Or.inl ⟨idx, v, hfix, hent, hbad,
        LitTable.decodeClause_map_pLit T _⟩)
    · exact Or.inr (Or.inr ⟨ls, hw, LitTable.decodeClause_map_pLit T _⟩)
  · cases h

theorem arrayIntElementPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .prune ps) :
    ∃ (pairs : List (Literal × Clause)),
      pairs = aiePrunePairs (view.doms.getD i DomC.empty)
        (view.doms.getD k DomC.empty) xs i k ∧
      ((∃ idx v : Int,
          (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
          valuesGet1 (xs.map Value.int) idx = some (.int v) ∧
          (view.doms.getD k DomC.empty).memIntView v = true) ∨
       ((view.doms.getD i DomC.empty).fixedValue = none ∧
          aieHasGood (view.doms.getD i DomC.empty)
            (view.doms.getD k DomC.empty) xs = true)) ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        (l, reason) ∈ pairs ∧ q.1.lit = l ∧ T.decodeClause q.2.lits = reason) := by
  dsimp only [arrayIntElementPropWith] at h
  split at h
  · cases h
  · cases h
  · rename_i pairs hout
    injection h with hps
    subst hps
    have hout' : aieOut (view.doms.getD i DomC.empty)
        (view.doms.getD k DomC.empty) xs i k = .prune pairs := by
      rw [← aieOutA_eq]
      exact hout
    obtain ⟨hpairs, hsource⟩ := aieOut_prune_cases hout'
    exact ⟨pairs, hpairs, hsource,
      fun q hq => mkElemPruneArray_mem p T pairs _ hq⟩

theorem arrayIntElementPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  rcases arrayIntElementPropWith_run_conflict p T xs i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ | ⟨idx, v, hfix, hent, hbad, hdec⟩ |
      ⟨ls, hw, hdec⟩
  · rw [hdec]
    exact aie_entailed_out p xs i k hmem hnone
  · rw [hdec]
    exact aie_entailed_noSupp p xs i k hmem hent
  · rw [hdec]
    obtain ⟨hOK, hls⟩ := aieWipeout_spec hw
    rw [hls]
    exact aie_entailed_wipeout p xs i k hmem hOK

theorem arrayIntElementPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (.arrayIntElementSlot xs i k)).toArray)
    {ec : EClause p T}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD l.atom.slot DomC.empty).evalLit l = some false := by
  have hWF' : ViewWF view #[i, k] := by simpa [dcSlotsFull] using hWF
  rcases arrayIntElementPropWith_run_conflict p T xs i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ | ⟨idx, v, hfix, hent, hbad, hdec⟩ |
      ⟨ls, hw, hdec⟩
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_singleton] at hl
    subst l
    have hWFi : (view.doms.getD i DomC.empty).WF :=
      hWF'.dom_wf (s := i) (by simp)
    have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
      (DomC.fixedValue_sound _ hWFi hfix).1
    exact DomC.evalLit_posNe_of_fixed hfix hmem
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_cons, List.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have hWFi : (view.doms.getD i DomC.empty).WF :=
        hWF'.dom_wf (s := i) (by simp)
      have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
        (DomC.fixedValue_sound _ hWFi hfix).1
      exact DomC.evalLit_posNe_of_fixed hfix hmem
    · exact DomC.evalLit_negNe_false_of_not_memIntView _ k hbad
  · intro l hl
    rw [hdec] at hl
    obtain ⟨hOK, hls⟩ := aieWipeout_spec hw
    rw [hls] at hl
    unfold aieWipeoutClause at hl
    rw [List.mem_map] at hl
    obtain ⟨t, ht, rfl⟩ := hl
    have ht' : t < xs.length := List.mem_range.mp ht
    have hj1 : 1 ≤ (Int.ofNat t + 1 : Int) := by
      change (1 : Int) ≤ (t : Int) + 1
      omega
    have hjn : (Int.ofNat t + 1 : Int) ≤ (xs.length : Int) := by
      change (t : Int) + 1 ≤ (xs.length : Int)
      have htI : (t : Int) < (xs.length : Int) := by exact_mod_cast ht'
      omega
    by_cases hmem : (view.doms.getD i DomC.empty).memIntView
        (Int.ofNat t + 1) = true
    · obtain ⟨w, hent, hbad⟩ :=
        (aieWipeoutOK_spec hOK).2 (Int.ofNat t + 1) hj1 hjn hmem
      simp only [hmem, if_true]
      rw [hent]
      exact DomC.evalLit_negNe_false_of_not_memIntView
        (view.doms.getD k DomC.empty) k hbad
    · have hnot : (view.doms.getD i DomC.empty).memIntView
          (Int.ofNat t + 1) = false := by simpa using hmem
      simp only [hnot, Bool.false_eq_true, if_false]
      exact DomC.evalLit_negNe_false_of_not_memIntView
        (view.doms.getD i DomC.empty) i hnot

theorem arrayIntElementPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayIntElementPropWith_run_prune p T xs i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hdec]
  rw [hpairs] at hlr
  exact aiePrunePairs_entailed p xs i k hmem _ _ hlr

theorem arrayIntElementPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (.arrayIntElementSlot xs i k)).toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayIntElementPropWith p T xs i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  have hWF' : ViewWF view #[i, k] := by simpa [dcSlotsFull] using hWF
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayIntElementPropWith_run_prune p T xs i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hpairs] at hlr
  have hsound := aiePrunePairs_eval p xs i k hmem view hWF'
    (view.doms.getD i DomC.empty) (view.doms.getD k DomC.empty) rfl rfl hlr
  refine ⟨?_, ?_⟩
  · rw [hlit]
    exact hsound.1
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hsound.2 q' hq' (by rwa [hlit] at hne)

/-- Malformed index/result bounds: the stage-1 propagator is a no-op. -/
theorem arrayIntElementPropWith_run_fix_of_bounds (p : CompiledProblem DomConstraint)
    (T : LitTable) (xs : List Int) (i k : Nat)
    (hmem : DomConstraint.arrayIntElementSlot xs i k ∈ p.constraints)
    (view : EngineView)
    (hb : intPairBounds (view.doms.getD i DomC.empty)
      (view.doms.getD k DomC.empty) = none) :
    (arrayIntElementPropWith p T xs i k hmem).run view = .fix := by
  have ha : aieOut (view.doms.getD i DomC.empty)
      (view.doms.getD k DomC.empty) xs i k = .fix := by
    unfold aieOut
    rw [hb]
  dsimp only [arrayIntElementPropWith]
  split
  · rfl
  · rename_i ls hout
    have hout' : aieOut (view.doms.getD i DomC.empty)
        (view.doms.getD k DomC.empty) xs i k = .conflict ls := by
      rw [← aieOutA_eq]
      exact hout
    exact absurd hout' (by rw [ha]; simp)
  · rename_i pairs hout
    have hout' : aieOut (view.doms.getD i DomC.empty)
        (view.doms.getD k DomC.empty) xs i k = .prune pairs := by
      rw [← aieOutA_eq]
      exact hout
    exact absurd hout' (by rw [ha]; simp)

/-! ## Stage 2: the variable-table integer element -/

/-- Integer hull bounds of a compact domain, when nonempty. -/
def intBounds (d : DomC) : Option (Int × Int) :=
  match d.lo?, d.hi? with
  | some lo, some hi => some (lo, hi)
  | _, _ => none

theorem intBounds_some_iff {d : DomC} {lo hi : Int} :
    intBounds d = some (lo, hi) ↔ d.lo? = some lo ∧ d.hi? = some hi := by
  unfold intBounds
  constructor
  · intro h
    split at h
    · rename_i lo' hi' hlo hhi
      have h' : (lo', hi') = (lo, hi) := Option.some.inj h
      rw [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨hlo, hhi⟩
    · cases h
  · rintro ⟨hlo, hhi⟩
    simp [hlo, hhi]

/-- An integer table slot is usable when it is not represented as a
Boolean domain and its hull is nonempty. -/
def intSlotOkB (d : DomC) : Bool :=
  match d with
  | .bool _ => false
  | _ => (intBounds d).isSome

/-- Every table slot is a usable integer slot. -/
def avieTableOkB (doms : Array DomC) (is : List Nat) : Bool :=
  is.all fun j => intSlotOkB (doms.getD j DomC.empty)

inductive AvieOut where
  | fix
  | conflict (ls : List Literal)
  | prune (pairs : List (Literal × Clause))

/-- Table values absent from the result domain. -/
def avieJBad (dj dk : DomC) : List Int :=
  (intCandidates dj).filter fun w => !dk.memIntView w

/-- Result values absent from the selected table slot. -/
def avieKBad (dj dk : DomC) : List Int :=
  (intCandidates dk).filter fun w => !dj.memIntView w

/-- Entry-slot prunes: remove selected-slot values absent from the result. -/
def avieJPrunes (i k j : Nat) (idx : Int) (dj dk : DomC) :
    List (Literal × Clause) :=
  (avieJBad dj dk).map fun w =>
    (posNe j w, [posNe j w, posNe i idx, negNe k w])

/-- Result-slot prunes: remove result values absent from the selected
table slot. -/
def avieKPrunes (i k j : Nat) (idx : Int) (dj dk : DomC) :
    List (Literal × Clause) :=
  (avieKBad dj dk).map fun w =>
    (posNe k w, [posNe k w, posNe i idx, negNe j w])

/-- The fixed-index link prunes in both directions, only from sides that
are not already fixed. -/
def avieFixedPrunes (i k j : Nat) (idx : Int) (dj dk : DomC) :
    List (Literal × Clause) :=
  (match dj.fixedValue with
   | some _ => []
   | none => safePrunes dj (avieJPrunes i k j idx dj dk)) ++
  (match dk.fixedValue with
   | some _ => []
   | none => safePrunes dk (avieKPrunes i k j idx dj dk))

/-- A fixed-index value conflict between the selected slot and the result,
for explicit domains. -/
def avieFixedConflictOf? (i k : Nat) (idx : Int) (j : Nat) (dj dk : DomC) :
    Option (List Literal) :=
  match dj.fixedValue with
  | some (.int w) =>
      if dk.memIntView w then none
      else some [posNe j w, posNe i idx, negNe k w]
  | _ =>
      match dk.fixedValue with
      | some (.int w) =>
          if dj.memIntView w then none
          else some [posNe k w, posNe i idx, negNe j w]
      | _ => none

/-- A fixed-index value conflict between the selected slot and the result. -/
def avieFixedConflict? (doms : Array DomC) (i k : Nat) (idx : Int)
    (j : Nat) : Option (List Literal) :=
  avieFixedConflictOf? i k idx j (doms.getD j DomC.empty)
    (doms.getD k DomC.empty)

/-- The result-pinned unsupported-index pair, for explicit domains. -/
def avieBadIndexPinVal? (i k j : Nat) (dk dj : DomC) (idx : Int) :
    Option (Literal × Clause) :=
  match dk.fixedValue with
  | some (.int w) =>
      if dj.memIntView w then none
      else some (posNe i idx, [posNe i idx, posNe k w, negNe j w])
  | _ => none

/-- The unsupported-index prune/conflict for one index value and an
explicit selected table slot. -/
def avieBadIndexPairOf? (i k j : Nat) (dk dj : DomC) (idx : Int) :
    Option (Literal × Clause) :=
  match intBounds dj, intBounds dk with
  | some (jlo, jhi), some (klo, khi) =>
      if jhi < klo then
        some (posNe i idx, [posNe i idx, negLe j jhi, posLe k (klo - 1)])
      else if khi < jlo then
        some (posNe i idx, [posNe i idx, negLe k khi, posLe j (jlo - 1)])
      else
        match dj.fixedValue with
        | some (.int w) =>
            if dk.memIntView w then none
            else some (posNe i idx, [posNe i idx, posNe j w, negNe k w])
        | _ => avieBadIndexPinVal? i k j dk dj idx
  | _, _ => none

/-- The unsupported-index prune/conflict for one index value in the
general branch. -/
def avieBadIndexPair? (doms : Array DomC) (is : List Nat) (i k : Nat)
    (dk : DomC) (idx : Int) : Option (Literal × Clause) :=
  match avieEntry is idx with
  | none => some (posNe i idx, [posNe i idx])
  | some j => avieBadIndexPairOf? i k j dk (doms.getD j DomC.empty) idx

/-- Unsupported index values in the general branch. -/
def avieIndexPrunes (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di dk : DomC) : List (Literal × Clause) :=
  (intCandidates di).filterMap fun idx =>
    avieBadIndexPair? doms is i k dk idx

/-- Result values absent from every table slot. -/
def avieNoSuppPrunes (doms : Array DomC) (is : List Nat) (k : Nat)
    (dk : DomC) : List (Literal × Clause) :=
  match dk.fixedValue with
  | some _ => []
  | none =>
      (intCandidates dk).filterMap fun w =>
        if is.all (fun j => !(doms.getD j DomC.empty).memIntView w) then
          some (posNe k w, posNe k w :: is.map (fun j => negNe j w))
        else none

/-- The general-branch prunes: unsupported index values and unsupported
result values. -/
def avieGeneralPrunes (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di dk : DomC) : List (Literal × Clause) :=
  safePrunes di (avieIndexPrunes doms is i k di dk) ++
    safePrunes dk (avieNoSuppPrunes doms is k dk)

/-- The prune list selected by the stage-2 decision, for explicit index
and result domains. -/
def aviePrunePairsOf (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di dk : DomC) : List (Literal × Clause) :=
  match intBounds di, intBounds dk with
  | some (ilo, ihi), some (klo, khi) =>
      match di.fixedValue with
      | some (.int idx) =>
            match avieEntry is idx with
            | none => []
            | some j =>
                match intBounds (doms.getD j DomC.empty) with
                | none => []
                | some (jlo, jhi) =>
                    if jhi < klo then []
                    else if khi < jlo then []
                    else avieFixedPrunes i k j idx
                      (doms.getD j DomC.empty) dk
        | some _ => []
        | none => avieGeneralPrunes doms is i k di dk
  | _, _ => []

/-- The prune list selected by the stage-2 decision. -/
def aviePrunePairs (doms : Array DomC) (is : List Nat) (i k : Nat) :
    List (Literal × Clause) :=
  aviePrunePairsOf doms is i k (doms.getD i DomC.empty)
    (doms.getD k DomC.empty)

/-- The pure stage-2 decision for explicit index and result domains. -/
def avieOutOf (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di dk : DomC) : AvieOut :=
  match intBounds di, intBounds dk with
  | some (ilo, ihi), some (klo, khi) =>
      match di.fixedValue with
      | some (.int idx) =>
            match avieEntry is idx with
            | none => .conflict [posNe i idx]
            | some j =>
                match intBounds (doms.getD j DomC.empty) with
                | none => .fix
                | some (jlo, jhi) =>
                    if jhi < klo then
                      .conflict [posNe i idx, negLe j jhi, posLe k (klo - 1)]
                    else if khi < jlo then
                      .conflict [posNe i idx, negLe k khi, posLe j (jlo - 1)]
                    else
                      match avieFixedConflict? doms i k idx j with
                      | some ls => .conflict ls
                      | none =>
                          let ps := aviePrunePairs doms is i k
                          if ps.isEmpty then .fix else .prune ps
        | some _ => .fix
        | none =>
            let ps := aviePrunePairs doms is i k
            if ps.isEmpty then .fix else .prune ps
  | _, _ => .fix

/-- The pure stage-2 decision. -/
def avieOut (doms : Array DomC) (is : List Nat) (i k : Nat) : AvieOut :=
  avieOutOf doms is i k (doms.getD i DomC.empty) (doms.getD k DomC.empty)

/-! ### Array/runtime twins for the variable-table element

`avieOutOf` indexes the slot list with `avieEntry` for every index
candidate, recomputes the result-domain bounds for every candidate, and
re-reads `fixedValue` of the selected slot and the result.  The twins
below hoist the slot list to an `Array`, the result bounds, the result
fixed value, and derive the selected slot's integer fixed value from its
already computed hull bounds.  They are installed only in compiled code
by `@[csimp]`; every proof keeps using the list-based definitions. -/

/-- 1-based table lookup with the slot list hoisted to an array. -/
def avieEntryA (isa : Array Nat) (idx : Int) : Option Nat :=
  if 0 < idx then isa[idx.toNat - 1]? else none

theorem avieEntryA_eq (is : List Nat) (idx : Int) :
    avieEntryA is.toArray idx = avieEntry is idx := by
  unfold avieEntryA avieEntry
  rw [List.getElem?_toArray]

/-- The integer value of a domain when its integer view is fixed,
derived from already computed hull bounds and the domain kind. -/
def intFixedOf (d : DomC) (b : Option (Int × Int)) : Option Int :=
  match b with
  | some (lo, hi) => if d.intKindB && lo == hi then some lo else none
  | none => none

/-- A Boolean domain is never fixed to an integer value. -/
theorem bool_fixedValue_int_match_none (bits : UInt8) :
    (match (DomC.bool bits).fixedValue with
     | some (.int w) => some w
     | _ => none) = none := by
  simp only [DomC.fixedValue]
  split
  case h_1 heq => split at heq <;> simp at heq
  case h_2 => simp

theorem intFixedOf_intBounds_eq (d : DomC) :
    intFixedOf d (intBounds d) =
      (match d.fixedValue with
       | some (.int w) => some w
       | _ => none) := by
  cases d with
  | bool bits =>
      simp only [intFixedOf, intBounds, DomC.intKindB]
      split <;> simp [bool_fixedValue_int_match_none]
  | bounds lo hi =>
      by_cases h : hi < lo
      · have hne : lo ≠ hi := by omega
        simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
          DomC.lo?, DomC.hi?, h, hne, beq_iff_eq]
      · by_cases h2 : lo = hi <;>
          simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
            DomC.lo?, DomC.hi?, h, h2, beq_iff_eq]
  | bitset lo words =>
      cases hlo : DomC.lo? (.bitset lo words) with
      | none =>
          simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB, hlo]
      | some a =>
          cases hhi : DomC.hi? (.bitset lo words) with
          | none =>
              simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB, hlo, hhi]
          | some b =>
              by_cases hab : a = b <;>
                simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
                  hlo, hhi, hab, beq_iff_eq]
  | boundsHoles lo hi holes =>
      cases hlo : DomC.lo? (.boundsHoles lo hi holes) with
      | none =>
          simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB, hlo]
      | some a =>
          cases hhi : DomC.hi? (.boundsHoles lo hi holes) with
          | none =>
              simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB, hlo, hhi]
          | some b =>
              by_cases hab : a = b <;>
                simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
                  hlo, hhi, hab, beq_iff_eq]
  | sparse values =>
      cases hhead : arrayHead? values with
      | none =>
          simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
            DomC.lo?, DomC.hi?, hhead]
      | some a =>
          cases hlast : arrayLast? values with
          | none =>
              simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
                DomC.lo?, DomC.hi?, hhead, hlast]
          | some b =>
              by_cases hab : a = b <;>
                simp [intFixedOf, intBounds, DomC.fixedValue, DomC.intKindB,
                  DomC.lo?, DomC.hi?, hhead, hlast, hab, beq_iff_eq]

theorem intFixedOf_some (d : DomC) {lo hi : Int}
    (hb : intBounds d = some (lo, hi)) :
    intFixedOf d (some (lo, hi)) =
      (match d.fixedValue with
       | some (.int w) => some w
       | _ => none) := by
  unfold intFixedOf
  rw [← hb]
  exact intFixedOf_intBounds_eq d

/-- The result-pinned unsupported-index pair with the result fixed value
hoisted. -/
def avieBadIndexPinValFA (i k j : Nat) (dk dj : DomC)
    (fk : Option Value) (idx : Int) : Option (Literal × Clause) :=
  match fk with
  | some (.int w) =>
      if dj.memIntView w then none
      else some (posNe i idx, [posNe i idx, posNe k w, negNe j w])
  | _ => none

theorem avieBadIndexPinValFA_eq (i k j : Nat) (dk dj : DomC) (idx : Int) :
    avieBadIndexPinValFA i k j dk dj dk.fixedValue idx =
      avieBadIndexPinVal? i k j dk dj idx := by
  unfold avieBadIndexPinValFA avieBadIndexPinVal?
  rfl

/-- `avieBadIndexPairOf?` with the result bounds and fixed value hoisted
and the selected slot's fixed value derived from its hull bounds. -/
def avieBadIndexPairOfFA (i k j : Nat) (dk dj : DomC)
    (bk : Option (Int × Int)) (fk : Option Value) (idx : Int) :
    Option (Literal × Clause) :=
  match intBounds dj, bk with
  | some (jlo, jhi), some (klo, khi) =>
      if jhi < klo then
        some (posNe i idx, [posNe i idx, negLe j jhi, posLe k (klo - 1)])
      else if khi < jlo then
        some (posNe i idx, [posNe i idx, negLe k khi, posLe j (jlo - 1)])
      else
        match intFixedOf dj (some (jlo, jhi)) with
        | some w =>
            if dk.memIntView w then none
            else some (posNe i idx, [posNe i idx, posNe j w, negNe k w])
        | none => avieBadIndexPinValFA i k j dk dj fk idx
  | _, _ => none

theorem avieBadIndexPairOfFA_eq (i k j : Nat) (dk dj : DomC) (idx : Int) :
    avieBadIndexPairOfFA i k j dk dj (intBounds dk) dk.fixedValue idx =
      avieBadIndexPairOf? i k j dk dj idx := by
  unfold avieBadIndexPairOfFA avieBadIndexPairOf?
  cases hdj : intBounds dj with
  | none => rfl
  | some p =>
      obtain ⟨jlo, jhi⟩ := p
      cases hdk : intBounds dk with
      | none => rfl
      | some q =>
          obtain ⟨klo, khi⟩ := q
          dsimp only
          rw [intFixedOf_some dj hdj]
          cases h : dj.fixedValue with
          | none => rfl
          | some v =>
              cases v with
              | bool b => rfl
              | int w => rfl
              | setOfInt s => rfl
              | array xs => rfl

/-- `avieBadIndexPair?` with the array table and hoisted result data. -/
def avieBadIndexPairFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (dk : DomC) (bk : Option (Int × Int)) (fk : Option Value) (idx : Int) :
    Option (Literal × Clause) :=
  match avieEntryA isa idx with
  | none => some (posNe i idx, [posNe i idx])
  | some j => avieBadIndexPairOfFA i k j dk (doms.getD j DomC.empty) bk fk idx

theorem avieBadIndexPairFA_eq (doms : Array DomC) (is : List Nat)
    (i k : Nat) (dk : DomC) (idx : Int) :
    avieBadIndexPairFA doms is.toArray i k dk (intBounds dk) dk.fixedValue idx =
      avieBadIndexPair? doms is i k dk idx := by
  unfold avieBadIndexPairFA avieBadIndexPair?
  rw [avieEntryA_eq]
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      exact avieBadIndexPairOfFA_eq i k j dk (doms.getD j DomC.empty) idx

/-- `avieIndexPrunes` with the array table and hoisted result data. -/
def avieIndexPrunesFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (di dk : DomC) (bk : Option (Int × Int)) (fk : Option Value) :
    List (Literal × Clause) :=
  (intCandidates di).filterMap fun idx =>
    avieBadIndexPairFA doms isa i k dk bk fk idx

theorem avieIndexPrunesFA_eq (doms : Array DomC) (is : List Nat)
    (i k : Nat) (di dk : DomC) :
    avieIndexPrunesFA doms is.toArray i k di dk (intBounds dk) dk.fixedValue =
      avieIndexPrunes doms is i k di dk := by
  unfold avieIndexPrunesFA avieIndexPrunes
  congr 1
  funext idx
  exact avieBadIndexPairFA_eq doms is i k dk idx

/-- `avieGeneralPrunes` with the array table and hoisted result data. -/
def avieGeneralPrunesFA (doms : Array DomC) (isa : Array Nat) (is : List Nat)
    (i k : Nat) (di dk : DomC) (bk : Option (Int × Int)) (fk : Option Value) :
    List (Literal × Clause) :=
  safePrunes di (avieIndexPrunesFA doms isa i k di dk bk fk) ++
    safePrunes dk (avieNoSuppPrunes doms is k dk)

theorem avieGeneralPrunesFA_eq (doms : Array DomC) (is : List Nat)
    (i k : Nat) (di dk : DomC) :
    avieGeneralPrunesFA doms is.toArray is i k di dk (intBounds dk) dk.fixedValue =
      avieGeneralPrunes doms is i k di dk := by
  unfold avieGeneralPrunesFA avieGeneralPrunes
  rw [avieIndexPrunesFA_eq]

/-- `aviePrunePairsOf` with the array table and hoisted bounds. -/
def aviePrunePairsOfFA (doms : Array DomC) (isa : Array Nat) (is : List Nat)
    (i k : Nat) (di dk : DomC) (fi : Option Value)
    (bi bk : Option (Int × Int)) (fk : Option Value) :
    List (Literal × Clause) :=
  match bi, bk with
  | some (_ilo, _ihi), some (klo, khi) =>
      match fi with
      | some (.int idx) =>
            match avieEntryA isa idx with
            | none => []
            | some j =>
                match intBounds (doms.getD j DomC.empty) with
                | none => []
                | some (jlo, jhi) =>
                    if jhi < klo then []
                    else if khi < jlo then []
                    else avieFixedPrunes i k j idx
                      (doms.getD j DomC.empty) dk
        | some _ => []
        | none => avieGeneralPrunesFA doms isa is i k di dk bk fk
  | _, _ => []

theorem aviePrunePairsOfFA_eq (doms : Array DomC) (is : List Nat)
    (i k : Nat) (di dk : DomC) :
    aviePrunePairsOfFA doms is.toArray is i k di dk di.fixedValue
        (intBounds di) (intBounds dk) dk.fixedValue =
      aviePrunePairsOf doms is i k di dk := by
  unfold aviePrunePairsOfFA aviePrunePairsOf
  simp only [avieEntryA_eq, avieGeneralPrunesFA_eq]

/-- `avieOutOf` with the array table and hoisted bounds. -/
def avieOutOfFA (doms : Array DomC) (isa : Array Nat) (is : List Nat) (i k : Nat)
    (di dk : DomC) : AvieOut :=
  let fi := di.fixedValue
  let bi := intBounds di
  let bk := intBounds dk
  let fk := dk.fixedValue
  match bi, bk with
  | some (_ilo, _ihi), some (klo, khi) =>
      match fi with
      | some (.int idx) =>
            match avieEntryA isa idx with
            | none => .conflict [posNe i idx]
            | some j =>
                match intBounds (doms.getD j DomC.empty) with
                | none => .fix
                | some (jlo, jhi) =>
                    if jhi < klo then
                      .conflict [posNe i idx, negLe j jhi, posLe k (klo - 1)]
                    else if khi < jlo then
                      .conflict [posNe i idx, negLe k khi, posLe j (jlo - 1)]
                    else
                      match avieFixedConflict? doms i k idx j with
                      | some ls => .conflict ls
                      | none =>
                          let ps := aviePrunePairsOfFA doms isa is i k di dk fi bi bk fk
                          if ps.isEmpty then .fix else .prune ps
        | some _ => .fix
        | none =>
            let ps := aviePrunePairsOfFA doms isa is i k di dk fi bi bk fk
            if ps.isEmpty then .fix else .prune ps
  | _, _ => .fix

theorem avieOutOfFA_eq (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di dk : DomC) (hdi : di = doms.getD i DomC.empty)
    (hdk : dk = doms.getD k DomC.empty) :
    avieOutOfFA doms is.toArray is i k di dk = avieOutOf doms is i k di dk := by
  subst hdi
  subst hdk
  unfold avieOutOfFA avieOutOf aviePrunePairs
  simp only [avieEntryA_eq, aviePrunePairsOfFA_eq]

/-- The `avieOutFA` equation at the domains read by `avieOut`. -/
theorem avieOutOfFA_getD_eq (doms : Array DomC) (is : List Nat) (i k : Nat) :
    avieOutOfFA doms is.toArray is i k
        (doms.getD i DomC.empty) (doms.getD k DomC.empty) =
      avieOut doms is i k := by
  unfold avieOut
  exact avieOutOfFA_eq doms is i k _ _ rfl rfl

/-- Runtime twin of `avieOut` used by compiled code only. -/
def avieOutFast (doms : Array DomC) (is : List Nat) (i k : Nat) : AvieOut :=
  avieOutOfFA doms is.toArray is i k (doms.getD i DomC.empty)
    (doms.getD k DomC.empty)

theorem avieOutFast_eq (doms : Array DomC) (is : List Nat) (i k : Nat) :
    avieOutFast doms is i k = avieOut doms is i k := by
  unfold avieOutFast avieOut
  exact avieOutOfFA_eq doms is i k _ _ rfl rfl

@[csimp] theorem avieOut_eq_fast : @avieOut = @avieOutFast := by
  funext doms is i k
  exact (avieOutFast_eq doms is i k).symm

/-! ### Stage-2 membership lemmas for the pure prune lists -/

theorem avieJPrunes_mem {i k j : Nat} {idx : Int} {dj dk : DomC}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avieJPrunes i k j idx dj dk) :
    ∃ w : Int, w ∈ intCandidates dj ∧ dk.memIntView w = false ∧
      l = posNe j w ∧ reason = [posNe j w, posNe i idx, negNe k w] := by
  unfold avieJPrunes at h
  rw [List.mem_map] at h
  obtain ⟨w, hw, hpair⟩ := h
  unfold avieJBad at hw
  rw [List.mem_filter] at hw
  obtain ⟨hmem, hbad⟩ := hw
  cases hpair
  exact ⟨w, hmem, by simpa using hbad, rfl, rfl⟩

theorem avieKPrunes_mem {i k j : Nat} {idx : Int} {dj dk : DomC}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avieKPrunes i k j idx dj dk) :
    ∃ w : Int, w ∈ intCandidates dk ∧ dj.memIntView w = false ∧
      l = posNe k w ∧ reason = [posNe k w, posNe i idx, negNe j w] := by
  unfold avieKPrunes at h
  rw [List.mem_map] at h
  obtain ⟨w, hw, hpair⟩ := h
  unfold avieKBad at hw
  rw [List.mem_filter] at hw
  obtain ⟨hmem, hbad⟩ := hw
  cases hpair
  exact ⟨w, hmem, by simpa using hbad, rfl, rfl⟩

theorem safePrunes_mem {d : DomC} {ps : List (Literal × Clause)}
    {q : Literal × Clause} (h : q ∈ safePrunes d ps) : q ∈ ps := by
  unfold safePrunes at h
  split at h
  · exact h
  · simp at h

theorem avieFixedPrunes_mem {i k j : Nat} {idx : Int} {dj dk : DomC}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avieFixedPrunes i k j idx dj dk) :
    (dj.fixedValue = none ∧ ∃ w : Int, w ∈ intCandidates dj ∧
        dk.memIntView w = false ∧
        l = posNe j w ∧ reason = [posNe j w, posNe i idx, negNe k w]) ∨
    (dk.fixedValue = none ∧ ∃ w : Int, w ∈ intCandidates dk ∧
        dj.memIntView w = false ∧
        l = posNe k w ∧ reason = [posNe k w, posNe i idx, negNe j w]) := by
  unfold avieFixedPrunes at h
  rcases List.mem_append.mp h with h1 | h2
  · split at h1
    · simp at h1
    · rename_i hfix
      obtain ⟨w, hw, hbad, hl, hr⟩ := avieJPrunes_mem (safePrunes_mem h1)
      exact Or.inl ⟨hfix, w, hw, hbad, hl, hr⟩
  · split at h2
    · simp at h2
    · rename_i hfix
      obtain ⟨w, hw, hbad, hl, hr⟩ := avieKPrunes_mem (safePrunes_mem h2)
      exact Or.inr ⟨hfix, w, hw, hbad, hl, hr⟩

theorem avieIndexPrunes_mem {doms : Array DomC} {is : List Nat} {i k : Nat}
    {di dk : DomC} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avieIndexPrunes doms is i k di dk) :
    ∃ idx : Int, idx ∈ intCandidates di ∧
      avieBadIndexPair? doms is i k dk idx = some (l, reason) := by
  unfold avieIndexPrunes at h
  rw [List.mem_filterMap] at h
  obtain ⟨idx, hidx, hf⟩ := h
  exact ⟨idx, hidx, hf⟩

theorem avieNoSuppPrunes_mem {doms : Array DomC} {is : List Nat} {k : Nat}
    {dk : DomC} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avieNoSuppPrunes doms is k dk) :
    ∃ w : Int, w ∈ intCandidates dk ∧ dk.fixedValue = none ∧
      is.all (fun j => !(doms.getD j DomC.empty).memIntView w) = true ∧
      l = posNe k w ∧ reason = posNe k w :: is.map (fun j => negNe j w) := by
  unfold avieNoSuppPrunes at h
  split at h
  · simp at h
  · rename_i hfix
    rw [List.mem_filterMap] at h
    obtain ⟨w, hw, hf⟩ := h
    split at hf
    · rename_i hall
      cases hf
      exact ⟨w, hw, hfix, hall, rfl, rfl⟩
    · simp at hf

theorem avieGeneralPrunes_mem {doms : Array DomC} {is : List Nat} {i k : Nat}
    {di dk : DomC} {l : Literal} {reason : Clause}
    (hfixi : di.fixedValue = none)
    (h : (l, reason) ∈ avieGeneralPrunes doms is i k di dk) :
    (∃ idx : Int, idx ∈ intCandidates di ∧
        avieBadIndexPair? doms is i k dk idx = some (l, reason)) ∨
    (∃ w : Int, w ∈ intCandidates dk ∧ dk.fixedValue = none ∧
        is.all (fun j => !(doms.getD j DomC.empty).memIntView w) = true ∧
        l = posNe k w ∧ reason = posNe k w :: is.map (fun j => negNe j w)) := by
  unfold avieGeneralPrunes at h
  rcases List.mem_append.mp h with h1 | h2
  · exact Or.inl (avieIndexPrunes_mem (safePrunes_mem h1))
  · exact Or.inr (avieNoSuppPrunes_mem (safePrunes_mem h2))

/-! ### Stage-2 entailment of the pure clauses -/

theorem avie_entailed_out (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} (hnone : avieEntry is idx = none) :
    Entailed p [posNe i idx] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResOut_entailed hs hnone

theorem avie_entailed_J (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {w : Int} (he : avieEntry is idx = some j) :
    Entailed p [posNe j w, posNe i idx, negNe k w] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResJ_entailed hs he

theorem avie_entailed_K (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {w : Int} (he : avieEntry is idx = some j) :
    Entailed p [posNe k w, posNe i idx, negNe j w] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResK_entailed hs he

theorem avie_entailed_pinVal (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {v : Int} (he : avieEntry is idx = some j) :
    Entailed p [posNe i idx, posNe k v, negNe j v] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResPinVal_entailed hs he

theorem avie_entailed_single (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {w : Int} (he : avieEntry is idx = some j) :
    Entailed p [posNe i idx, posNe j w, negNe k w] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResSingle_entailed hs he

theorem avie_entailed_below (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {mx mn : Int} (he : avieEntry is idx = some j)
    (hlt : mx < mn) :
    Entailed p [posNe i idx, negLe j mx, posLe k (mn - 1)] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResBelow_entailed hs he hlt

theorem avie_entailed_above (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {mx mn : Int} (he : avieEntry is idx = some j)
    (hlt : mx < mn) :
    Entailed p [posNe i idx, negLe k mx, posLe j (mn - 1)] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResAbove_entailed hs he hlt

theorem avie_entailed_noSupp (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {w : Int} :
    Entailed p (posNe k w :: is.map (fun j => negNe j w)) := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avieResNoSupp_entailed hs

/-- Inversion of the result-pinned unsupported-index builder. -/
theorem avieBadIndexPinVal?_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k j : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {dk dj : DomC} {idx : Int} {l : Literal} {reason : Clause}
    (he : avieEntry is idx = some j)
    (hf : avieBadIndexPinVal? i k j dk dj idx = some (l, reason)) :
    Entailed p reason := by
  unfold avieBadIndexPinVal? at hf
  cases hfk : dk.fixedValue with
  | none =>
      simp only [hfk] at hf
      simp at hf
  | some v =>
      cases v with
      | int w =>
          simp only [hfk] at hf
          by_cases hm : dj.memIntView w = true
          · rw [if_pos hm] at hf
            simp at hf
          · rw [if_neg hm] at hf
            cases hf
            exact avie_entailed_pinVal p is i k hmem he
      | bool b =>
          simp only [hfk] at hf
          simp at hf
      | setOfInt s =>
          simp only [hfk] at hf
          simp at hf
      | array xs =>
          simp only [hfk] at hf
          simp at hf

/-- Inversion of the explicit-slot unsupported-index builder. -/
theorem avieBadIndexPairOf?_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k j : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    {dk dj : DomC} {idx : Int} {l : Literal} {reason : Clause}
    (he : avieEntry is idx = some j)
    (hf : avieBadIndexPairOf? i k j dk dj idx = some (l, reason)) :
    Entailed p reason := by
  unfold avieBadIndexPairOf? at hf
  cases hb : intBounds dj with
  | none =>
      rw [hb] at hf
      simp at hf
  | some p =>
      obtain ⟨jlo, jhi⟩ := p
      cases hbk : intBounds dk with
      | none =>
          rw [hb, hbk] at hf
          simp at hf
      | some q =>
          obtain ⟨klo, khi⟩ := q
          simp only [hb, hbk] at hf
          by_cases hlt : jhi < klo
          · rw [if_pos hlt] at hf
            cases hf
            exact avie_entailed_below p is i k hmem he hlt
          · rw [if_neg hlt] at hf
            by_cases hlt2 : khi < jlo
            · rw [if_pos hlt2] at hf
              cases hf
              exact avie_entailed_above p is i k hmem he hlt2
            · rw [if_neg hlt2] at hf
              cases hfix : dj.fixedValue with
              | none =>
                  simp only [hfix] at hf
                  exact avieBadIndexPinVal?_entailed p is i k j hmem he hf
              | some v =>
                  cases v with
                  | int w =>
                      simp only [hfix] at hf
                      by_cases hmemv : dk.memIntView w = true
                      · rw [if_pos hmemv] at hf
                        simp at hf
                      · rw [if_neg hmemv] at hf
                        cases hf
                        exact avie_entailed_single p is i k hmem he
                  | bool b =>
                      simp only [hfix] at hf
                      exact avieBadIndexPinVal?_entailed p is i k j hmem he hf
                  | setOfInt s =>
                      simp only [hfix] at hf
                      exact avieBadIndexPinVal?_entailed p is i k j hmem he hf
                  | array xs =>
                      simp only [hfix] at hf
                      exact avieBadIndexPinVal?_entailed p is i k j hmem he hf

/-- Inversion of the general-branch unsupported-index pair builder. -/
theorem avieBadIndexPair?_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (doms : Array DomC) (dk : DomC) {idx : Int} {l : Literal}
    {reason : Clause}
    (hf : avieBadIndexPair? doms is i k dk idx = some (l, reason)) :
    Entailed p reason := by
  unfold avieBadIndexPair? at hf
  cases he : avieEntry is idx with
  | none =>
      rw [he] at hf
      cases hf
      exact avie_entailed_out p is i k hmem he
  | some j =>
      rw [he] at hf
      exact avieBadIndexPairOf?_entailed p is i k j hmem he hf

theorem aviePrunePairs_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (doms : Array DomC) {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aviePrunePairs doms is i k) : Entailed p reason := by
  unfold aviePrunePairs aviePrunePairsOf at h
  split at h
  · rename_i ilo ihi klo khi hbi hbk
    cases hfix : (doms.getD i DomC.empty).fixedValue with
    | none =>
        simp only [hfix] at h
        obtain (⟨idx, hidx, hf⟩ |
          ⟨w, hw, hfixk, hall, rfl, rfl⟩) := avieGeneralPrunes_mem hfix h
        · exact avieBadIndexPair?_entailed p is i k hmem doms
            (doms.getD k DomC.empty) hf
        · exact avie_entailed_noSupp p is i k hmem
    | some v =>
        cases v with
        | int idx =>
            simp only [hfix] at h
            cases he : avieEntry is idx with
            | none =>
                simp only [he] at h
                simp at h
            | some j =>
                simp only [he] at h
                split at h
                · simp at h
                · rename_i jlo jhi hbj
                  split at h
                  · simp at h
                  · split at h
                    · simp at h
                    · obtain (⟨_, w, hw, hbad, rfl, rfl⟩ |
                        ⟨_, w, hw, hbad, rfl, rfl⟩) := avieFixedPrunes_mem h
                      · exact avie_entailed_J p is i k hmem he
                      · exact avie_entailed_K p is i k hmem he
        | bool b => simp only [hfix] at h; simp at h
        | setOfInt s => simp only [hfix] at h; simp at h
        | array xs => simp only [hfix] at h; simp at h
  · simp at h

/-- Inversion of the fixed-index value conflict. -/
theorem avieFixedConflict?_cases {doms : Array DomC} {i k : Nat} {idx : Int}
    {j : Nat} {ls : List Literal}
    (h : avieFixedConflict? doms i k idx j = some ls) :
    (∃ w : Int, (doms.getD j DomC.empty).fixedValue = some (.int w) ∧
        (doms.getD k DomC.empty).memIntView w = false ∧
        ls = [posNe j w, posNe i idx, negNe k w]) ∨
    (∃ w : Int, (doms.getD k DomC.empty).fixedValue = some (.int w) ∧
        (doms.getD j DomC.empty).memIntView w = false ∧
        ls = [posNe k w, posNe i idx, negNe j w]) := by
  unfold avieFixedConflict? avieFixedConflictOf? at h
  split at h
  · rename_i w hfix
    split at h
    · simp at h
    · rename_i hbad
      cases h
      exact Or.inl ⟨w, hfix, by simpa using hbad, rfl⟩
  · split at h
    · rename_i w hfix
      split at h
      · simp at h
      · rename_i hbad
        cases h
        exact Or.inr ⟨w, hfix, by simpa using hbad, rfl⟩
    · simp at h

/-- Evaluation of every stage-2 prune: the pivot is unassigned and all
other reason literals are false. -/
theorem aviePrunePairs_eval (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (.arrayVarIntElementSlot is i k)).toArray)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ aviePrunePairs view.doms is i k) :
    (view.doms.getD l.atom.slot DomC.empty).evalLit l = none ∧
      ∀ q ∈ reason, q ≠ l →
        (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  have hWF' : ViewWF view (is ++ [i, k]).toArray := by
    simpa [dcSlotsFull] using hWF
  have hdi_wf : (view.doms.getD i DomC.empty).WF :=
    hWF'.dom_wf (s := i) (by simp)
  have hdk_wf : (view.doms.getD k DomC.empty).WF :=
    hWF'.dom_wf (s := k) (by simp)
  unfold aviePrunePairs aviePrunePairsOf at h
  split at h
  · rename_i ilo ihi klo khi hbi hbk
    split at h
    · rename_i idx hfix
      split at h
      · simp at h
      · rename_i j hent
        split at h
        · simp at h
        · rename_i jlo jhi hbj
          split at h
          · simp at h
          · split at h
            · simp at h
            · have hdi_mem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
                (DomC.fixedValue_sound _ hdi_wf hfix).1
              have hipos : (view.doms.getD i DomC.empty).evalLit (posNe i idx) = some false :=
                DomC.evalLit_posNe_of_fixed hfix hdi_mem
              have hdj_wf : (view.doms.getD j DomC.empty).WF :=
                hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
              rcases avieFixedPrunes_mem h with
                ⟨hfvj, w, hw, hbadk, rfl, rfl⟩ |
                ⟨hfvk, w, hw, hbadj, rfl, rfl⟩
              · have hdjm : (view.doms.getD j DomC.empty).mem (.int w) = true :=
                  mem_intCandidates hw
                have hjn : (view.doms.getD j DomC.empty).evalLit (posNe j w) = none := by
                  have := DomC.evalLit_neLit_none_of_not_fixed
                    (d := view.doms.getD j DomC.empty) (s := j) (v := .int w) hfvj hdjm
                  simpa [neLit] using this
                refine ⟨hjn, ?_⟩
                intro q hq hne
                rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
                rcases hq with rfl | rfl | rfl
                · exact absurd rfl hne
                · simpa [posNe, Atom.slot] using hipos
                · simpa [negNe, Atom.slot] using
                    DomC.evalLit_negNe_false_of_not_memIntView
                      (view.doms.getD k DomC.empty) k hbadk
              · have hdkm : (view.doms.getD k DomC.empty).mem (.int w) = true :=
                  mem_intCandidates hw
                have hkn : (view.doms.getD k DomC.empty).evalLit (posNe k w) = none := by
                  have := DomC.evalLit_neLit_none_of_not_fixed
                    (d := view.doms.getD k DomC.empty) (s := k) (v := .int w) hfvk hdkm
                  simpa [neLit] using this
                refine ⟨hkn, ?_⟩
                intro q hq hne
                rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
                rcases hq with rfl | rfl | rfl
                · exact absurd rfl hne
                · simpa [posNe, Atom.slot] using hipos
                · simpa [negNe, Atom.slot] using
                    DomC.evalLit_negNe_false_of_not_memIntView
                      (view.doms.getD j DomC.empty) j hbadj
    · simp at h
    · rename_i hfix
      have hgen := avieGeneralPrunes_mem
        (di := view.doms.getD i DomC.empty) hfix h
      rcases hgen with
        ⟨idx, hidx, hf⟩ |
        ⟨w, hw, hfixk, hall, hll, hrr⟩
      · have hdix : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
          mem_intCandidates hidx
        have hipos : (view.doms.getD i DomC.empty).evalLit (posNe i idx) = none := by
          have := DomC.evalLit_neLit_none_of_not_fixed
            (d := view.doms.getD i DomC.empty) (s := i) (v := .int idx) hfix hdix
          simpa [neLit] using this
        unfold avieBadIndexPair? at hf
        split at hf
        · rename_i hnone
          cases hf
          refine ⟨hipos, ?_⟩
          intro q hq hne
          rw [List.mem_singleton] at hq
          subst hq
          exact absurd rfl hne
        · rename_i j hent
          have hdj_wf : (view.doms.getD j DomC.empty).WF :=
            hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
          unfold avieBadIndexPairOf? at hf
          split at hf
          · rename_i jlo jhi klo2 khi2 hbj hbk2
            have hbj' := intBounds_some_iff.mp hbj
            have hbk2' := intBounds_some_iff.mp hbk2
            have hdjle : jlo ≤ jhi :=
              DomC.lo?_le_hi? _ hdj_wf hbj'.1 hbj'.2
            have hdkle : klo2 ≤ khi2 :=
              DomC.lo?_le_hi? _ hdk_wf hbk2'.1 hbk2'.2
            split at hf
            · rename_i hlt
              cases hf
              refine ⟨hipos, ?_⟩
              intro q hq hne
              rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl
              · exact absurd rfl hne
              · simpa [negLe, Atom.slot] using
                  evalLit_negLe_false_of_hi_le
                    (d := view.doms.getD j DomC.empty)
                    hbj'.1 hbj'.2 (Int.le_refl jhi) (by omega)
              · simpa [posLe, Atom.slot] using
                  evalLit_posLe_false_of_lo_gt
                    (d := view.doms.getD k DomC.empty)
                    hbk2'.1 hbk2'.2 (by omega) (by omega)
            · split at hf
              · rename_i hlt2
                cases hf
                refine ⟨hipos, ?_⟩
                intro q hq hne
                rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
                rcases hq with rfl | rfl | rfl
                · exact absurd rfl hne
                · simpa [negLe, Atom.slot] using
                    evalLit_negLe_false_of_hi_le
                      (d := view.doms.getD k DomC.empty)
                      hbk2'.1 hbk2'.2 (Int.le_refl khi2) (by omega)
                · simpa [posLe, Atom.slot] using
                    evalLit_posLe_false_of_lo_gt
                      (d := view.doms.getD j DomC.empty)
                      hbj'.1 hbj'.2 (by omega) (by omega)
              · split at hf
                · rename_i w hfw
                  split at hf
                  · simp at hf
                  · rename_i hbad
                    cases hf
                    refine ⟨hipos, ?_⟩
                    intro q hq hne
                    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
                    rcases hq with rfl | rfl | rfl
                    · exact absurd rfl hne
                    · have hmemw : (view.doms.getD j DomC.empty).mem (.int w) = true :=
                        (DomC.fixedValue_sound _ hdj_wf hfw).1
                      simpa [posNe, Atom.slot] using
                        DomC.evalLit_posNe_of_fixed hfw hmemw
                    · simpa [negNe, Atom.slot] using
                        DomC.evalLit_negNe_false_of_not_memIntView
                          (view.doms.getD k DomC.empty) k (by simpa using hbad)
                · unfold avieBadIndexPinVal? at hf
                  split at hf
                  · rename_i w hfw
                    split at hf
                    · simp at hf
                    · rename_i hbad
                      cases hf
                      refine ⟨hipos, ?_⟩
                      intro q hq hne
                      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
                      rcases hq with rfl | rfl | rfl
                      · exact absurd rfl hne
                      · have hmemw : (view.doms.getD k DomC.empty).mem (.int w) = true :=
                          (DomC.fixedValue_sound _ hdk_wf hfw).1
                        simpa [posNe, Atom.slot] using
                          DomC.evalLit_posNe_of_fixed hfw hmemw
                      · simpa [negNe, Atom.slot] using
                          DomC.evalLit_negNe_false_of_not_memIntView
                            (view.doms.getD j DomC.empty) j (by simpa using hbad)
                  · simp at hf
          · simp at hf
      · have hdkm : (view.doms.getD k DomC.empty).mem (.int w) = true :=
          mem_intCandidates hw
        have hkn : (view.doms.getD k DomC.empty).evalLit (posNe k w) = none := by
          have := DomC.evalLit_neLit_none_of_not_fixed
            (d := view.doms.getD k DomC.empty) (s := k) (v := .int w) hfixk hdkm
          simpa [neLit] using this
        subst hll
        subst hrr
        refine ⟨hkn, ?_⟩
        intro q hq hne
        rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact absurd rfl hne
        · rw [List.mem_map] at hq
          obtain ⟨j, hj, rfl⟩ := hq
          have hallj := List.all_eq_true.mp hall j hj
          have hbad : (view.doms.getD j DomC.empty).memIntView w = false := by
            simpa using hallj
          simpa [negNe, Atom.slot] using
            DomC.evalLit_negNe_false_of_not_memIntView
              (view.doms.getD j DomC.empty) j hbad
  · simp at h

/-- Inversion of the stage-2 conflict output. -/
theorem avieOut_conflict_cases {doms : Array DomC} {is : List Nat} {i k : Nat}
    {ls : List Literal} (h : avieOut doms is i k = .conflict ls) :
    (∃ idx : Int, (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = none ∧ ls = [posNe i idx]) ∨
    (∃ (idx : Int) (j : Nat) (jlo jhi klo khi : Int),
        (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        intBounds (doms.getD j DomC.empty) = some (jlo, jhi) ∧
        intBounds (doms.getD k DomC.empty) = some (klo, khi) ∧
        jhi < klo ∧ ls = [posNe i idx, negLe j jhi, posLe k (klo - 1)]) ∨
    (∃ (idx : Int) (j : Nat) (jlo jhi klo khi : Int),
        (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        intBounds (doms.getD j DomC.empty) = some (jlo, jhi) ∧
        intBounds (doms.getD k DomC.empty) = some (klo, khi) ∧
        khi < jlo ∧ ls = [posNe i idx, negLe k khi, posLe j (jlo - 1)]) ∨
    (∃ (idx : Int) (j : Nat),
        (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        ((∃ w : Int, (doms.getD j DomC.empty).fixedValue = some (.int w) ∧
            (doms.getD k DomC.empty).memIntView w = false ∧
            ls = [posNe j w, posNe i idx, negNe k w]) ∨
         (∃ w : Int, (doms.getD k DomC.empty).fixedValue = some (.int w) ∧
            (doms.getD j DomC.empty).memIntView w = false ∧
            ls = [posNe k w, posNe i idx, negNe j w]))) := by
  unfold avieOut avieOutOf at h
  split at h
  · rename_i ilo ihi klo khi hbi hbk
    split at h
    · rename_i idx hfix
      split at h
      · rename_i hnone
        cases h
        exact Or.inl ⟨idx, hfix, hnone, rfl⟩
      · rename_i j hent
        split at h
        · cases h
        · rename_i jlo jhi hbj
          split at h
          · rename_i hlt
            cases h
            exact Or.inr (Or.inl
              ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, rfl⟩)
          · split at h
            · rename_i hlt2
              cases h
              exact Or.inr (Or.inr (Or.inl
                ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt2, rfl⟩))
            · split at h
              · rename_i lsc hfc
                injection h with hls
                subst hls
                rcases avieFixedConflict?_cases hfc with
                  ⟨w, hfw, hbad, rfl⟩ | ⟨w, hfw, hbad, rfl⟩
                · exact Or.inr (Or.inr (Or.inr
                    ⟨idx, j, hfix, hent, Or.inl ⟨w, hfw, hbad, rfl⟩⟩))
                · exact Or.inr (Or.inr (Or.inr
                    ⟨idx, j, hfix, hent, Or.inr ⟨w, hfw, hbad, rfl⟩⟩))
              · dsimp only at h
                split at h
                · cases h
                · cases h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · cases h
  · cases h

/-- Inversion of the stage-2 prune output. -/
theorem avieOut_prune_cases {doms : Array DomC} {is : List Nat} {i k : Nat}
    {pairs : List (Literal × Clause)}
    (h : avieOut doms is i k = .prune pairs) :
    pairs = aviePrunePairs doms is i k ∧
      ((∃ idx : Int, (doms.getD i DomC.empty).fixedValue = some (.int idx)) ∨
       (doms.getD i DomC.empty).fixedValue = none) := by
  unfold avieOut avieOutOf at h
  split at h
  · rename_i ilo ihi klo khi hbi hbk
    split at h
    · rename_i idx hfix
      split at h
      · cases h
      · rename_i j hent
        split at h
        · cases h
        · rename_i jlo jhi hbj
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · dsimp only at h
                split at h
                · rename_i lsc hfc
                  cases h
                · injection h with hp
                  exact ⟨hp.symm, Or.inl ⟨idx, hfix⟩⟩
    · cases h
    · rename_i hfix
      dsimp only at h
      split at h
      · cases h
      · injection h with hp
        exact ⟨hp.symm, Or.inr hfix⟩
  · cases h

/-! ### The stage-2 builder -/

/-- The variable-table integer element propagator. -/
def arrayVarIntElementPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints) : PropV2 p T :=
  let isa := is.toArray
  { vars := (dcSlotsFull (.arrayVarIntElementSlot is i k)).toArray
    events := ((is.map fun j => (j, EventKind.bounds)) ++
      [(i, EventKind.bounds), (k, EventKind.bounds),
        (i, EventKind.fix), (k, EventKind.fix)]).toArray
    run := fun view =>
      match hout : avieOutOfFA view.doms isa is i k
          (view.doms.getD i DomC.empty) (view.doms.getD k DomC.empty) with
      | .fix => .fix
      | .conflict ls =>
          .conflict (EClause.ofLiterals p T ls (by
            have hout' : avieOut view.doms is i k = .conflict ls := by
              rw [← avieOutOfFA_getD_eq view.doms is i k]
              exact hout
            rcases avieOut_conflict_cases hout' with
              ⟨idx, hfix, hnone, rfl⟩ |
              ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, rfl⟩ |
              ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, rfl⟩ |
              ⟨idx, j, hfix, hent, hrest⟩
            · exact avie_entailed_out p is i k hmem hnone
            · exact avie_entailed_below p is i k hmem hent hlt
            · exact avie_entailed_above p is i k hmem hent hlt
            · rcases hrest with ⟨w, hfw, hbad, rfl⟩ | ⟨w, hfw, hbad, rfl⟩
              · exact avie_entailed_J p is i k hmem hent
              · exact avie_entailed_K p is i k hmem hent))
      | .prune pairs =>
          .prune (mkElemPruneArray p T pairs
            (fun l reason hlr =>
              aviePrunePairs_entailed p is i k hmem view.doms (by
                have hout' : avieOut view.doms is i k = .prune pairs := by
                  rw [← avieOutOfFA_getD_eq view.doms is i k]
                  exact hout
                have hp := (avieOut_prune_cases hout').1
                rwa [hp] at hlr))) }

theorem arrayVarIntElementPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .conflict ec) :
    (∃ idx : Int,
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = none ∧
        T.decodeClause ec.lits = [posNe i idx]) ∨
    (∃ (idx : Int) (j : Nat) (jlo jhi klo khi : Int),
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        intBounds (view.doms.getD j DomC.empty) = some (jlo, jhi) ∧
        intBounds (view.doms.getD k DomC.empty) = some (klo, khi) ∧
        jhi < klo ∧
        T.decodeClause ec.lits =
          [posNe i idx, negLe j jhi, posLe k (klo - 1)]) ∨
    (∃ (idx : Int) (j : Nat) (jlo jhi klo khi : Int),
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        intBounds (view.doms.getD j DomC.empty) = some (jlo, jhi) ∧
        intBounds (view.doms.getD k DomC.empty) = some (klo, khi) ∧
        khi < jlo ∧
        T.decodeClause ec.lits =
          [posNe i idx, negLe k khi, posLe j (jlo - 1)]) ∨
    (∃ (idx : Int) (j : Nat),
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        ((∃ w : Int, (view.doms.getD j DomC.empty).fixedValue = some (.int w) ∧
            (view.doms.getD k DomC.empty).memIntView w = false ∧
            T.decodeClause ec.lits = [posNe j w, posNe i idx, negNe k w]) ∨
         (∃ w : Int, (view.doms.getD k DomC.empty).fixedValue = some (.int w) ∧
            (view.doms.getD j DomC.empty).memIntView w = false ∧
            T.decodeClause ec.lits = [posNe k w, posNe i idx, negNe j w]))) := by
  dsimp only [arrayVarIntElementPropWith] at h
  split at h
  · cases h
  · rename_i ls hout
    injection h with hec
    subst hec
    have hout' : avieOut view.doms is i k = .conflict ls := by
      rw [← avieOutOfFA_getD_eq view.doms is i k]
      exact hout
    rcases avieOut_conflict_cases hout' with
      ⟨idx, hfix, hnone, rfl⟩ |
      ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, rfl⟩ |
      ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, rfl⟩ |
      ⟨idx, j, hfix, hent, hrest⟩
    · exact Or.inl ⟨idx, hfix, hnone, LitTable.decodeClause_map_pLit T _⟩
    · exact Or.inr (Or.inl
        ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt,
          LitTable.decodeClause_map_pLit T _⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt,
          LitTable.decodeClause_map_pLit T _⟩))
    · rcases hrest with ⟨w, hfw, hbad, rfl⟩ | ⟨w, hfw, hbad, rfl⟩
      · exact Or.inr (Or.inr (Or.inr
          ⟨idx, j, hfix, hent, Or.inl
            ⟨w, hfw, hbad, LitTable.decodeClause_map_pLit T _⟩⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨idx, j, hfix, hent, Or.inr
            ⟨w, hfw, hbad, LitTable.decodeClause_map_pLit T _⟩⟩))
  · cases h

theorem arrayVarIntElementPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  rcases arrayVarIntElementPropWith_run_conflict p T is i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ |
    ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, hdec⟩ |
    ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, hdec⟩ |
    ⟨idx, j, hfix, hent, hrest⟩
  · rw [hdec]
    exact avie_entailed_out p is i k hmem hnone
  · rw [hdec]
    exact avie_entailed_below p is i k hmem hent hlt
  · rw [hdec]
    exact avie_entailed_above p is i k hmem hent hlt
  · rcases hrest with ⟨w, hfw, hbad, hdec⟩ | ⟨w, hfw, hbad, hdec⟩
    · rw [hdec]
      exact avie_entailed_J p is i k hmem hent
    · rw [hdec]
      exact avie_entailed_K p is i k hmem hent

theorem arrayVarIntElementPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view
      (dcSlotsFull (.arrayVarIntElementSlot is i k)).toArray)
    {ec : EClause p T}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD l.atom.slot DomC.empty).evalLit l = some false := by
  have hWF' : ViewWF view (is ++ [i, k]).toArray := by
    simpa [dcSlotsFull] using hWF
  have hdi_wf : (view.doms.getD i DomC.empty).WF :=
    hWF'.dom_wf (s := i) (by simp)
  have hdk_wf : (view.doms.getD k DomC.empty).WF :=
    hWF'.dom_wf (s := k) (by simp)
  rcases arrayVarIntElementPropWith_run_conflict p T is i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ |
    ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, hdec⟩ |
    ⟨idx, j, jlo, jhi, klo, khi, hfix, hent, hbj, hbk, hlt, hdec⟩ |
    ⟨idx, j, hfix, hent, hrest⟩
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_singleton] at hl
    subst hl
    have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
      (DomC.fixedValue_sound _ hdi_wf hfix).1
    exact DomC.evalLit_posNe_of_fixed hfix hmem
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hl
    have hbj' := intBounds_some_iff.mp hbj
    have hbk' := intBounds_some_iff.mp hbk
    have hdj_wf : (view.doms.getD j DomC.empty).WF :=
      hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
    have hdjle : jlo ≤ jhi := DomC.lo?_le_hi? _ hdj_wf hbj'.1 hbj'.2
    have hdkle : klo ≤ khi := DomC.lo?_le_hi? _ hdk_wf hbk'.1 hbk'.2
    rcases hl with rfl | rfl | rfl
    · have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
        (DomC.fixedValue_sound _ hdi_wf hfix).1
      exact DomC.evalLit_posNe_of_fixed hfix hmem
    · simpa [negLe, Atom.slot] using
        evalLit_negLe_false_of_hi_le
          (d := view.doms.getD j DomC.empty)
          hbj'.1 hbj'.2 (Int.le_refl jhi) (by omega)
    · simpa [posLe, Atom.slot] using
        evalLit_posLe_false_of_lo_gt
          (d := view.doms.getD k DomC.empty)
          hbk'.1 hbk'.2 (by omega) (by omega)
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hl
    have hbj' := intBounds_some_iff.mp hbj
    have hbk' := intBounds_some_iff.mp hbk
    have hdj_wf : (view.doms.getD j DomC.empty).WF :=
      hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
    have hdjle : jlo ≤ jhi := DomC.lo?_le_hi? _ hdj_wf hbj'.1 hbj'.2
    have hdkle : klo ≤ khi := DomC.lo?_le_hi? _ hdk_wf hbk'.1 hbk'.2
    rcases hl with rfl | rfl | rfl
    · have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
        (DomC.fixedValue_sound _ hdi_wf hfix).1
      exact DomC.evalLit_posNe_of_fixed hfix hmem
    · simpa [negLe, Atom.slot] using
        evalLit_negLe_false_of_hi_le
          (d := view.doms.getD k DomC.empty)
          hbk'.1 hbk'.2 (Int.le_refl khi) (by omega)
    · simpa [posLe, Atom.slot] using
        evalLit_posLe_false_of_lo_gt
          (d := view.doms.getD j DomC.empty)
          hbj'.1 hbj'.2 (by omega) (by omega)
  · rcases hrest with ⟨w, hfw, hbad, hdec⟩ | ⟨w, hfw, hbad, hdec⟩
    · intro l hl
      rw [hdec] at hl
      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hl
      have hdj_wf : (view.doms.getD j DomC.empty).WF :=
        hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
      rcases hl with rfl | rfl | rfl
      · have hmem : (view.doms.getD j DomC.empty).mem (.int w) = true :=
          (DomC.fixedValue_sound _ hdj_wf hfw).1
        exact DomC.evalLit_posNe_of_fixed hfw hmem
      · have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
          (DomC.fixedValue_sound _ hdi_wf hfix).1
        exact DomC.evalLit_posNe_of_fixed hfix hmem
      · exact DomC.evalLit_negNe_false_of_not_memIntView
          (view.doms.getD k DomC.empty) k hbad
    · intro l hl
      rw [hdec] at hl
      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hl
      have hdj_wf : (view.doms.getD j DomC.empty).WF :=
        hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
      rcases hl with rfl | rfl | rfl
      · have hmem : (view.doms.getD k DomC.empty).mem (.int w) = true :=
          (DomC.fixedValue_sound _ hdk_wf hfw).1
        exact DomC.evalLit_posNe_of_fixed hfw hmem
      · have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
          (DomC.fixedValue_sound _ hdi_wf hfix).1
        exact DomC.evalLit_posNe_of_fixed hfix hmem
      · exact DomC.evalLit_negNe_false_of_not_memIntView
          (view.doms.getD j DomC.empty) j hbad

theorem arrayVarIntElementPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .prune ps) :
    ∃ (pairs : List (Literal × Clause)),
      pairs = aviePrunePairs view.doms is i k ∧
      ((∃ idx : Int,
          (view.doms.getD i DomC.empty).fixedValue = some (.int idx)) ∨
       (view.doms.getD i DomC.empty).fixedValue = none) ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        (l, reason) ∈ pairs ∧ q.1.lit = l ∧ T.decodeClause q.2.lits = reason) := by
  dsimp only [arrayVarIntElementPropWith] at h
  split at h
  · cases h
  · cases h
  · rename_i pairs hout
    injection h with hps
    subst hps
    have hout' : avieOut view.doms is i k = .prune pairs := by
      rw [← avieOutOfFA_getD_eq view.doms is i k]
      exact hout
    obtain ⟨hpairs, hsource⟩ := avieOut_prune_cases hout'
    exact ⟨pairs, hpairs, hsource,
      fun q hq => mkElemPruneArray_mem p T pairs _ hq⟩

theorem arrayVarIntElementPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayVarIntElementPropWith_run_prune p T is i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hdec]
  rw [hpairs] at hlr
  exact aviePrunePairs_entailed p is i k hmem view.doms hlr

theorem arrayVarIntElementPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarIntElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view
      (dcSlotsFull (.arrayVarIntElementSlot is i k)).toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarIntElementPropWith p T is i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayVarIntElementPropWith_run_prune p T is i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hpairs] at hlr
  have hsound := aviePrunePairs_eval p is i k hmem view hWF hlr
  refine ⟨?_, ?_⟩
  · rw [hlit]
    exact hsound.1
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hsound.2 q' hq' (by rwa [hlit] at hne)

/-! ### Malformed-input no-ops for the stage-2 decision -/

theorem avieOut_eq_fix_of_index_bounds_none {doms : Array DomC}
    {is : List Nat} {i k : Nat}
    (h : intBounds (doms.getD i DomC.empty) = none) :
    avieOut doms is i k = .fix := by
  unfold avieOut avieOutOf
  split
  · rename_i ilo ihi klo khi hbi hbk
    rw [h] at hbi
    simp at hbi
  · rfl

theorem avieOut_eq_fix_of_result_bounds_none {doms : Array DomC}
    {is : List Nat} {i k : Nat}
    (h : intBounds (doms.getD k DomC.empty) = none) :
    avieOut doms is i k = .fix := by
  unfold avieOut avieOutOf
  split
  · rename_i ilo ihi klo khi hbi hbk
    rw [h] at hbk
    simp at hbk
  · rfl

/-! ## Stage 3: the variable-table Boolean element -/

/-- A domain that is syntactically Boolean. -/
def boolOnlyB (d : DomC) : Bool :=
  match d with
  | .bool _ => true
  | _ => false

/-- The Boolean-table guard: the index is a usable integer slot, and the
result and every table slot are Boolean domains. -/
def avbeGuardB (doms : Array DomC) (is : List Nat) (i k : Nat) : Bool :=
  intSlotOkB (doms.getD i DomC.empty) &&
    (boolOnlyB (doms.getD k DomC.empty) &&
      is.all fun j => boolOnlyB (doms.getD j DomC.empty))

/-- Fixed-index Boolean prunes: when the result is fixed to `v`, remove
the opposite entry value; when the entry is fixed to `b`, remove the
opposite result value. -/
def avbeFixedPrunes (doms : Array DomC) (i k : Nat) (idx : Int) (j : Nat) :
    List (Literal × Clause) :=
  match (doms.getD k DomC.empty).fixedValue,
        (doms.getD j DomC.empty).fixedValue with
  | some (.bool v), none =>
      safePrunes (doms.getD j DomC.empty)
        [(posBool j v, [posNe i idx, posBool k (!v), posBool j v])]
  | none, some (.bool b) =>
      safePrunes (doms.getD k DomC.empty)
        [(posBool k b, [posNe i idx, posBool j (!b), posBool k b])]
  | _, _ => []

/-- The unsupported-index pair for a fixed selected Boolean slot: the
selected entry and the result are fixed to opposite Booleans. -/
def avbeBadIndexPair? (doms : Array DomC) (is : List Nat) (i k : Nat)
    (idx : Int) : Option (Literal × Clause) :=
  match avieEntry is idx with
  | none => some (posNe i idx, [posNe i idx])
  | some j =>
      match (doms.getD k DomC.empty).fixedValue,
            (doms.getD j DomC.empty).fixedValue with
      | some (.bool v), some (.bool b) =>
          if b == v then none
          else some (posNe i idx, [posNe i idx, posBool k (!v), posBool j v])
      | _, _ => none

/-- Unsupported index values in the Boolean general branch. -/
def avbeIndexPrunes (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di : DomC) : List (Literal × Clause) :=
  (intCandidates di).filterMap fun idx => avbeBadIndexPair? doms is i k idx

/-- The prune list selected by the Boolean decision. -/
def avbePrunePairs (doms : Array DomC) (is : List Nat) (i k : Nat) :
    List (Literal × Clause) :=
  let di := doms.getD i DomC.empty
  let dk := doms.getD k DomC.empty
  match intBounds di, intBounds dk with
  | some _, some _ =>
      if !avbeGuardB doms is i k then []
      else
        match di.fixedValue with
        | some (.int idx) =>
            match avieEntry is idx with
            | none => []
            | some j => avbeFixedPrunes doms i k idx j
        | some _ => []
        | none => safePrunes di (avbeIndexPrunes doms is i k di)
  | _, _ => []

inductive AvbeOut where
  | fix
  | conflict (ls : List Literal)
  | prune (pairs : List (Literal × Clause))

/-- The pure Boolean decision. -/
def avbeOut (doms : Array DomC) (is : List Nat) (i k : Nat) : AvbeOut :=
  let di := doms.getD i DomC.empty
  let dk := doms.getD k DomC.empty
  match intBounds di, intBounds dk with
  | some _, some _ =>
      if !avbeGuardB doms is i k then .fix
      else
        match di.fixedValue with
        | some (.int idx) =>
            match avieEntry is idx with
            | none => .conflict [posNe i idx]
            | some j =>
                let dj := doms.getD j DomC.empty
                match dk.fixedValue, dj.fixedValue with
                | some (.bool v), some (.bool b) =>
                    if b == v then .fix
                    else .conflict [posNe i idx, posBool k (!v), posBool j v]
                | some (.bool _), _ =>
                    let ps := avbePrunePairs doms is i k
                    if ps.isEmpty then .fix else .prune ps
                | none, some (.bool _) =>
                    let ps := avbePrunePairs doms is i k
                    if ps.isEmpty then .fix else .prune ps
                | _, _ => .fix
        | some _ => .fix
        | none =>
            let ps := avbePrunePairs doms is i k
            if ps.isEmpty then .fix else .prune ps
  | _, _ => .fix

/-! ### Array/runtime twins for the Boolean-table element

`avbeOut` and `avbePrunePairs` rescan the table `is` through `avieEntry`
for every candidate index and recompute the guard on every call.  The twins
hoist the table to an `Array`, the index/result bounds and fixed values, and
the guard.  They are installed in compiled code only by `@[csimp]`; every
proof keeps using the list-based definitions. -/

/-- `avbeBadIndexPair?` with the table hoisted to an array. -/
def avbeBadIndexPairFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (idx : Int) : Option (Literal × Clause) :=
  match avieEntryA isa idx with
  | none => some (posNe i idx, [posNe i idx])
  | some j =>
      match (doms.getD k DomC.empty).fixedValue,
            (doms.getD j DomC.empty).fixedValue with
      | some (.bool v), some (.bool b) =>
          if b == v then none
          else some (posNe i idx, [posNe i idx, posBool k (!v), posBool j v])
      | _, _ => none

theorem avbeBadIndexPairFA_eq (doms : Array DomC) (is : List Nat) (i k : Nat)
    (idx : Int) :
    avbeBadIndexPairFA doms is.toArray i k idx =
      avbeBadIndexPair? doms is i k idx := by
  unfold avbeBadIndexPairFA avbeBadIndexPair?
  rw [avieEntryA_eq]

/-- `avbeIndexPrunes` with the table hoisted to an array. -/
def avbeIndexPrunesFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (di : DomC) : List (Literal × Clause) :=
  (intCandidates di).filterMap fun idx => avbeBadIndexPairFA doms isa i k idx

theorem avbeIndexPrunesFA_eq (doms : Array DomC) (is : List Nat) (i k : Nat)
    (di : DomC) :
    avbeIndexPrunesFA doms is.toArray i k di =
      avbeIndexPrunes doms is i k di := by
  unfold avbeIndexPrunesFA avbeIndexPrunes
  congr 1
  funext idx
  exact avbeBadIndexPairFA_eq doms is i k idx

/-- `avbePrunePairs` with the table, guard and domains hoisted. -/
def avbePrunePairsFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (di dk : DomC) (g : Bool) : List (Literal × Clause) :=
  match intBounds di, intBounds dk with
  | some _, some _ =>
      if !g then []
      else
        match di.fixedValue with
        | some (.int idx) =>
            match avieEntryA isa idx with
            | none => []
            | some j => avbeFixedPrunes doms i k idx j
        | some _ => []
        | none => safePrunes di (avbeIndexPrunesFA doms isa i k di)
  | _, _ => []

theorem avbePrunePairsFA_eq (doms : Array DomC) (is : List Nat) (i k : Nat) :
    avbePrunePairsFA doms is.toArray i k (doms.getD i DomC.empty)
        (doms.getD k DomC.empty) (avbeGuardB doms is i k) =
      avbePrunePairs doms is i k := by
  unfold avbePrunePairsFA avbePrunePairs
  simp only [avieEntryA_eq, avbeIndexPrunesFA_eq]

/-- `avbeOut` with the table, guard, bounds and fixed values hoisted. -/
def avbeOutFA (doms : Array DomC) (isa : Array Nat) (i k : Nat)
    (di dk : DomC) (bi bk : Option (Int × Int))
    (fi fk : Option Value) (g : Bool) : AvbeOut :=
  match bi, bk with
  | some _, some _ =>
      if !g then .fix
      else
        match fi with
        | some (.int idx) =>
            match avieEntryA isa idx with
            | none => .conflict [posNe i idx]
            | some j =>
                let dj := doms.getD j DomC.empty
                match fk, dj.fixedValue with
                | some (.bool v), some (.bool b) =>
                    if b == v then .fix
                    else .conflict [posNe i idx, posBool k (!v), posBool j v]
                | some (.bool _), _ =>
                    let ps := avbePrunePairsFA doms isa i k di dk g
                    if ps.isEmpty then .fix else .prune ps
                | none, some (.bool _) =>
                    let ps := avbePrunePairsFA doms isa i k di dk g
                    if ps.isEmpty then .fix else .prune ps
                | _, _ => .fix
        | some _ => .fix
        | none =>
            let ps := avbePrunePairsFA doms isa i k di dk g
            if ps.isEmpty then .fix else .prune ps
  | _, _ => .fix

theorem avbeOutFA_eq (doms : Array DomC) (is : List Nat) (i k : Nat) :
    avbeOutFA doms is.toArray i k (doms.getD i DomC.empty)
        (doms.getD k DomC.empty) (intBounds (doms.getD i DomC.empty))
        (intBounds (doms.getD k DomC.empty))
        (doms.getD i DomC.empty).fixedValue
        (doms.getD k DomC.empty).fixedValue (avbeGuardB doms is i k) =
      avbeOut doms is i k := by
  unfold avbeOutFA avbeOut
  simp only [avieEntryA_eq, avbePrunePairsFA_eq]

/-- Runtime twin of `avbeOut` used by compiled code only. -/
def avbeOutFast (doms : Array DomC) (is : List Nat) (i k : Nat) : AvbeOut :=
  avbeOutFA doms is.toArray i k (doms.getD i DomC.empty)
    (doms.getD k DomC.empty) (intBounds (doms.getD i DomC.empty))
    (intBounds (doms.getD k DomC.empty))
    (doms.getD i DomC.empty).fixedValue
    (doms.getD k DomC.empty).fixedValue (avbeGuardB doms is i k)

theorem avbeOutFast_eq (doms : Array DomC) (is : List Nat) (i k : Nat) :
    avbeOutFast doms is i k = avbeOut doms is i k := by
  unfold avbeOutFast
  exact avbeOutFA_eq doms is i k

@[csimp] theorem avbeOut_eq_fast : @avbeOut = @avbeOutFast := by
  funext doms is i k
  exact (avbeOutFast_eq doms is i k).symm

/-! ### Stage-3 membership lemmas -/

theorem avbeFixedPrunes_mem {doms : Array DomC} {i k : Nat} {idx : Int}
    {j : Nat} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avbeFixedPrunes doms i k idx j) :
    (∃ v : Bool,
        (doms.getD k DomC.empty).fixedValue = some (.bool v) ∧
        (doms.getD j DomC.empty).fixedValue = none ∧
        l = posBool j v ∧
        reason = [posNe i idx, posBool k (!v), posBool j v]) ∨
    (∃ b : Bool,
        (doms.getD k DomC.empty).fixedValue = none ∧
        (doms.getD j DomC.empty).fixedValue = some (.bool b) ∧
        l = posBool k b ∧
        reason = [posNe i idx, posBool j (!b), posBool k b]) := by
  unfold avbeFixedPrunes at h
  split at h
  · rename_i v hfk hfjn
    have hp := safePrunes_mem h
    simp only [List.mem_singleton, Prod.mk.injEq] at hp
    exact Or.inl ⟨v, hfk, hfjn, hp.1, hp.2⟩
  · rename_i b hfkn hfjb
    have hp := safePrunes_mem h
    simp only [List.mem_singleton, Prod.mk.injEq] at hp
    exact Or.inr ⟨b, hfkn, hfjb, hp.1, hp.2⟩
  · simp at h

theorem avbeBadIndexPair?_mem {doms : Array DomC} {is : List Nat} {i k : Nat}
    {di : DomC} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avbeIndexPrunes doms is i k di) :
    ∃ idx : Int, idx ∈ intCandidates di ∧
      avbeBadIndexPair? doms is i k idx = some (l, reason) := by
  unfold avbeIndexPrunes at h
  rw [List.mem_filterMap] at h
  obtain ⟨idx, hidx, hf⟩ := h
  exact ⟨idx, hidx, hf⟩

theorem avbeBadIndexPair?_cases {doms : Array DomC} {is : List Nat}
    {i k : Nat} {idx : Int} {l : Literal} {reason : Clause}
    (hf : avbeBadIndexPair? doms is i k idx = some (l, reason)) :
    (avieEntry is idx = none ∧ l = posNe i idx ∧
        reason = [posNe i idx]) ∨
    (∃ j : Nat, ∃ v b : Bool,
        avieEntry is idx = some j ∧
        (doms.getD k DomC.empty).fixedValue = some (.bool v) ∧
        (doms.getD j DomC.empty).fixedValue = some (.bool b) ∧
        b ≠ v ∧ l = posNe i idx ∧
        reason = [posNe i idx, posBool k (!v), posBool j v]) := by
  unfold avbeBadIndexPair? at hf
  split at hf
  · rename_i hnone
    cases hf
    exact Or.inl ⟨hnone, rfl, rfl⟩
  · rename_i j hent
    split at hf
    · rename_i v b hfk hfj
      by_cases hbv : b == v
      · rw [if_pos hbv] at hf
        simp at hf
      · rw [if_neg hbv] at hf
        cases hf
        exact Or.inr ⟨j, v, b, hent, hfk, hfj,
          by simpa using hbv, rfl, rfl⟩
    · simp at hf

/-! ### Stage-3 entailment -/

theorem avbe_entailed_out (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    {idx : Int} (hnone : avieEntry is idx = none) :
    Entailed p [posNe i idx] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avbeResOut_entailed hs hnone

theorem avbe_entailed_pinVal (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {v : Bool} (he : avieEntry is idx = some j) :
    Entailed p [posNe i idx, posBool k (!v), posBool j v] := by
  intro b _ hacc
  have hs : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy b :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avbeResPinVal_entailed hs he

theorem avbe_entailed_single (p : CompiledProblem DomConstraint) (is : List Nat)
    (i k : Nat) (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    {idx : Int} {j : Nat} {b : Bool} (he : avieEntry is idx = some j) :
    Entailed p [posNe i idx, posBool j (!b), posBool k b] := by
  intro b' _ hacc
  have hs : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy b' :=
    (DomConstraint.satisfiedB_iff _ _).mp (accepts_satisfiedB hacc hmem)
  exact avbeResSingle_entailed hs he

theorem avbeBadIndexPair?_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    {idx : Int} {l : Literal} {reason : Clause}
    (hf : avbeBadIndexPair? doms is i k idx = some (l, reason)) :
    Entailed p reason := by
  rcases avbeBadIndexPair?_cases hf with
    ⟨hnone, rfl, rfl⟩ | ⟨j, v, b, hent, hfk, hfj, hne, rfl, rfl⟩
  · exact avbe_entailed_out p is i k hmem hnone
  · exact avbe_entailed_pinVal p is i k hmem hent

theorem avbePrunePairs_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (doms : Array DomC) {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avbePrunePairs doms is i k) : Entailed p reason := by
  unfold avbePrunePairs at h
  dsimp only at h
  split at h
  · rename_i hbi hbk
    split at h
    · simp at h
    · rename_i hguard
      split at h
      · rename_i idx hfix
        split at h
        · simp at h
        · rename_i j hent
          rcases avbeFixedPrunes_mem h with
            ⟨v, hfk, hfjn, rfl, rfl⟩ | ⟨b, hfkn, hfjb, rfl, rfl⟩
          · exact avbe_entailed_pinVal p is i k hmem hent
          · exact avbe_entailed_single p is i k hmem hent
      · simp at h
      · rcases avbeBadIndexPair?_mem (safePrunes_mem h) with ⟨idx, hidx, hf⟩
        exact avbeBadIndexPair?_entailed p is i k hmem hf
  · simp at h

/-! ### Stage-3 evaluation of the pure prune lists -/

theorem avbePrunePairs_eval (p : CompiledProblem DomConstraint)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view (dcSlotsFull (.arrayVarBoolElementSlot is i k)).toArray)
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ avbePrunePairs view.doms is i k) :
    (view.doms.getD l.atom.slot DomC.empty).evalLit l = none ∧
      ∀ q ∈ reason, q ≠ l →
        (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false := by
  have hWF' : ViewWF view (is ++ [i, k]).toArray := by
    simpa [dcSlotsFull] using hWF
  have hdi_wf : (view.doms.getD i DomC.empty).WF :=
    hWF'.dom_wf (s := i) (by simp)
  unfold avbePrunePairs at h
  dsimp only at h
  split at h
  · rename_i hbi hbk
    split at h
    · simp at h
    · rename_i hguard
      split at h
      · rename_i idx hfix
        split at h
        · simp at h
        · rename_i j hent
          have hdi_mem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
            (DomC.fixedValue_sound _ hdi_wf hfix).1
          have hipos : (view.doms.getD i DomC.empty).evalLit (posNe i idx) = some false :=
            DomC.evalLit_posNe_of_fixed hfix hdi_mem
          rcases avbeFixedPrunes_mem h with
            ⟨v, hfk, hfjn, rfl, rfl⟩ |
            ⟨b, hfkn, hfjb, rfl, rfl⟩
          · have hpivot : (view.doms.getD j DomC.empty).evalLit (posBool j v) = none :=
              DomC.evalLit_posBool_none_of_not_fixed hfjn
            refine ⟨hpivot, ?_⟩
            intro q hq hne
            rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · simpa [posNe, Atom.slot] using hipos
            · simpa [posBool, Atom.slot] using
                DomC.evalLit_posBool_false_of_fixed_other hfk (by cases v <;> simp)
            · exact absurd rfl hne
          · have hpivot : (view.doms.getD k DomC.empty).evalLit (posBool k b) = none :=
              DomC.evalLit_posBool_none_of_not_fixed hfkn
            refine ⟨hpivot, ?_⟩
            intro q hq hne
            rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · simpa [posNe, Atom.slot] using hipos
            · simpa [posBool, Atom.slot] using
                DomC.evalLit_posBool_false_of_fixed_other hfjb (by cases b <;> simp)
            · exact absurd rfl hne
      · simp at h
      · rename_i hfixnone
        rcases avbeBadIndexPair?_mem (safePrunes_mem h) with ⟨idx, hidx, hf⟩
        have hdix : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
          mem_intCandidates hidx
        have hipos : (view.doms.getD i DomC.empty).evalLit (posNe i idx) = none := by
          have := DomC.evalLit_neLit_none_of_not_fixed
            (d := view.doms.getD i DomC.empty) (s := i) (v := .int idx) hfixnone hdix
          simpa [neLit] using this
        rcases avbeBadIndexPair?_cases hf with
          ⟨hnone, rfl, rfl⟩ |
          ⟨j, v, b, hent, hfk, hfj, hne, rfl, rfl⟩
        · refine ⟨hipos, ?_⟩
          intro q hq hne
          rw [List.mem_singleton] at hq
          subst hq
          exact absurd rfl hne
        · refine ⟨hipos, ?_⟩
          intro q hq hne
          rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · exact absurd rfl hne
          · simpa [posBool, Atom.slot] using
              DomC.evalLit_posBool_false_of_fixed_other hfk (by cases v <;> simp)
          · simpa [posBool, Atom.slot] using
              DomC.evalLit_posBool_false_of_fixed_other hfj (by
                cases b <;> cases v <;> simp_all)
  · simp at h

/-! ### Stage-3 decision analysis -/

theorem avbeOut_conflict_cases {doms : Array DomC} {is : List Nat} {i k : Nat}
    {ls : List Literal} (h : avbeOut doms is i k = .conflict ls) :
    (∃ idx : Int, (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = none ∧ ls = [posNe i idx]) ∨
    (∃ (idx : Int) (j : Nat) (v b : Bool),
        (doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        (doms.getD k DomC.empty).fixedValue = some (.bool v) ∧
        (doms.getD j DomC.empty).fixedValue = some (.bool b) ∧
        b ≠ v ∧ ls = [posNe i idx, posBool k (!v), posBool j v]) := by
  unfold avbeOut at h
  dsimp only at h
  split at h
  · rename_i hbi hbk
    split at h
    · cases h
    · split at h
      · rename_i idx hfix
        split at h
        · rename_i hnone
          cases h
          exact Or.inl ⟨idx, hfix, hnone, rfl⟩
        · rename_i j hent
          split at h
          · rename_i v b hfk hfj
            by_cases hbv : b == v
            · rw [if_pos hbv] at h
              cases h
            · rw [if_neg hbv] at h
              cases h
              exact Or.inr ⟨idx, j, v, b, hfix, hent, hfk, hfj,
                by simpa using hbv, rfl⟩
          · split at h
            · cases h
            · cases h
          · split at h
            · cases h
            · cases h
          · cases h
      · cases h
      · split at h
        · cases h
        · cases h
  · cases h

theorem avbeOut_prune_cases {doms : Array DomC} {is : List Nat} {i k : Nat}
    {pairs : List (Literal × Clause)}
    (h : avbeOut doms is i k = .prune pairs) :
    pairs = avbePrunePairs doms is i k ∧
      ((∃ idx : Int, (doms.getD i DomC.empty).fixedValue = some (.int idx)) ∨
       (doms.getD i DomC.empty).fixedValue = none) := by
  unfold avbeOut at h
  dsimp only at h
  split at h
  · rename_i hbi hbk
    split at h
    · cases h
    · split at h
      · rename_i idx hfix
        split at h
        · cases h
        · rename_i j hent
          split at h
          · rename_i v b hfk hfj
            by_cases hbv : b == v
            · rw [if_pos hbv] at h
              cases h
            · rw [if_neg hbv] at h
              cases h
          · split at h
            · cases h
            · injection h with hp
              exact ⟨hp.symm, Or.inl ⟨idx, hfix⟩⟩
          · split at h
            · cases h
            · injection h with hp
              exact ⟨hp.symm, Or.inl ⟨idx, hfix⟩⟩
          · cases h
      · cases h
      · rename_i hfixnone
        split at h
        · cases h
        · injection h with hp
          exact ⟨hp.symm, Or.inr hfixnone⟩
  · cases h

/-! ### The stage-3 builder -/

/-- The variable-table Boolean element propagator. -/
def arrayVarBoolElementPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints) : PropV2 p T :=
  let isa := is.toArray
  { vars := (dcSlotsFull (.arrayVarBoolElementSlot is i k)).toArray
    events := ((is.map fun j => (j, EventKind.fix)) ++
      [(i, EventKind.bounds), (i, EventKind.fix), (k, EventKind.fix)]).toArray
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dk := view.doms.getD k DomC.empty
      match hout : avbeOutFA view.doms isa i k di dk
          (intBounds di) (intBounds dk) di.fixedValue dk.fixedValue
          (avbeGuardB view.doms is i k) with
      | .fix => .fix
      | .conflict ls =>
          .conflict (EClause.ofLiterals p T ls (by
            have hout' : avbeOut view.doms is i k = .conflict ls := by
              rw [← avbeOutFA_eq view.doms is i k]
              exact hout
            rcases avbeOut_conflict_cases hout' with
              ⟨idx, hfix, hnone, rfl⟩ |
              ⟨idx, j, v, b, hfix, hent, hfk, hfj, hne, rfl⟩
            · exact avbe_entailed_out p is i k hmem hnone
            · exact avbe_entailed_pinVal p is i k hmem hent))
      | .prune pairs =>
          .prune (mkElemPruneArray p T pairs
            (fun l reason hlr =>
              avbePrunePairs_entailed p is i k hmem view.doms (by
                have hout' : avbeOut view.doms is i k = .prune pairs := by
                  rw [← avbeOutFA_eq view.doms is i k]
                  exact hout
                have hp := (avbeOut_prune_cases hout').1
                rwa [hp] at hlr))) }

theorem arrayVarBoolElementPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .conflict ec) :
    (∃ idx : Int,
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = none ∧
        T.decodeClause ec.lits = [posNe i idx]) ∨
    (∃ (idx : Int) (j : Nat) (v b : Bool),
        (view.doms.getD i DomC.empty).fixedValue = some (.int idx) ∧
        avieEntry is idx = some j ∧
        (view.doms.getD k DomC.empty).fixedValue = some (.bool v) ∧
        (view.doms.getD j DomC.empty).fixedValue = some (.bool b) ∧
        b ≠ v ∧
        T.decodeClause ec.lits =
          [posNe i idx, posBool k (!v), posBool j v]) := by
  dsimp only [arrayVarBoolElementPropWith] at h
  split at h
  · cases h
  · rename_i ls hout
    injection h with hec
    subst hec
    have hout' : avbeOut view.doms is i k = .conflict ls := by
      rw [← avbeOutFA_eq view.doms is i k]
      exact hout
    rcases avbeOut_conflict_cases hout' with
      ⟨idx, hfix, hnone, rfl⟩ |
      ⟨idx, j, v, b, hfix, hent, hfk, hfj, hne, rfl⟩
    · exact Or.inl ⟨idx, hfix, hnone, LitTable.decodeClause_map_pLit T _⟩
    · exact Or.inr ⟨idx, j, v, b, hfix, hent, hfk, hfj, hne,
        LitTable.decodeClause_map_pLit T _⟩
  · cases h

theorem arrayVarBoolElementPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ec : EClause p T}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  rcases arrayVarBoolElementPropWith_run_conflict p T is i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ |
    ⟨idx, j, v, b, hfix, hent, hfk, hfj, hne, hdec⟩
  · rw [hdec]
    exact avbe_entailed_out p is i k hmem hnone
  · rw [hdec]
    exact avbe_entailed_pinVal p is i k hmem hent

theorem arrayVarBoolElementPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view
      (dcSlotsFull (.arrayVarBoolElementSlot is i k)).toArray)
    {ec : EClause p T}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD l.atom.slot DomC.empty).evalLit l = some false := by
  have hWF' : ViewWF view (is ++ [i, k]).toArray := by
    simpa [dcSlotsFull] using hWF
  have hdi_wf : (view.doms.getD i DomC.empty).WF :=
    hWF'.dom_wf (s := i) (by simp)
  rcases arrayVarBoolElementPropWith_run_conflict p T is i k hmem view h with
    ⟨idx, hfix, hnone, hdec⟩ |
    ⟨idx, j, v, b, hfix, hent, hfk, hfj, hne, hdec⟩
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_singleton] at hl
    subst hl
    have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
      (DomC.fixedValue_sound _ hdi_wf hfix).1
    exact DomC.evalLit_posNe_of_fixed hfix hmem
  · intro l hl
    rw [hdec] at hl
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hl
    have hdj_wf : (view.doms.getD j DomC.empty).WF :=
      hWF'.dom_wf (s := j) (by simp [avieEntry_mem hent])
    rcases hl with rfl | rfl | rfl
    · have hmem : (view.doms.getD i DomC.empty).mem (.int idx) = true :=
        (DomC.fixedValue_sound _ hdi_wf hfix).1
      exact DomC.evalLit_posNe_of_fixed hfix hmem
    · simpa [posBool, Atom.slot] using
        DomC.evalLit_posBool_false_of_fixed_other hfk (by cases v <;> simp)
    · simpa [posBool, Atom.slot] using
        DomC.evalLit_posBool_false_of_fixed_other hfj hne

theorem arrayVarBoolElementPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .prune ps) :
    ∃ (pairs : List (Literal × Clause)),
      pairs = avbePrunePairs view.doms is i k ∧
      ((∃ idx : Int,
          (view.doms.getD i DomC.empty).fixedValue = some (.int idx)) ∨
       (view.doms.getD i DomC.empty).fixedValue = none) ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        (l, reason) ∈ pairs ∧ q.1.lit = l ∧ T.decodeClause q.2.lits = reason) := by
  dsimp only [arrayVarBoolElementPropWith] at h
  split at h
  · cases h
  · cases h
  · rename_i pairs hout
    injection h with hps
    subst hps
    have hout' : avbeOut view.doms is i k = .prune pairs := by
      rw [← avbeOutFA_eq view.doms is i k]
      exact hout
    obtain ⟨hpairs, hsource⟩ := avbeOut_prune_cases hout'
    exact ⟨pairs, hpairs, hsource,
      fun q hq => mkElemPruneArray_mem p T pairs _ hq⟩

theorem arrayVarBoolElementPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayVarBoolElementPropWith_run_prune p T is i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hdec]
  rw [hpairs] at hlr
  exact avbePrunePairs_entailed p is i k hmem view.doms hlr

theorem arrayVarBoolElementPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (hWF : ViewWF view
      (dcSlotsFull (.arrayVarBoolElementSlot is i k)).toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (arrayVarBoolElementPropWith p T is i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD q.1.lit.atom.slot DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD q'.atom.slot DomC.empty).evalLit q' = some false := by
  obtain ⟨pairs, hpairs, hsource, hmemq⟩ :=
    arrayVarBoolElementPropWith_run_prune p T is i k hmem view h
  obtain ⟨l, reason, hlr, hlit, hdec⟩ := hmemq q hq
  rw [hpairs] at hlr
  have hsound := avbePrunePairs_eval p is i k hmem view hWF hlr
  refine ⟨?_, ?_⟩
  · rw [hlit]
    exact hsound.1
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hsound.2 q' hq' (by rwa [hlit] at hne)

/-! ### Malformed-input no-ops for the stage-3 decision -/

theorem avbeOut_eq_fix_of_index_bounds_none {doms : Array DomC}
    {is : List Nat} {i k : Nat}
    (h : intBounds (doms.getD i DomC.empty) = none) :
    avbeOut doms is i k = .fix := by
  unfold avbeOut
  dsimp only
  split
  · rename_i hbi hbk
    rw [h] at hbi
    simp at hbi
  · rfl

theorem avbeOut_eq_fix_of_result_bounds_none {doms : Array DomC}
    {is : List Nat} {i k : Nat}
    (h : intBounds (doms.getD k DomC.empty) = none) :
    avbeOut doms is i k = .fix := by
  unfold avbeOut
  dsimp only
  split
  · rename_i hbi hbk
    rw [h] at hbk
    simp at hbk
  · rfl

theorem avbeOut_eq_fix_of_guard_false {doms : Array DomC}
    {is : List Nat} {i k : Nat}
    (h : avbeGuardB doms is i k = false) :
    avbeOut doms is i k = .fix := by
  unfold avbeOut
  dsimp only
  split
  · split
    · rfl
    · rename_i hc
      simp [h] at hc
  · rfl

/-- Malformed input for the stage-3 propagator: unusable index or result
bounds, or a non-Boolean index/result/table slot, all yield a no-op. -/
theorem arrayVarBoolElementPropWith_run_fix_of_malformed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (i k : Nat)
    (hmem : DomConstraint.arrayVarBoolElementSlot is i k ∈ p.constraints)
    (view : EngineView)
    (h : intBounds (view.doms.getD i DomC.empty) = none ∨
      intBounds (view.doms.getD k DomC.empty) = none ∨
      avbeGuardB view.doms is i k = false) :
    (arrayVarBoolElementPropWith p T is i k hmem).run view = .fix := by
  have ha : avbeOut view.doms is i k = .fix := by
    rcases h with h | h | h
    · exact avbeOut_eq_fix_of_index_bounds_none h
    · exact avbeOut_eq_fix_of_result_bounds_none h
    · exact avbeOut_eq_fix_of_guard_false h
  dsimp only [arrayVarBoolElementPropWith]
  split
  · rfl
  · rename_i ls hout
    have hout' : avbeOut view.doms is i k = .conflict ls := by
      rw [← avbeOutFA_eq view.doms is i k]
      exact hout
    exact absurd hout' (by rw [ha]; simp)
  · rename_i pairs hout
    have hout' : avbeOut view.doms is i k = .prune pairs := by
      rw [← avbeOutFA_eq view.doms is i k]
      exact hout
    exact absurd hout' (by rw [ha]; simp)

end LeanFzn.Engine

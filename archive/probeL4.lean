/-
File: probeL4.lean

Purpose:
  Scratch file for `splitOnAux` step lemmas related to the
  `String.splitOn`/`intercalate` round-trip law (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution modules).

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn -> probeL4.lean (standalone, no dependents)
-/

import LeanFzn
open LeanFzn LeanFzn.Lexer LeanFzn.Solution

def PosR (n : Nat) : String.Pos.Raw := { byteIdx := n }
def prefSize (cs : List Char) : Nat := (cs.map Char.utf8Size).sum

theorem utf8ByteSize_eq_prefSize' (s : String) : s.utf8ByteSize = prefSize s.toList := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  induction l with
  | nil => rfl
  | cons c l ih =>
      have hsplit : String.ofList (c :: l) = String.ofList [c] ++ String.ofList l := by
        rw [← List.singleton_append, String.ofList_append]
      have h1 : (String.ofList [c]).utf8ByteSize = c.utf8Size := by
        rw [show String.ofList [c] = String.singleton c from String.singleton_eq_ofList.symm,
          String.utf8ByteSize_singleton]
      have h2 : (String.ofList [c]).toList = [c] := String.toList_ofList
      rw [hsplit, String.utf8ByteSize_append, h1, ih, String.toList_append, h2,
        String.toList_ofList]
      show c.utf8Size + prefSize l = prefSize ([c] ++ l)
      rw [List.cons_append, List.nil_append]
      rfl

theorem prefSize_append (l1 l2 : List Char) :
    prefSize (l1 ++ l2) = prefSize l1 + prefSize l2 := by
  simp only [prefSize, List.map_append, List.sum_append]

theorem prefSize_cons (p : Char) (cs : List Char) :
    prefSize (p :: cs) = p.utf8Size + prefSize cs := rfl

theorem posR_cases (p : String.Pos.Raw) : p = PosR p.byteIdx := by
  cases p; rfl

theorem posR_add_char (n : Nat) (c : Char) : PosR n + c = PosR (n + c.utf8Size) := by
  show { byteIdx := n + c.utf8Size } = PosR (n + c.utf8Size)
  rfl

theorem prefSize_pos (c : Char) (cs : List Char) : 0 < prefSize (c :: cs) := by
  show 0 < c.utf8Size + prefSize cs
  have := c.utf8Size_pos
  omega

theorem utf8GetAux_at' : ∀ (pre post : List Char) (c : Char) (cs : List Char)
    (_hcs : cs = pre ++ (c :: post)) (start : String.Pos.Raw),
    String.Pos.Raw.utf8GetAux cs start (PosR (start.byteIdx + prefSize pre)) = c := by
  intro pre
  induction pre with
  | nil =>
      intro post c cs _hcs start
      subst _hcs
      rw [posR_cases start, show (PosR start.byteIdx).byteIdx = start.byteIdx from rfl]
      show String.Pos.Raw.utf8GetAux (c :: post) (PosR start.byteIdx)
          (PosR (start.byteIdx + prefSize ([] : List Char))) = c
      rw [show prefSize ([] : List Char) = 0 from rfl, Nat.add_zero, posR_cases (PosR start.byteIdx),
        show (PosR (PosR start.byteIdx).byteIdx) = PosR start.byteIdx from rfl,
        String.Pos.Raw.utf8GetAux.eq_2]
      simp
  | cons p pre' ih =>
      intro post c cs _hcs start
      subst _hcs
      have hne : ¬ (start = PosR (start.byteIdx + prefSize (p :: pre'))) := by
        intro h
        have h2 : PosR start.byteIdx = PosR (start.byteIdx + prefSize (p :: pre')) := by
          rw [← posR_cases start]; exact h
        injection h2 with h0
        have : 0 < prefSize (p :: pre') := by
          show 0 < p.utf8Size + prefSize pre'
          have := p.utf8Size_pos
          omega
        omega
      show String.Pos.Raw.utf8GetAux (p :: (pre' ++ c :: post)) start
          (PosR (start.byteIdx + prefSize (p :: pre'))) = c
      rw [String.Pos.Raw.utf8GetAux.eq_2 start (PosR (start.byteIdx + prefSize (p :: pre'))) p
        (pre' ++ c :: post), if_neg hne,
        show start + p = PosR (start.byteIdx + p.utf8Size) from posR_cases start ▸
          (show (PosR start.byteIdx) + p = PosR (start.byteIdx + p.utf8Size) from by
            show { byteIdx := start.byteIdx + p.utf8Size } = PosR (start.byteIdx + p.utf8Size)
            rfl)]
      show String.Pos.Raw.utf8GetAux (pre' ++ c :: post) (PosR (start.byteIdx + p.utf8Size))
          (PosR (start.byteIdx + (p.utf8Size + prefSize pre'))) = c
      have h1 : start.byteIdx + (p.utf8Size + prefSize pre')
          = (start.byteIdx + p.utf8Size) + prefSize pre' := by omega
      rw [h1]
      exact ih post c (pre' ++ c :: post) rfl (PosR (start.byteIdx + p.utf8Size))

theorem pos_get_head' (s : String) (pre post : List Char) (c : Char)
    (hcs : s.toList = pre ++ (c :: post)) :
    (PosR (prefSize pre)).get s = c := by
  show String.Pos.Raw.utf8GetAux s.toList (PosR 0) (PosR (prefSize pre)) = c
  have := utf8GetAux_at' pre post c s.toList hcs (PosR 0)
  rw [show (PosR 0).byteIdx = 0 from rfl, Nat.zero_add] at this
  exact this

/-- One step of `splitOnAux` at a matching position: the scan at the
    separator character `c` emits the segment before it and restarts
    just past it. -/
theorem splitOnAux_step (s : String) (pre0 pre post : List Char) (c : Char) (r : List String)
    (hcs : s.toList = pre0 ++ pre ++ (c :: post)) :
    String.splitOnAux s (String.singleton c) (PosR (prefSize pre0))
      (PosR (prefSize pre0 + prefSize pre)) (PosR 0) r
      = String.splitOnAux s (String.singleton c)
          (PosR (prefSize pre0 + prefSize pre + c.utf8Size))
          (PosR (prefSize pre0 + prefSize pre + c.utf8Size)) (PosR 0)
          (((PosR (prefSize pre0)).extract s (PosR (prefSize pre0 + prefSize pre))) :: r) := by
  rw [String.splitOnAux]
  have hsz : s.utf8ByteSize = prefSize (pre0 ++ pre ++ c :: post) := by
    have := utf8ByteSize_eq_prefSize' s
    rw [hcs] at this
    exact this
  have hlt : (String.Pos.Raw.atEnd s (PosR (prefSize pre0 + prefSize pre))) = false := by
    show decide (prefSize pre0 + prefSize pre ≥ s.utf8ByteSize) = false
    rw [hsz]
    show decide (prefSize pre0 + prefSize pre ≥ prefSize (pre0 ++ pre ++ c :: post)) = false
    rw [prefSize_append (pre0 ++ pre) (c :: post), prefSize_append pre0 pre, prefSize_cons]
    have hc : 0 < c.utf8Size := c.utf8Size_pos
    have hpp : 0 ≤ prefSize post := Nat.zero_le _
    have hlt' : ¬ (prefSize pre0 + prefSize pre
        ≥ prefSize pre0 + prefSize pre + (c.utf8Size + prefSize post)) := by omega
    simp only [hlt', decide_false]
  rw [if_neg (by rw [hlt]; simp)]
  -- the characters match
  have hsuf : s.toList = (pre0 ++ pre) ++ (c :: post) := by rw [hcs, List.append_assoc]
  have hget : (PosR (prefSize (pre0 ++ pre))).get s = c :=
    pos_get_head' s (pre0 ++ pre) post c hsuf
  have hget' : (PosR (prefSize pre0 + prefSize pre)).get s = c := by
    rw [show PosR (prefSize pre0 + prefSize pre) = PosR (prefSize (pre0 ++ pre)) from by
      rw [prefSize_append pre0 pre]]
    exact hget
  have hcsep : (PosR 0).get (String.singleton c) = c := by
    show String.Pos.Raw.utf8GetAux (String.singleton c).toList (PosR 0) (PosR 0) = c
    rw [show (String.singleton c).toList = [c] from by
      rw [show String.singleton c = String.ofList [c] from String.singleton_eq_ofList,
        String.toList_ofList]]
    rfl
  rw [hget', hcsep]
  show (if (c == c) = true then _ else _) = _
  simp only [beq_self_eq_true, if_true]
  -- i := next; j := next 0; atEnd sep j = true
  have hnext : (PosR (prefSize pre0 + prefSize pre)).next s
      = PosR (prefSize pre0 + prefSize pre + c.utf8Size) := by
    show { byteIdx := prefSize pre0 + prefSize pre + (String.Pos.Raw.get s (PosR (prefSize pre0 + prefSize pre))).utf8Size }
      = PosR (prefSize pre0 + prefSize pre + c.utf8Size)
    rw [hget']
    rfl
  have hnext0 : (PosR 0).next (String.singleton c) = PosR c.utf8Size := by
    show { byteIdx := 0 + ((PosR 0).get (String.singleton c)).utf8Size } = PosR c.utf8Size
    rw [hcsep]
    show { byteIdx := 0 + c.utf8Size } = PosR c.utf8Size
    rw [Nat.zero_add]
    rfl
  have hatEnd : (String.Pos.Raw.atEnd (String.singleton c) (PosR c.utf8Size)) = true := by
    show decide (c.utf8Size ≥ (String.singleton c).utf8ByteSize) = true
    rw [String.utf8ByteSize_singleton]
    simp
  rw [hnext, hnext0, hatEnd]
  show (if true = true then _ else _) = _
  simp only [if_true]
  -- i.unoffsetBy j = PosR (prefSize pre0 + prefSize pre)
  show s.splitOnAux (String.singleton c) (PosR (prefSize pre0 + prefSize pre + c.utf8Size))
      (PosR (prefSize pre0 + prefSize pre + c.utf8Size)) (PosR 0)
      (String.Pos.Raw.extract s (PosR (prefSize pre0))
        ((PosR (prefSize pre0 + prefSize pre + c.utf8Size)).unoffsetBy (PosR c.utf8Size)) :: r) = _
  show s.splitOnAux (String.singleton c) (PosR (prefSize pre0 + prefSize pre + c.utf8Size))
      (PosR (prefSize pre0 + prefSize pre + c.utf8Size)) (PosR 0)
      (String.Pos.Raw.extract s (PosR (prefSize pre0))
        ((PosR (prefSize pre0 + prefSize pre + c.utf8Size)).unoffsetBy (PosR c.utf8Size)) :: r) = _
  have hun : (PosR (prefSize pre0 + prefSize pre + c.utf8Size)).unoffsetBy (PosR c.utf8Size)
      = PosR (prefSize pre0 + prefSize pre) := by
    show { byteIdx := prefSize pre0 + prefSize pre + c.utf8Size - c.utf8Size }
      = PosR (prefSize pre0 + prefSize pre)
    congr 1
    omega
  rw [hun]

/-- One step of `splitOnAux` at a non-matching character: the scan
    advances past one character of the segment. -/
theorem splitOnAux_step_nomatch (s : String) (pre0 pre post : List Char) (c d : Char)
    (r : List String) (hcs : s.toList = pre0 ++ pre ++ (d :: post))
    (hd : d ≠ c) :
    String.splitOnAux s (String.singleton c) (PosR (prefSize pre0))
      (PosR (prefSize pre0 + prefSize pre)) (PosR 0) r
      = String.splitOnAux s (String.singleton c) (PosR (prefSize pre0))
          (PosR (prefSize pre0 + prefSize pre + d.utf8Size)) (PosR 0) r := by
  rw [String.splitOnAux]
  have hsz : s.utf8ByteSize = prefSize (pre0 ++ pre ++ d :: post) := by
    have := utf8ByteSize_eq_prefSize' s
    rw [hcs] at this
    exact this
  have hlt : (String.Pos.Raw.atEnd s (PosR (prefSize pre0 + prefSize pre))) = false := by
    show decide (prefSize pre0 + prefSize pre ≥ s.utf8ByteSize) = false
    rw [hsz]
    show decide (prefSize pre0 + prefSize pre
        ≥ prefSize (pre0 ++ pre ++ d :: post)) = false
    rw [show pre0 ++ pre ++ d :: post = (pre0 ++ pre) ++ (d :: post) from by
      rw [List.append_assoc],
      prefSize_append (pre0 ++ pre) (d :: post), prefSize_cons, prefSize_append pre0 pre]
    have hc : 0 < d.utf8Size := d.utf8Size_pos
    have hpp : 0 ≤ prefSize post := Nat.zero_le _
    have hlt' : ¬ (prefSize pre0 + prefSize pre
        ≥ prefSize pre0 + prefSize pre + (d.utf8Size + prefSize post)) := by omega
    simp only [show decide (prefSize pre0 + prefSize pre
        ≥ prefSize pre0 + prefSize pre + (d.utf8Size + prefSize post)) = false from
      by simp [hlt']]
  rw [if_neg (by rw [hlt]; exact Bool.noConfusion)]
  -- characters differ
  have hget' : (PosR (prefSize pre0 + prefSize pre)).get s = d := by
    have hsuf : s.toList = (pre0 ++ pre) ++ (d :: post) := by rw [hcs, List.append_assoc]
    rw [show PosR (prefSize pre0 + prefSize pre) = PosR (prefSize (pre0 ++ pre)) from by
      rw [prefSize_append pre0 pre]]
    exact pos_get_head' s (pre0 ++ pre) post d hsuf
  have hcsep : (PosR 0).get (String.singleton c) = c := by
    show String.Pos.Raw.utf8GetAux (String.singleton c).toList (PosR 0) (PosR 0) = c
    rw [show (String.singleton c).toList = [c] from by
      rw [show String.singleton c = String.ofList [c] from String.singleton_eq_ofList,
        String.toList_ofList]]
    rfl
  rw [hget', hcsep]
  show (if (d == c) = true then _ else _) = _
  have hdf : (d == c) = false := by
    have : (d == c) = decide (d = c) := rfl
    rw [this]
    simp [hd]
  rw [hdf]
  show s.splitOnAux (String.singleton c) (PosR (prefSize pre0))
      (String.Pos.Raw.next s ((PosR (prefSize pre0 + prefSize pre)).unoffsetBy (PosR 0))) (PosR 0) r = _
  rw [show (PosR (prefSize pre0 + prefSize pre)).unoffsetBy (PosR 0)
      = PosR (prefSize pre0 + prefSize pre) from rfl]
  have hnext : (PosR (prefSize pre0 + prefSize pre)).next s
      = PosR (prefSize pre0 + prefSize pre + d.utf8Size) := by
    show { byteIdx := prefSize pre0 + prefSize pre
        + (String.Pos.Raw.get s (PosR (prefSize pre0 + prefSize pre))).utf8Size }
      = PosR (prefSize pre0 + prefSize pre + d.utf8Size)
    rw [hget']
    rfl
  rw [hnext]

/-- The terminal step of `splitOnAux`: at the end of the string the
    last segment is emitted and the accumulator reversed. -/
theorem splitOnAux_end (s : String) (pre0 pre : List Char) (c : Char) (r : List String)
    (hcs : s.toList = pre0 ++ pre) :
    String.splitOnAux s (String.singleton c) (PosR (prefSize pre0))
        (PosR (prefSize pre0 + prefSize pre)) (PosR 0) r
      = (((PosR (prefSize pre0)).extract s (PosR (prefSize pre0 + prefSize pre))) :: r).reverse := by
  rw [String.splitOnAux]
  have hsz : s.utf8ByteSize = prefSize (pre0 ++ pre) := by
    have := utf8ByteSize_eq_prefSize' s
    rw [hcs] at this
    exact this
  have hlt : (String.Pos.Raw.atEnd s (PosR (prefSize pre0 + prefSize pre))) = true := by
    show decide (prefSize pre0 + prefSize pre ≥ s.utf8ByteSize) = true
    rw [hsz, prefSize_append pre0 pre]
    simp only [Nat.le_refl, decide_eq_true]
  rw [hlt]
  simp only [if_true]

/-! ### Extracting between prefix boundaries -/

/-- `extract.go₂` collects the characters between two prefix
    boundaries. -/
theorem extractGo₂ : ∀ (mid post : List Char) (start : String.Pos.Raw),
    String.Pos.Raw.extract.go₂ (mid ++ post) start
        (PosR (start.byteIdx + prefSize mid)) = mid := by
  intro mid
  induction mid with
  | nil =>
      intro post start
      show String.Pos.Raw.extract.go₂ post start (PosR (start.byteIdx + prefSize [])) = []
      have heq : PosR (start.byteIdx + prefSize []) = start := by
        show PosR (start.byteIdx + 0) = start
        rw [Nat.add_zero, posR_cases start, show (PosR start.byteIdx).byteIdx = start.byteIdx from rfl]
      rw [heq]
      show String.Pos.Raw.extract.go₂ post start start = []
      cases post with
      | nil => rfl
      | cons q post' =>
          rw [String.Pos.Raw.extract.go₂.eq_2]
          exact (if_pos rfl).symm ▸ rfl
  | cons p mid' ih =>
      intro post start
      have hne : ¬ (start = PosR (start.byteIdx + prefSize (p :: mid'))) := by
        intro h
        injection (show PosR start.byteIdx = PosR (start.byteIdx + prefSize (p :: mid')) from by
          rw [← posR_cases start]; exact h) with h0
        have := prefSize_pos p mid'
        omega
      show String.Pos.Raw.extract.go₂ ((p :: mid') ++ post) start
          (PosR (start.byteIdx + prefSize (p :: mid'))) = p :: mid'
      rw [List.cons_append, String.Pos.Raw.extract.go₂.eq_2, if_neg hne]
      show p :: String.Pos.Raw.extract.go₂ (mid' ++ post) (start + p)
          (PosR (start.byteIdx + prefSize (p :: mid'))) = p :: mid'
      rw [show start + p = PosR (start.byteIdx + p.utf8Size) from posR_cases start ▸ posR_add_char _ p,
        show prefSize (p :: mid') = p.utf8Size + prefSize mid' from rfl, ← Nat.add_assoc]
      exact congrArg (p :: ·) (ih post (PosR (start.byteIdx + p.utf8Size)))

/-- `extract.go₁` collects the characters between two prefix
    boundaries, skipping a prefix first. -/
theorem extractGo₁_eq (l : List Char) (n m : Nat) :
    String.Pos.Raw.extract.go₁ l (PosR n) (PosR n) (PosR (n + m)) =
      String.Pos.Raw.extract.go₂ l (PosR n) (PosR (n + m)) := by
  cases l with
  | nil => rfl
  | cons c cs => rw [String.Pos.Raw.extract.go₁.eq_2, if_pos rfl, String.Pos.Raw.extract.go₂.eq_2]

theorem extractGo₁ : ∀ (pre1 mid post : List Char) (n : Nat),
    String.Pos.Raw.extract.go₁ (pre1 ++ mid ++ post) (PosR n)
        (PosR (n + prefSize pre1))
        (PosR (n + prefSize pre1 + prefSize mid)) = mid := by
  intro pre1
  induction pre1 with
  | nil =>
      intro mid post n
      show String.Pos.Raw.extract.go₁ (mid ++ post) (PosR n) (PosR (n + prefSize []))
          (PosR (n + prefSize [] + prefSize mid)) = mid
      rw [show prefSize ([] : List Char) = 0 from rfl]
      show String.Pos.Raw.extract.go₁ (mid ++ post) (PosR n) (PosR (n + 0))
          (PosR (n + 0 + prefSize mid)) = mid
      rw [Nat.add_zero, extractGo₁_eq]
      exact extractGo₂ mid post (PosR n)
  | cons p pre1' ih =>
      intro mid post n
      have hne : ¬ ((PosR n) = PosR (n + prefSize (p :: pre1'))) := by
        intro h
        injection h with h0
        have := prefSize_pos p pre1'
        omega
      show String.Pos.Raw.extract.go₁ (p :: (pre1' ++ mid ++ post)) (PosR n)
          (PosR (n + prefSize (p :: pre1')))
          (PosR (n + prefSize (p :: pre1') + prefSize mid)) = mid
      rw [String.Pos.Raw.extract.go₁.eq_2, if_neg hne,
        show prefSize (p :: pre1') = p.utf8Size + prefSize pre1' from rfl, posR_add_char]
      have h1 : n + (p.utf8Size + prefSize pre1') = n + p.utf8Size + prefSize pre1' := by omega
      have h2 : n + (p.utf8Size + prefSize pre1') + prefSize mid
          = n + p.utf8Size + prefSize pre1' + prefSize mid := by omega
      rw [h1]
      exact ih mid post (n + p.utf8Size)

/-- `Pos.Raw.extract` between two prefix boundaries of a string is the
    string of the characters in between. -/
theorem pos_extract (s : String) (pre1 mid post : List Char)
    (hcs : s.toList = pre1 ++ mid ++ post) :
    (PosR (prefSize pre1)).extract s (PosR (prefSize pre1 + prefSize mid)) = String.ofList mid := by
  show (if prefSize pre1 ≥ prefSize pre1 + prefSize mid then ""
      else String.ofList (String.Pos.Raw.extract.go₁ s.toList 0
        (PosR (prefSize pre1)) (PosR (prefSize pre1 + prefSize mid)))) = String.ofList mid
  by_cases hge : prefSize pre1 ≥ prefSize pre1 + prefSize mid
  · have hz : prefSize mid = 0 := by omega
    have hmid : mid = [] := by
      cases mid with
      | nil => rfl
      | cons m mid' => exact absurd (prefSize_pos m mid') (by omega)
    subst hmid
    show (if prefSize pre1 ≥ prefSize pre1 + 0 then ""
      else String.ofList (String.Pos.Raw.extract.go₁ s.toList 0
        (PosR (prefSize pre1)) (PosR (prefSize pre1 + 0)))) = String.ofList []
    rw [show prefSize pre1 + 0 = prefSize pre1 from Nat.add_zero _, if_pos (Nat.le_refl _)]
  · rw [if_neg hge]
    show String.ofList (String.Pos.Raw.extract.go₁ s.toList (PosR 0) (PosR (prefSize pre1))
        (PosR (prefSize pre1 + prefSize mid))) = String.ofList mid
    have h0 : String.Pos.Raw.extract.go₁ (pre1 ++ mid ++ post) (PosR 0)
        (PosR (prefSize pre1)) (PosR (prefSize pre1 + prefSize mid)) = mid := by
      simpa only [Nat.zero_add, Nat.zero_add] using extractGo₁ pre1 mid post 0
    rw [show s.toList = pre1 ++ mid ++ post from hcs]
    exact congrArg String.ofList h0


/-- The scan invariant: with the segment-before-`b` already scanned
    (`pre0`), the current segment accumulated so far (`pre`, containing
    no separator), and the unscanned suffix (`rem`), the accumulator
    holds the already-finished segments (most recent first): the result
    is those segments (reversed into order) followed by the splits of
    the rest of the string. -/
theorem splitOnAux_inv : ∀ (N : Nat) (rem : List Char), rem.length ≤ N →
    ∀ (pre0 pre : List Char) (c : Char) (r : List String) (s : String),
    ¬ c ∈ pre → s.toList = pre0 ++ pre ++ rem →
    String.splitOnAux s (String.singleton c) (PosR (prefSize pre0))
      (PosR (prefSize pre0 + prefSize pre)) (PosR 0) r
      = r.reverse ++ ((List.splitOn c (pre ++ rem)).map String.ofList) := by
  intro N
  induction N with
  | zero =>
      intro rem hlen pre0 pre c r s hnm hcs
      -- rem = [] forced
      cases rem with
      | nil =>
          have hcs' : s.toList = pre0 ++ pre ++ ([] : List Char) := hcs
          rw [show pre0 ++ pre ++ ([] : List Char) = pre0 ++ pre from by
            rw [List.append_nil]] at hcs'
          rw [splitOnAux_end s pre0 pre c r hcs', List.append_nil]
          have hex : (PosR (prefSize pre0)).extract s (PosR (prefSize pre0 + prefSize pre))
              = String.ofList pre :=
            pos_extract s pre0 pre [] (by rw [hcs, List.append_nil])
          rw [hex, List.splitOn_eq_singleton hnm, List.map_singleton]
          show (String.ofList pre :: r).reverse
              = r.reverse ++ [String.ofList pre]
          exact List.reverse_cons
      | cons d rem' => rw [List.length_cons] at hlen; omega
  | succ N ih =>
      intro rem hlen pre0 pre c r s hnm hcs
      cases rem with
      | nil =>
          have hcs' : s.toList = pre0 ++ pre ++ ([] : List Char) := hcs
          rw [show pre0 ++ pre ++ ([] : List Char) = pre0 ++ pre from by
            rw [List.append_nil]] at hcs'
          rw [splitOnAux_end s pre0 pre c r hcs', List.append_nil]
          have hex : (PosR (prefSize pre0)).extract s (PosR (prefSize pre0 + prefSize pre))
              = String.ofList pre :=
            pos_extract s pre0 pre [] (by rw [hcs, List.append_nil])
          rw [hex, List.splitOn_eq_singleton hnm, List.map_singleton]
          show (String.ofList pre :: r).reverse
              = r.reverse ++ [String.ofList pre]
          exact List.reverse_cons
      | cons d rem' =>
          by_cases hd : d = c
          · -- matching step: emit the segment `pre`
            subst hd
            have hcs' : s.toList = (pre0 ++ pre) ++ (d :: rem') := by
              rw [hcs, List.append_assoc]
            have hext : String.Pos.Raw.extract s (PosR (prefSize pre0))
                (PosR (prefSize pre0 + prefSize pre)) = String.ofList pre :=
              pos_extract s pre0 pre (d :: rem') (by rw [hcs, List.append_assoc])
            have hih := ih rem' (by rw [List.length_cons] at hlen; omega)
              (pre0 ++ pre ++ [d]) [] d (String.ofList pre :: r) s
              (by simp) (by
                show s.toList = (pre0 ++ pre ++ [d]) ++ [] ++ rem'
                rw [hcs]
                simp only [List.append_assoc, List.cons_append, List.nil_append,
                  List.append_nil])
            have hps : prefSize (pre0 ++ pre ++ [d])
                = prefSize pre0 + prefSize pre + d.utf8Size := by
              rw [prefSize_append (pre0 ++ pre) [d], prefSize_append pre0 pre]
              show prefSize pre0 + prefSize pre + (d.utf8Size + prefSize ([] : List Char))
                = prefSize pre0 + prefSize pre + d.utf8Size
              rw [show prefSize ([] : List Char) = 0 from rfl, Nat.add_zero]
            rw [hps, show prefSize ([] : List Char) = 0 from rfl, Nat.add_zero] at hih
            have hsplit : List.splitOn d (pre ++ d :: rem')
                = pre :: List.splitOn d rem' :=
              List.splitOn_append_cons_self_of_not_mem hnm rem'
            rw [splitOnAux_step s pre0 pre rem' d r hcs', hext, hih, hsplit,
              List.map_cons, List.reverse_cons, List.nil_append]
            show r.reverse ++ [String.ofList pre]
                ++ List.map String.ofList (List.splitOn d rem')
              = r.reverse ++ String.ofList pre :: List.map String.ofList (List.splitOn d rem')
            simp
          · -- non-matching step: extend the current segment
            have hcs' : s.toList = pre0 ++ (pre ++ [d]) ++ rem' := by
              rw [hcs]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            have hnm' : ¬ c ∈ (pre ++ [d]) := by
              intro hmem
              rcases List.mem_append.mp hmem with h | h
              · exact hnm h
              · exact hd (List.mem_singleton.mp h).symm
            rw [splitOnAux_step_nomatch s pre0 pre rem' c d r
              (by rw [hcs, List.append_assoc]) hd]
            have hih := ih rem' (by rw [List.length_cons] at hlen; omega) pre0 (pre ++ [d]) c r
              s hnm' (by rw [hcs', List.append_assoc])
            have hih' : s.splitOnAux (String.singleton c) (PosR (prefSize pre0))
                (PosR (prefSize pre0 + prefSize pre + d.utf8Size)) (PosR 0) r
                = r.reverse ++ List.map String.ofList (List.splitOn c (pre ++ [d] ++ rem')) := by
              have h := hih
              rw [show prefSize (pre ++ [d]) = prefSize pre + d.utf8Size from by
                rw [prefSize_append pre [d]]
                show prefSize pre + (d.utf8Size + prefSize ([] : List Char))
                  = prefSize pre + d.utf8Size
                rw [show prefSize ([] : List Char) = 0 from rfl, Nat.add_zero]] at h
              rw [show prefSize pre0 + (prefSize pre + d.utf8Size)
                  = prefSize pre0 + prefSize pre + d.utf8Size from by omega] at h
              exact h
            rw [hih']
            show r.reverse ++ List.map String.ofList (List.splitOn c (pre ++ [d] ++ rem'))
              = r.reverse ++ List.map String.ofList (List.splitOn c (pre ++ d :: rem'))
            simp

/-- The master bridge: splitting a string on a single character is
    splitting its character list. -/
theorem splitOn_eq_splitOnList (s : String) (c : Char) :
    String.splitOn s (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hne : (String.singleton c == "") = false := by
    have hne' : ¬ (String.singleton c = "") := by
      intro h
      have h2 : (String.singleton c).toList = ("" : String).toList := by rw [h]
      rw [show (String.singleton c).toList = [c] from by
        rw [show String.singleton c = String.ofList [c] from String.singleton_eq_ofList,
          String.toList_ofList]] at h2
      rw [String.toList_empty] at h2
      exact absurd h2 (by simp)
    simp [hne']
  rw [String.splitOn, hne, if_neg (by simp)]
  have h := splitOnAux_inv s.toList.length s.toList (Nat.le_refl _) [] [] c [] s
    (by simp) (by simp)
  show s.splitOnAux (String.singleton c) (PosR (prefSize ([] : List Char)))
      (PosR (prefSize ([] : List Char) + prefSize ([] : List Char))) (PosR 0) []
    = [].reverse ++ List.map String.ofList (List.splitOn c ([] ++ s.toList))
  rw [h, List.nil_append, List.reverse_nil, List.nil_append]

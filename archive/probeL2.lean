/-
File: probeL2.lean

Purpose:
  Scratch file prototyping `extract` helper functions between prefix
  boundaries for the round-trip theorem (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution, Check, Globals), solver.Domain.

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn + solver.Domain -> probeL2.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Domain

open LeanFzn LeanFzn.Lexer LeanFzn.Solution LeanFzn.Solver LeanFzn.Check LeanFzn.Globals

def LeafFast.prefSize (cs : List Char) : Nat := (cs.map Char.utf8Size).sum
def LeafFast.PosR (n : Nat) : String.Pos.Raw := { byteIdx := n }

namespace LeafFast

theorem prefSize_cons (p : Char) (cs : List Char) :
    prefSize (p :: cs) = p.utf8Size + prefSize cs := rfl

theorem prefSize_append (l1 l2 : List Char) :
    prefSize (l1 ++ l2) = prefSize l1 + prefSize l2 := by
  simp only [prefSize, List.map_append, List.sum_append]

theorem prefSize_pos (c : Char) (cs : List Char) : 0 < prefSize (c :: cs) := by
  show 0 < c.utf8Size + prefSize cs
  have := c.utf8Size_pos
  omega

theorem posR_add_char (n : Nat) (c : Char) : PosR n + c = PosR (n + c.utf8Size) := by
  show { byteIdx := n + c.utf8Size } = PosR (n + c.utf8Size)
  rfl

theorem posR_byteIdx (n : Nat) : (PosR n).byteIdx = n := rfl

theorem posR_cases (p : String.Pos.Raw) : p = PosR p.byteIdx := by
  cases p; rfl

theorem utf8ByteSize_eq_prefSize (s : String) : s.utf8ByteSize = prefSize s.toList := by
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
      rw [hsplit, String.utf8ByteSize_append, h1, ih]
      rw [String.toList_append, h2, String.toList_ofList]
      show c.utf8Size + prefSize l = prefSize ([c] ++ l)
      rw [List.cons_append, List.nil_append, prefSize_cons]

theorem utf8GetAux_at : ∀ (pre post : List Char) (c : Char) (cs : List Char)
    (_hcs : cs = pre ++ (c :: post)) (start : String.Pos.Raw),
    String.Pos.Raw.utf8GetAux cs start (PosR (start.byteIdx + prefSize pre)) = c := by
  intro pre
  induction pre with
  | nil =>
      intro post c cs _hcs start
      subst _hcs
      rw [posR_cases start]
      show String.Pos.Raw.utf8GetAux (c :: post) (PosR start.byteIdx)
          (PosR (start.byteIdx + 0)) = c
      rw [Nat.add_zero, String.Pos.Raw.utf8GetAux.eq_2]
      simp
  | cons p pre' ih =>
      intro post c cs _hcs start
      subst _hcs
      have hne : ¬ (start = PosR (start.byteIdx + prefSize (p :: pre'))) := by
        intro h
        injection (show PosR start.byteIdx = PosR (start.byteIdx + prefSize (p :: pre')) from by
          rw [← posR_cases start]; exact h) with h0
        have := prefSize_pos p pre'
        omega
      show String.Pos.Raw.utf8GetAux (p :: (pre' ++ c :: post)) start
          (PosR (start.byteIdx + prefSize (p :: pre'))) = c
      rw [String.Pos.Raw.utf8GetAux.eq_2 start (PosR (start.byteIdx + prefSize (p :: pre'))) p
        (pre' ++ c :: post), if_neg hne,
        show start + p = PosR (start.byteIdx + p.utf8Size) from posR_cases start ▸ posR_add_char _ p,
        show prefSize (p :: pre') = p.utf8Size + prefSize pre' from rfl]
      show String.Pos.Raw.utf8GetAux (pre' ++ c :: post) (PosR (start.byteIdx + p.utf8Size))
          (PosR (start.byteIdx + (p.utf8Size + prefSize pre'))) = c
      rw [← Nat.add_assoc]
      exact ih post c (pre' ++ c :: post) rfl (PosR (start.byteIdx + p.utf8Size))

theorem pos_get_head (s : String) (pre post : List Char) (c : Char)
    (hcs : s.toList = pre ++ (c :: post)) :
    (PosR (prefSize pre)).get s = c := by
  show String.Pos.Raw.utf8GetAux s.toList (PosR 0) (PosR (prefSize pre)) = c
  have := utf8GetAux_at pre post c s.toList hcs (PosR 0)
  rw [show (PosR 0).byteIdx = 0 from rfl, Nat.zero_add] at this
  exact this

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

end LeafFast

namespace LeafFast

/-- `splitOnAux` at prefix positions: scanning `cs` from the boundary
    of `pre1` with the segment starting at the boundary of `pre0`,
    splitting on the character `c` (the only character of `sep`,
    assumed given as `String.singleton c`). -/
theorem splitOnAux_char : ∀ (cs pre0 pre1 mid post : List Char) (c : Char)
    (r : List String) (n : Nat),
    cs = pre0 ++ mid ++ (c :: post) →
    String.splitOnAux (String.ofList cs) (String.singleton c)
      (PosR (n + prefSize pre0)) (PosR (n + prefSize (pre0 ++ mid))) (PosR 0) r =
    (String.ofList mid) :: (splitOnAux_char_help cs pre0 mid post c r n) := by
  sorry

end LeafFast

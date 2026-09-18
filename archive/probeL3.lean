/-
File: probeL3.lean

Purpose:
  Scratch file for `utf8ByteSize` proofs related to the byte-position
  dictionary in the round-trip theorem (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution modules).

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn -> probeL3.lean (standalone, no dependents)
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

theorem splitOnAux_char : ∀ (N : Nat) (cs pre post : List Char) (c : Char)
    (r : List String) (n : Nat),
    cs.length ≤ N → cs = pre ++ (c :: post) →
    String.splitOnAux (String.ofList cs) (String.singleton c)
      (PosR n) (PosR (n + prefSize pre)) (PosR 0) r =
    String.splitOnAux (String.ofList cs) (String.singleton c)
      (PosR (n + prefSize pre + c.utf8Size)) (PosR (n + prefSize pre + c.utf8Size)) (PosR 0)
      (String.ofList pre :: r) := by
  intro N
  induction N with
  | zero =>
      intro cs pre post c r n hlen hcs
      subst hcs
      cases pre with
      | nil => simp at hlen
      | cons p pre' => simp at hlen
  | succ N ih =>
      intro cs pre post c r n hlen hcs
      subst hcs
      -- the byte size of the string
      have hcs2 : (String.ofList (pre ++ c :: post)).toList = pre ++ c :: post :=
        String.toList_ofList
      have hsz : (String.ofList (pre ++ c :: post)).utf8ByteSize
          = prefSize (pre ++ c :: post) := by
        have := utf8ByteSize_eq_prefSize' (String.ofList (pre ++ c :: post))
        rw [hcs2] at this
        exact this
      sorry

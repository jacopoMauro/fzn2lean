/-
File: probeL5.lean

Purpose:
  Scratch file for `skipToNewline` and `skipTrivia` append lemmas
  related to the `tokenize` lexer law (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution modules).

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn -> probeL5.lean (standalone, no dependents)
-/

import LeanFzn
open LeanFzn LeanFzn.Lexer LeanFzn.Solution

set_option maxHeartbeats 4000000

theorem toArray_append' (s t : String) :
    String.Internal.toArray (s ++ t) = String.Internal.toArray s ++ String.Internal.toArray t := by
  apply Array.ext'
  rw [show (String.Internal.toArray (s ++ t)).toList = (s ++ t).toList from rfl,
    Array.toList_append,
    show (String.Internal.toArray s).toList = s.toList from rfl,
    show (String.Internal.toArray t).toList = t.toList from rfl,
    String.toList_append]

theorem size_append_eq' (a b : Array Char) : (a ++ b).size = a.size + b.size :=
  Array.size_append

theorem getElem_append_size' (a b : Array Char) (j : Nat) (hj : j < b.size) :
    (a ++ b)[a.size + j]'(by
      have h1 : (a ++ b).size = a.size + b.size := size_append_eq' a b
      simp only [h1]
      omega) = b[j] := by
  have h1 : (a ++ b).size = a.size + b.size := size_append_eq' a b
  have hlt : ¬ (a.size + j < a.size) := by omega
  rw [Array.getElem_append (by simp only [h1]; omega)]
  split
  · exact absurd ‹_› hlt
  · congr 1
    omega

/-- `skipToNewline` on `a ++ b` starting at `a.size + k` scans only `b` from `k`. -/
theorem skipToNewline_offset (a b : LeanFzn.Lexer.Input) (n : Nat) :
    ∀ (k : Nat), b.size - k ≤ n →
    LeanFzn.Lexer.skipToNewline (a ++ b) (a.size + k)
      = a.size + LeanFzn.Lexer.skipToNewline b k := by
  induction n with
  | zero =>
      intro k hk
      have : b.size ≤ k := by omega
      have h1 : a.size + k ≥ (a ++ b).size := by
        rw [size_append_eq' a b]; omega
      have h2 : k ≥ b.size := by omega
      rw [LeanFzn.Lexer.skipToNewline, dif_neg (by
        show ¬ (a.size + k < (a ++ b).size)
        omega)]
      rw [LeanFzn.Lexer.skipToNewline, dif_neg (by omega)]
  | succ n ih =>
      intro k hk
      by_cases hlt : a.size + k < (a ++ b).size
      · have hkb : k < b.size := by
          rw [size_append_eq' a b] at hlt
          omega
        rw [LeanFzn.Lexer.skipToNewline, dif_pos hlt]
        have hchar : (a ++ b)[a.size + k]'hlt = b[k]'hkb := getElem_append_size' a b k hkb
        rw [hchar]
        by_cases hn : (b[k]'hkb) == '\n'
        · rw [if_pos hn]
          conv => rhs; rw [LeanFzn.Lexer.skipToNewline, dif_pos hkb, if_pos hn]
          show Array.size a + k + 1 = Array.size a + (k + 1)
          rfl
        · rw [if_neg hn]
          conv => rhs; rw [LeanFzn.Lexer.skipToNewline, dif_pos (by omega), if_neg hn]
          rw [show a.size + k + 1 = a.size + (k + 1) from rfl]
          exact ih (k + 1) (by omega)
      · rw [LeanFzn.Lexer.skipToNewline, dif_neg hlt]
        have hge : a.size + k ≥ (a ++ b).size := by omega
        have hge2 : k ≥ b.size := by
          rw [show (a ++ b).size = a.size + b.size from size_append_eq' a b] at hge
          omega
        conv => rhs; rw [LeanFzn.Lexer.skipToNewline, dif_neg (by omega)]

/-- `skipTrivia` on `a ++ b` starting at `a.size + k` scans only `b`
    from `k`. -/
theorem skipTrivia_offset (a b : LeanFzn.Lexer.Input) (n : Nat) :
    ∀ (k : Nat), b.size - k ≤ n →
    LeanFzn.Lexer.skipTrivia (a ++ b) (a.size + k)
      = a.size + LeanFzn.Lexer.skipTrivia b k := by
  induction n with
  | zero =>
      intro k hk
      have h1 : a.size + k ≥ (a ++ b).size := by
        rw [size_append_eq' a b]; omega
      rw [LeanFzn.Lexer.skipTrivia, dif_neg (by show ¬ (a.size + k < (a ++ b).size); omega)]
      rw [LeanFzn.Lexer.skipTrivia, dif_neg (by omega)]
  | succ n ih =>
      intro k hk
      by_cases hlt : a.size + k < (a ++ b).size
      · have hkb : k < b.size := by rw [size_append_eq' a b] at hlt; omega
        have hchar : (a ++ b)[a.size + k]'hlt = b[k]'hkb := getElem_append_size' a b k hkb
        rw [LeanFzn.Lexer.skipTrivia, dif_pos hlt, hchar]
        by_cases hw : LeanFzn.Lexer.isWhitespace (b[k]'hkb)
        · rw [if_pos hw]
          conv => rhs; rw [LeanFzn.Lexer.skipTrivia, dif_pos (by omega), if_pos hw]
          rw [show a.size + k + 1 = a.size + (k + 1) from rfl]
          exact ih (k + 1) (by omega)
        · rw [if_neg hw]
          by_cases hc : (b[k]'hkb) == '%'
          · rw [if_pos hc]
            conv => rhs; rw [LeanFzn.Lexer.skipTrivia, dif_pos (by omega), if_neg hw, if_pos hc]
            have hsnl := skipToNewline_offset a b n (k + 1) (by omega)
            rw [show a.size + k + 1 = a.size + (k + 1) from rfl, hsnl]
            exact ih (LeanFzn.Lexer.skipToNewline b (k + 1)) (by
              have hge1 := LeanFzn.Lexer.skipToNewline_ge b (k + 1)
              have hge2 := LeanFzn.Lexer.skipTrivia_ge b (LeanFzn.Lexer.skipToNewline b (k + 1))
              omega)
          · rw [if_neg hc]
            conv => rhs; rw [LeanFzn.Lexer.skipTrivia, dif_pos (by omega), if_neg hw, if_neg hc]
      · have hge : a.size + k ≥ (a ++ b).size := by omega
        rw [LeanFzn.Lexer.skipTrivia, dif_neg hlt]
        have hge2 : k ≥ b.size := by
          rw [show (a ++ b).size = a.size + b.size from size_append_eq' a b] at hge
          omega
        conv => rhs; rw [LeanFzn.Lexer.skipTrivia, dif_neg (by omega)]

/-- `takeWhile` on `a ++ b` starting at `a.size + k` scans only `b`
    from `k`; the resulting position is offset by `a.size` and the
    string by the accumulator. -/
theorem takeWhile_offset (p : Char → Bool) (a b : LeanFzn.Lexer.Input) (n : Nat) :
    ∀ (k : Nat) (acc : String), b.size - k ≤ n →
    LeanFzn.Lexer.takeWhile p (a ++ b) (a.size + k) acc
      = ((LeanFzn.Lexer.takeWhile p b k acc).1, a.size + (LeanFzn.Lexer.takeWhile p b k acc).2) := by
  induction n with
  | zero =>
      intro k acc hk
      have h1 : a.size + k ≥ (a ++ b).size := by rw [size_append_eq' a b]; omega
      rw [LeanFzn.Lexer.takeWhile.eq_def, dif_neg (by show ¬ (a.size + k < (a ++ b).size); omega)]
      have hb : LeanFzn.Lexer.takeWhile p b k acc = (acc, k) := by
        rw [LeanFzn.Lexer.takeWhile.eq_def, dif_neg (by omega)]
      rw [hb]
  | succ n ih =>
      intro k acc hk
      by_cases hlt : a.size + k < (a ++ b).size
      · have hkb : k < b.size := by rw [size_append_eq' a b] at hlt; omega
        have hchar : (a ++ b)[a.size + k]'hlt = b[k]'hkb := getElem_append_size' a b k hkb
        rw [LeanFzn.Lexer.takeWhile.eq_def, dif_pos hlt, hchar]
        by_cases hp : p (b[k]'hkb)
        · conv => rhs; rw [LeanFzn.Lexer.takeWhile.eq_def, dif_pos hkb, if_pos hp]
          rw [if_pos hp, show a.size + k + 1 = a.size + (k + 1) from rfl]
          exact ih (k + 1) (acc.push (b[k]'hkb)) (by omega)
        · rw [if_neg hp]
          have hb : LeanFzn.Lexer.takeWhile p b k acc = (acc, k) := by
            rw [LeanFzn.Lexer.takeWhile.eq_def, dif_pos hkb, if_neg hp]
          rw [hb]
      · have hge : a.size + k ≥ (a ++ b).size := by omega
        have hge2 : k ≥ b.size := by
          rw [show (a ++ b).size = a.size + b.size from size_append_eq' a b] at hge
          omega
        conv => lhs; rw [LeanFzn.Lexer.takeWhile.eq_def, dif_neg hlt]
        have hb : LeanFzn.Lexer.takeWhile p b k acc = (acc, k) := by
          rw [LeanFzn.Lexer.takeWhile.eq_def, dif_neg (by omega)]
        rw [hb]

/-- The token-and-end-position view of `lexToken`: what a successful
    lex step consumed. -/
def lexTokenResult (s : LeanFzn.Lexer.Input) (pos : Nat) (h : pos < s.size) :
    Except String (LeanFzn.Lexer.Token × Nat) :=
  (LeanFzn.Lexer.lexToken s pos h).map (fun p => (p.1, p.2.1))

/-- `lexString` on `a ++ b` at `a.size + k` succeeds exactly as on
    `b` at `k`, with the result offset by `a.size` (error texts may
    mention the offset position). -/
theorem lexString_offset (a b : LeanFzn.Lexer.Input) (n : Nat) :
    ∀ (k : Nat) (acc : String), b.size - k ≤ n →
    (LeanFzn.Lexer.lexString (a ++ b) (a.size + k) acc).toOption
      = (LeanFzn.Lexer.lexString b k acc).toOption.map
          (fun p => (p.1, a.size + p.2)) := by
  induction n with
  | zero =>
      intro k acc hk
      have h1 : a.size + k ≥ (a ++ b).size := by rw [size_append_eq' a b]; omega
      rw [LeanFzn.Lexer.lexString, dif_neg (by show ¬ (a.size + k < (a ++ b).size); omega)]
      rw [LeanFzn.Lexer.lexString, dif_neg (by omega)]
      rfl
  | succ n ih =>
      intro k acc hk
      by_cases hlt : a.size + k < (a ++ b).size
      · have hkb : k < b.size := by rw [size_append_eq' a b] at hlt; omega
        have hchar : (a ++ b)[a.size + k]'hlt = b[k]'hkb := getElem_append_size' a b k hkb
        rw [LeanFzn.Lexer.lexString, dif_pos hlt, hchar]
        by_cases hq : (b[k]'hkb) == '"'
        · rw [if_pos hq]
          conv => rhs; rw [LeanFzn.Lexer.lexString, dif_pos hkb, if_pos hq]
          show (Except.ok (acc, a.size + k + 1)).toOption
            = (Except.ok (acc, k + 1)).toOption.map
              (fun p : String × Nat => (p.1, a.size + p.2))
          rfl
        · rw [if_neg hq]
          by_cases hbs : (b[k]'hkb) == '\\'
          · rw [if_pos hbs]
            by_cases hnext : a.size + k + 1 < (a ++ b).size
            · rw [if_pos hnext]
              have hnb : k + 1 < b.size := by rw [size_append_eq' a b] at hnext; omega
              have hchar2 : (a ++ b)[a.size + (k + 1)] = b[k + 1] :=
                getElem_append_size' a b (k + 1) hnb
              have hchar2' : (a ++ b)[a.size + k + 1]! = b[k + 1]! := by
                have hq1 : (a ++ b)[a.size + k + 1]? = b[k + 1]? := by
                  rw [show a.size + k + 1 = a.size + (k + 1) from rfl,
                    Array.getElem?_append, if_neg (by omega),
                    show a.size + (k + 1) - a.size = k + 1 from by omega,
                    Array.getElem?_eq_getElem hnb]
                simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hq1]
              rw [hchar2']
              conv => rhs; rw [LeanFzn.Lexer.lexString, dif_pos hkb, if_neg hq, if_pos hbs,
                if_pos hnb]
              rw [show a.size + k + 2 = a.size + (k + 2) from rfl]
              exact ih (k + 2) (acc.push (b[k + 1]'hnb)) (by omega)
            · rw [if_neg hnext]
              conv => rhs; rw [LeanFzn.Lexer.lexString, dif_pos hkb, if_neg hq, if_pos hbs,
                if_neg (by
                  have : a.size + k + 1 < a.size + b.size := by
                    rw [show (a ++ b).size = a.size + b.size from size_append_eq' a b] at hnext
                    exact absurd this hnext
                  omega)]
              rfl
          · rw [if_neg hbs]
            by_cases hnl : (b[k]'hkb) == '\n'
            · rw [if_pos hnl]
              conv => rhs; rw [LeanFzn.Lexer.lexString, dif_pos hkb, if_neg hq, if_neg hbs,
                if_pos hnl]
              rfl
            · rw [if_neg hnl]
              conv => rhs; rw [LeanFzn.Lexer.lexString, dif_pos hkb, if_neg hq, if_neg hbs,
                if_neg hnl]
              rw [show a.size + k + 1 = a.size + (k + 1) from rfl]
              exact ih (k + 1) (acc.push (b[k]'hkb)) (by omega)
      · rw [LeanFzn.Lexer.lexString, dif_neg hlt]
        conv => rhs; rw [LeanFzn.Lexer.lexString, dif_neg (by omega)]
        rfl

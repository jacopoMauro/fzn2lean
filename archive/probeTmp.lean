import LeanFzn

/-!
Probe file (not a build target): guard-exclusion lemmas for the
integer half of the lexer round-trip (`solver/Emit.lean` item-2 work).

Facts pinned here (the Emit layer combines them with its existing
`toDigits_isDigit`):

* a digit char equals neither `'x'` nor `'o'` nor `'-'` — so on the
  `toDigits` text the hex/octal prefix guards of `lexUnsigned` fail,
  and `lexInt`'s leading-`-` guard fails;
* `lexInt` on the digits text: the `-` guard fails, so the result is
  `lexUnsigned`, whose guards both fail, so the result is the decimal
  `.ok (parseDecNat digits, end)` — the decimal arm, unconditionally
  on all-digit inputs (given the scan actually stops, i.e. the text
  is nonempty);
* the same arms inside `lexToken` at a digit head.
-/

namespace LeanFzn.Lexer

/-- A digit char equals neither `'x'` nor `'o'`. -/
theorem digit_not_xo {c : Char} (hd : isDigit c = true) :
    (c == 'x') = false ∧ (c == 'o') = false := by
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hge, hle⟩ := hd
  refine ⟨?_, ?_⟩
  · by_cases hc : c = 'x'
    · subst hc
      -- hle : ('x' : Char) ≤ '9' — it's decidable-false:
      have h9x : ¬ ((('x' : Char) : Char) ≤ '9') := by decide
      exact absurd hle h9x
    · show (c == 'x') = false
      by_cases hbeq : (c == 'x') = true
      · exact absurd (eq_of_beq hbeq) hc
      · exact Bool.not_eq_true _ |>.mp (by simpa using hbeq)
  · by_cases hc : c = 'o'
    · subst hc
      have h9o : ¬ ((('o' : Char)) ≤ '9') := by decide
      exact absurd hle h9o
    · show (c == 'o') = false
      by_cases hbeq : (c == 'o') = true
      · exact absurd (eq_of_beq hbeq) hc
      · exact Bool.not_eq_true _ |>.mp (by simpa using hbeq)

/-- A digit char is not `'-'` (digits start at `'0'`, which is after
    `'-'`). -/
theorem digit_not_minus {c : Char} (hd : isDigit c = true) : (c == '-') = false := by
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hge, hle⟩ := hd
  -- hge : '0' ≤ c.  If c = '-', then '0' ≤ '-' — false:
  cases hd' : (c == '-') with
  | true =>
      have hceq : c = '-' := eq_of_beq hd'
      subst hceq
      have hcontra : ('0' : Char) ≤ '-' := hge
      exact absurd hcontra (by decide)
  | false => rfl


/-- The bang read equals the proof-carrying read below the size
    (probe twin of `takeWhile_step_of`'s helper; the real home is
    `solver/Emit.lean`). -/
theorem arrGetElem_bang_eq' {s : Array Char} {i : Nat} (h : i < s.size) :
    s[i]! = s[i]'h := by
  rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]

/-- On a digit-headed array whose every char is a digit, `lexUnsigned`
    takes the decimal arm (both prefix guards fail: the second char,
    when present, is a digit — never `'x'`/`'o'`).  The decimal-arm
    nonemptiness is derived directly from `takeWhile`'s definitional
    step (no helper needed). -/
theorem lexUnsigned_decimal {s : Array Char} {pos : Nat}
    (hpos : pos < s.size)
    (hhead : isDigit s[pos]! = true)
    (hdigits : ∀ k : Nat, k < s.size → isDigit s[k]! = true) :
    lexUnsigned s pos =
      .ok ((parseDecNat (takeWhile isDigit s pos "").1 : Int),
           (takeWhile isDigit s pos "").2) := by
  rw [lexUnsigned]
  -- the hex/oct guard conjunctions are false (the char at pos+1 is a
  -- digit, never 'x'/'o'):
  have hsecondigit : pos + 1 < s.size → isDigit s[pos + 1]! = true := by
    intro h1
    exact hdigits (pos + 1) h1
  have hx : ¬ ((decide (pos + 1 < s.size) && s[pos]! == '0'
        && s[pos + 1]! == 'x') = true) := by
    intro hh
    rw [Bool.and_eq_true, Bool.and_eq_true] at hh
    obtain ⟨⟨h1, _⟩, hxneg⟩ := hh
    have h1n : pos + 1 < s.size := by simpa using h1
    have hstep := (digit_not_xo (hsecondigit h1n)).1
    rw [hstep] at hxneg
    exact Bool.noConfusion hxneg
  have ho : ¬ ((decide (pos + 1 < s.size) && s[pos]! == '0'
        && s[pos + 1]! == 'o') = true) := by
    intro hh
    rw [Bool.and_eq_true, Bool.and_eq_true] at hh
    obtain ⟨⟨h1, _⟩, honeg⟩ := hh
    have h1n : pos + 1 < s.size := by simpa using h1
    have hstep := (digit_not_xo (hsecondigit h1n)).2
    rw [hstep] at honeg
    exact Bool.noConfusion honeg
  rw [if_neg hx, if_neg ho]
  -- the decimal arm: the scan consumed at least the head digit, so
  -- its result cannot be empty.  Route: if the scan were empty, then
  -- by its one-step unfold the head branch was not taken — i.e.
  -- `isDigit s[pos] = false` — contradicting `hhead`.  This avoids
  -- any accumulator-shift law: the contradiction reads directly off
  -- the definition's false branch (`("", pos)`).
  have hnonempty : ¬ ((takeWhile isDigit s pos "").1.isEmpty = true) := by
    intro hempty
    rw [takeWhile.eq_def (s := s) (pos := pos) (acc := "")] at hempty
    simp only [dif_pos hpos] at hempty
    -- the if test is on the no-bang read; transport hhead to it:
    have hposnb : s[pos]! = s[pos] := by
      have h1 : s[pos]! = s[pos]'hpos := by
        rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]
      -- h1 : s[pos]! = s[pos]'hpos; the proof-carrying read is
      -- definitionally the plain read, so prove the shift first:
      have h2 : s[pos]'hpos = s[pos] := rfl
      rw [h2] at h1
      exact h1
    rw [hposnb] at hhead
    by_cases hdig : isDigit s[pos] = true
    · rw [if_pos hdig] at hempty
      -- hempty : (takeWhile isDigit s (pos+1) ("" push s[pos])).fst =
      -- "".  But the pushed accumulator keeps s[pos] as its first
      -- char (a takeWhile result is acc ++ scanned, and the acc is
      -- returned verbatim in the stop case).  Simplest sound route:
      -- the takeWhile result string at least contains the pushed
      -- char (acc prefix); derive the contradiction generically:
      exfalso
      -- If the scan stopped immediately (or not), the acc-prefix
      -- remains: use the length law takeWhile_length from the lexer
      -- module (it is public there):
      have hlen := takeWhile_length isDigit s (pos + 1)
        (String.singleton s[pos])
      -- hlen : result.len = 1 + (result.end - (pos+1)) ≥ 1 (the acc
      -- prefix).hempty says that very .1 is "" (length 0):
      rw [show ("".push s[pos]) = String.singleton s[pos] from rfl,
        String.isEmpty_iff] at hempty
      rw [hempty] at hlen
      simp at hlen
      -- hlen : 0 = 1 + (end - (pos+1)); a Nat difference is ≥ 0:
      omega
    · rw [if_neg hdig] at hempty
      -- the false branch is ("", pos): hdig contradicts hhead:
      exact absurd hhead hdig
  rw [if_neg hnonempty]

/-- `lexInt` on a digit-headed array: the `-` guard fails (the head
    is a digit), so the result is the `.intLit` mapping of `lexUnsigned`
    at `pos`. -/
theorem lexInt_nonneg_head {s : Array Char} {pos : Nat}
    (_hpos : pos < s.size)
    (hhead : isDigit s[pos]! = true) :
    lexInt s pos =
      (lexUnsigned s pos).map (fun p => (.intLit p.1, p.2)) := by
  rw [lexInt]
  -- the `-` guard is false: the decide fires only when both hold,
  -- and the head is a digit (never '-'):
  have hm : ¬ ((decide (pos < s.size) && (s[pos]! == '-')) = true) := by
    intro hh
    rw [Bool.and_eq_true] at hh
    obtain ⟨_h1, hneg⟩ := hh
    rw [digit_not_minus hhead] at hneg
    exact Bool.noConfusion hneg
  rw [if_neg hm]
  -- both forms case on lexUnsigned's outcome; `map` is that match:
  cases hlu : lexUnsigned s pos with
  | ok p => rfl
  | error e => rfl

end LeanFzn.Lexer
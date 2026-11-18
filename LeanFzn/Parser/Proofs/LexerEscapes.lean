/-
Purpose: Greedy bounded digit scans and byte escape correspondence.
Dependencies: Independent Lexical, suffix/scan and positional numeral bridges.
DAG: Lexical + Numbers -> this module -> arbitrary-accumulator string proofs.
-/
import LeanFzn.Parser.Proofs.LexerDigits

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

/-- Inverting a nonempty suffix determines its head, bounds and next suffix. -/
theorem suffix_cons {s : Array Char} {pos : Nat} {c : Char} {cs : List Char}
    (h : Suffix.toList s pos = c :: cs) :
    ∃ hp : pos < s.size, s[pos] = c ∧ Suffix.toList s (pos + 1) = cs := by
  have hn : ¬ s.size ≤ pos := by
    intro hn
    have := (Suffix.toList_eq_nil_iff s pos).mpr hn
    rw [h] at this
    cases this
  have hp : pos < s.size := by omega
  have hh := Suffix.toList_getElem s pos hp
  rw [h] at hh
  exact ⟨hp, (List.cons.inj hh).1.symm, (List.cons.inj hh).2.symm⟩

theorem digitsUpTo_spec (p : Char → Bool) (s : Array Char) (pos limit : Nat)
    (hp : pos ≤ s.size) :
    let ds := digitsUpTo p s pos limit
    (∀ c ∈ ds, p c = true) ∧ ds.length ≤ limit ∧ pos + ds.length ≤ s.size ∧
    Suffix.toList s pos = ds ++ Suffix.toList s (pos + ds.length) ∧
    (ds.length < limit → Boundary (fun c => p c = true)
      (Suffix.toList s (pos + ds.length))) := by
  induction limit generalizing pos with
  | zero => simp [digitsUpTo, hp]
  | succ limit ih =>
    rw [digitsUpTo]
    split
    · rename_i hpos
      split
      · rename_i hc
        have hh := ih (pos + 1) (by omega)
        simp only [List.length_cons, List.cons_append, List.mem_cons]
        refine ⟨?_, by omega, by omega, ?_, ?_⟩
        · intro c hc'
          rcases hc' with rfl | hc'
          · exact hc
          · exact hh.1 c hc'
        · rw [Suffix.toList_getElem s pos hpos, hh.2.2.2.1]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · intro hlen
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hh.2.2.2.2 (by omega)
      · rename_i hc
        simp only [List.length_nil, Nat.add_zero, List.not_mem_nil, List.nil_append]
        refine ⟨by simp, by omega, hp, True.intro, ?_⟩
        intro _
        rw [Suffix.toList_getElem s pos hpos]
        exact hc
    · rename_i hpos
      have heq : pos = s.size := by omega
      subst pos
      have hs : Suffix.toList s s.size = [] := (Suffix.toList_eq_nil_iff s s.size).mpr (by omega)
      simp [hs, Boundary]

theorem digitsUpTo_complete (p : Char → Bool) (s : Array Char) (pos limit : Nat)
    {ds rest : List Char} (he : Suffix.toList s pos = ds ++ rest)
    (hall : ∀ c ∈ ds, p c = true) (hlen : ds.length ≤ limit)
    (hstop : ds.length < limit → Boundary (fun c => p c = true) rest) :
    digitsUpTo p s pos limit = ds := by
  induction limit generalizing pos ds with
  | zero =>
    have hd : ds = [] := List.length_eq_zero_iff.mp (by omega)
    subst ds
    rfl
  | succ limit ih =>
    cases ds with
    | nil =>
      simp only [List.nil_append] at he
      rw [digitsUpTo]
      split
      · rename_i hp
        have hc := hstop (by simp)
        rw [← he, Suffix.toList_getElem s pos hp] at hc
        simp [show p s[pos] ≠ true from hc]
      · rfl
    | cons c ds =>
      obtain ⟨hp, hc, ht⟩ := suffix_cons he
      rw [digitsUpTo]
      simp only [hp, dif_pos, hc, hall c (by simp), ite_true]
      congr 1
      exact ih (pos + 1) ht (fun d hd => hall d (by simp [hd])) (by simpa using hlen)
        (fun hl => hstop (by simpa using hl))

/-- Successful escape decoding consumes a bounded prefix with its exact byte. -/
theorem lexEscape_sound {s : Array Char} {pos : Nat} {byte : UInt8}
    {q : Nat} {hq : pos < q} (h : lexEscape s pos = some (byte, ⟨q, hq⟩)) :
    q ≤ s.size ∧ Escape (Suffix.toList s pos) byte (Suffix.toList s q) := by
  unfold lexEscape at h
  split at h
  · rename_i hp
    split at h
    · rename_i hc
      cases h
      refine ⟨by omega, ?_⟩
      rw [Suffix.toList_getElem s pos hp, hc]
      exact .newline
    · rename_i hc
      cases h
      refine ⟨by omega, ?_⟩
      rw [Suffix.toList_getElem s pos hp, hc]
      exact .tab
    · rename_i hc
      cases h
      refine ⟨by omega, ?_⟩
      rw [Suffix.toList_getElem s pos hp, hc]
      exact .quote
    · rename_i hc
      cases h
      refine ⟨by omega, ?_⟩
      rw [Suffix.toList_getElem s pos hp, hc]
      exact .backslash
    · rename_i hc
      simp only at h
      split at h
      · cases h
      · rename_i hne
        have hspec := digitsUpTo_spec isHexDigit s (pos + 1) 2 (by omega)
        obtain ⟨n, hd⟩ := digits_of_all (fun c hc =>
          (baseDigit16_iff c).mpr (hspec.1 c hc))
        have hlen : 1 ≤ (digitsUpTo isHexDigit s (pos + 1) 2).length := by
          have hn : digitsUpTo isHexDigit s (pos + 1) 2 ≠ [] := by
            intro hn
            simp [hn] at hne
          exact List.length_pos_iff.mpr hn
        rw [parseNatBase_of_digits hd] at h
        cases h
        refine ⟨hspec.2.2.1, ?_⟩
        rw [Suffix.toList_getElem s pos hp, hc, hspec.2.2.2.1]
        exact .hex ⟨hlen, hspec.2.1⟩ hd (by
          simpa only [Boundary, baseDigit16_iff] using hspec.2.2.2.2)
    · rename_i c hn ht hquote hslash hx
      simp only at h
      split at h
      · rename_i ho
        have hspec := digitsUpTo_spec isOctDigit s pos 3 (by omega)
        obtain ⟨n, hd⟩ := digits_of_all (fun c hc =>
          (baseDigit8_iff c).mpr (hspec.1 c hc))
        have hlen : 1 ≤ (digitsUpTo isOctDigit s pos 3).length := by
          have hn : digitsUpTo isOctDigit s pos 3 ≠ [] := by
            rw [digitsUpTo]
            simp only [hp, dif_pos, ho, ite_true]
            exact List.cons_ne_nil _ _
          exact List.length_pos_iff.mpr hn
        rw [parseNatBase_of_digits hd] at h
        split at h
        · rename_i hb
          cases h
          have hm : max (digitsUpTo isOctDigit s pos 3).length 1 =
              (digitsUpTo isOctDigit s pos 3).length := Nat.max_eq_left hlen
          simp only [hm]
          refine ⟨hspec.2.2.1, ?_⟩
          rw [hspec.2.2.2.1]
          exact .octal ⟨hlen, hspec.2.1⟩ hd (by
            simpa only [Boundary, baseDigit8_iff] using hspec.2.2.2.2) hb
        · cases h
      · cases h
  · cases h

theorem digits_baseDigits {base : Nat} {cs : List Char} {n : Nat}
    (h : Digits base cs n) : ∀ c ∈ cs, BaseDigit base c := by
  induction h with
  | nil => simp
  | @cons c d cs n hd ht ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨d, hd⟩
    · exact ih x hx

theorem suffix_after_prefix {s : Array Char} {pos : Nat} {ds rest : List Char}
    (he : Suffix.toList s pos = ds ++ rest) (hp : pos ≤ s.size) :
    pos + ds.length ≤ s.size ∧ Suffix.toList s (pos + ds.length) = rest := by
  have hl := congrArg List.length he
  rw [Suffix.toList_size, List.length_append] at hl
  refine ⟨by omega, ?_⟩
  have hh := congrArg (List.drop ds.length) he
  simpa [Suffix.toList, List.drop_drop] using hh

theorem lexEscape_complete {s : Array Char} {pos : Nat} {byte : UInt8} {rest : List Char}
    (h : Escape (Suffix.toList s pos) byte rest) :
    ∃ (q : Nat) (hq : pos < q), lexEscape s pos = some (byte, ⟨q, hq⟩) ∧
      q ≤ s.size ∧ Suffix.toList s q = rest := by
  generalize he : Suffix.toList s pos = input at h
  cases h with
  | newline =>
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    refine ⟨pos + 1, by omega, ?_, by omega, ht⟩
    simp [lexEscape, hp, hc]
  | tab =>
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    refine ⟨pos + 1, by omega, ?_, by omega, ht⟩
    simp [lexEscape, hp, hc]
  | quote =>
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    refine ⟨pos + 1, by omega, ?_, by omega, ht⟩
    simp [lexEscape, hp, hc]
  | backslash =>
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    refine ⟨pos + 1, by omega, ?_, by omega, ht⟩
    simp [lexEscape, hp, hc]
  | @hex ds n tail hlen hd hstop =>
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    have hs := digitsUpTo_complete isHexDigit s (pos + 1) 2 ht
      (fun c hc => (baseDigit16_iff c).mp (digits_baseDigits hd c hc)) hlen.2
      (by simpa only [Boundary, baseDigit16_iff] using hstop)
    have hn : ds.isEmpty = false := by
      cases ds with
      | nil => simp at hlen
      | cons => rfl
    have ht' := suffix_after_prefix ht (by omega)
    refine ⟨pos + 1 + ds.length, by omega, ?_, ht'.1, ht'.2⟩
    simp [lexEscape, hp, hc, hs, hn, parseNatBase_of_digits hd, Nat.toUInt8_eq]
  | @octal ds n tail hlen hd hstop hb =>
    have hne : ds ≠ [] := List.length_pos_iff.mp hlen.1
    cases ds with
    | nil => contradiction
    | cons c cs =>
      obtain ⟨hp, hc, ht⟩ := suffix_cons he
      have ho : isOctDigit c = true := (baseDigit8_iff c).mp (digits_baseDigits hd c (by simp))
      have hn : c ≠ 'n' := by intro h; rw [h] at ho; simp [isOctDigit] at ho
      have htab : c ≠ 't' := by intro h; rw [h] at ho; simp [isOctDigit] at ho
      have hquote : c ≠ '\"' := by intro h; rw [h] at ho; simp [isOctDigit] at ho
      have hslash : c ≠ '\\' := by intro h; rw [h] at ho; simp [isOctDigit] at ho
      have hx : c ≠ 'x' := by intro h; rw [h] at ho; simp [isOctDigit] at ho
      have hs := digitsUpTo_complete isOctDigit s pos 3 he
        (fun c hc => (baseDigit8_iff c).mp (digits_baseDigits hd c hc)) hlen.2
        (by simpa only [Boundary, baseDigit8_iff] using hstop)
      have ht' := suffix_after_prefix he (by omega)
      have hv : parseNatBase 8 (String.singleton c ++ String.ofList cs) = n := by
        simpa using parseNatBase_of_digits hd
      refine ⟨pos + (c :: cs).length, by simp, ?_, ht'.1, ht'.2⟩
      simp [lexEscape, hp, hc, hn, htab, hquote, hslash, hx, ho, hs,
        parseNatBase_of_digits hd, hv, hb, Nat.max_eq_left hlen.1, Nat.toUInt8_eq]

end LeanFzn.Parser.Lexer

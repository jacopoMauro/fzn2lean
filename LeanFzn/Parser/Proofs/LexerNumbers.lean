/-
Purpose: Numeric scanner soundness and completeness against Magnitude.
Dependencies: Stable LexerDigits arithmetic, LexerScan and character suffixes.
DAG: Digit/scan proofs -> numeric scanners -> significant-token proof.
-/
import LeanFzn.Parser.Proofs.LexerDigits
import LeanFzn.Parser.Proofs.LexerScan
namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

private theorem char_le_nat (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

/-- The first two in-range array characters agree with the suffix view. -/
theorem suffix_two (s : Array Char) (pos : Nat) (h : pos + 1 < s.size) :
    Suffix.toList s pos = s[pos]! :: s[pos+1]! :: Suffix.toList s (pos+2) := by
  rw [Suffix.toList_getElem s pos (by omega), Suffix.toList_getElem s (pos+1) h]
  simp [getElem!_pos, show pos < s.size by omega, h, Nat.add_assoc]

theorem suffix_two_inv {s : Array Char} {pos : Nat} {a b : Char} {rest : List Char}
    (h : Suffix.toList s pos = a :: b :: rest) :
    pos + 1 < s.size ∧ s[pos]! = a ∧ s[pos+1]! = b ∧
      Suffix.toList s (pos+2) = rest := by
  have hl := congrArg List.length h
  rw [Suffix.toList_size] at hl
  simp only [List.length_cons] at hl
  have hb : pos + 1 < s.size := by omega
  rw [suffix_two s pos hb] at h
  exact ⟨hb, (List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1,
    (List.cons.inj (List.cons.inj h).2).2⟩

theorem intFormat_hex {s : Array Char} {pos : Nat} {rest : List Char}
    (h : Suffix.toList s pos = '0' :: 'x' :: rest) :
    intFormat s pos = (isHexDigit,16,2,"hexadecimal") := by
  obtain ⟨hb, h0, hx, _⟩ := suffix_two_inv h
  have hx' : s[pos+1] = 'x' := by simpa only [getElem!_pos s (pos+1) hb] using hx
  simp [intFormat, hb, h0, hx']

theorem intFormat_octal {s : Array Char} {pos : Nat} {rest : List Char}
    (h : Suffix.toList s pos = '0' :: 'o' :: rest) :
    intFormat s pos = (isOctDigit,8,2,"octal") := by
  obtain ⟨hb, h0, ho, _⟩ := suffix_two_inv h
  have ho' : s[pos+1] = 'o' := by simpa only [getElem!_pos s (pos+1) hb] using ho
  simp [intFormat, hb, h0, ho']

theorem intFormat_decimal {s : Array Char} {pos : Nat}
    (h : ¬ RadixPrefix (Suffix.toList s pos)) :
    intFormat s pos = (isDigit,10,0,"integer") := by
  unfold intFormat
  split
  · rename_i hh
    simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hh
    obtain ⟨⟨hb,h0⟩,hx⟩ := hh
    have hs := suffix_two s pos hb
    rw [h0,hx] at hs
    exact (h (by rw [hs]; trivial)).elim
  · split
    · rename_i hh
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hh
      obtain ⟨⟨hb,h0⟩,ho⟩ := hh
      have hs := suffix_two s pos hb
      rw [h0,ho] at hs
      exact (h (by rw [hs]; trivial)).elim
    · rfl

/-- A maximal Boolean digit scan has the independent positional value. -/
theorem takeWhile_digits (p : Char → Bool) (base : Nat) (s : Array Char) (pos : Nat)
    (hp : ∀ c, BaseDigit base c ↔ p c = true) (hpos : pos ≤ s.size) :
    ∃ ds n, (takeWhile p s pos "").1 = String.ofList ds ∧ Digits base ds n ∧
      Suffix.toList s pos = ds ++ Suffix.toList s (takeWhile p s pos "").2 ∧
      Boundary (BaseDigit base) (Suffix.toList s (takeWhile p s pos "").2) ∧
      (takeWhile p s pos "").2 ≤ s.size := by
  obtain ⟨ds, hstr, hs, hall, hb, hbound⟩ := takeWhile_spec p s pos "" hpos
  have hv : (takeWhile p s pos "").1 = String.ofList ds := by
    apply String.toList_inj.mp
    simpa using hstr
  obtain ⟨n, hn⟩ := digits_of_all (fun c hc => (hp c).mpr (hall c hc))
  refine ⟨ds, n, hv, hn, hs, ?_, hbound⟩
  cases hrest : Suffix.toList s (takeWhile p s pos "").2 with
  | nil => trivial
  | cons c cs =>
      simp only [hrest, Boundary] at hb ⊢
      exact fun hd => hb ((hp c).mp hd)

theorem digits_all {base : Nat} {ds : List Char} {n : Nat}
    (h : Digits base ds n) : ∀ c ∈ ds, BaseDigit base c := by
  induction h with
  | nil => simp
  | @cons c d cs n hd ht ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨d,hd⟩
      · exact ih x hx

private theorem ofList_isEmpty_false {ds : List Char} (h : ds ≠ []) :
    (String.ofList ds).isEmpty = false := by
  apply String.isEmpty_eq_false_iff.mpr
  intro hs
  apply h
  simpa using congrArg String.toList hs

/-- A supplied maximal positional digit derivation is recognized after the
format selector has committed to its radix and prefix width. -/
theorem lexUnsigned_complete_of_format (s : Array Char) (pos : Nat)
    (p : Char → Bool) (base offset : Nat) (kind : String)
    (ds rest : List Char) (n : Nat)
    (hfmt : intFormat s pos = (p,base,offset,kind))
    (hp : ∀ c, BaseDigit base c ↔ p c = true)
    (hs : Suffix.toList s (pos+offset) = ds ++ rest)
    (hd : Digits base ds n) (hne : ds ≠ [])
    (hb : Boundary (BaseDigit base) rest) (hstart : pos+offset ≤ s.size) :
    ∃ q : { q : Nat // pos < q },
      lexUnsigned s pos = .ok ((n : Int),q) ∧ Suffix.toList s q.val = rest ∧ q.val ≤ s.size := by
  have hall : ∀ c ∈ ds, p c = true := fun c hc => (hp c).mp (digits_all hd c hc)
  have hb' : Boundary (fun c => p c = true) rest := by
    cases rest with
    | nil => trivial
    | cons c cs => exact fun h => hb ((hp c).mpr h)
  obtain ⟨hrun,hrest⟩ := takeWhile_complete p s (pos+offset) "" ds rest hs hall hb' hstart
  have hrun : takeWhile p s (pos+offset) "" = (String.ofList ds,pos+offset+ds.length) := by
    simpa using hrun
  have hlen : 0 < ds.length := List.length_pos_iff.mpr hne
  have hbound : pos+offset+ds.length ≤ s.size := by
    have hl := congrArg List.length hs
    rw [Suffix.toList_size, List.length_append] at hl
    omega
  refine ⟨⟨pos+offset+ds.length,by omega⟩, ?_, hrest, hbound⟩
  simp only [lexUnsigned,hfmt]
  simp only [hrun, ofList_isEmpty_false hne, Bool.false_eq_true, dite_false, parseNatBase_of_digits hd]

/-- Every independent magnitude derivation is recognized with its exact value
and remaining suffix; no successful-execution premise is assumed. -/
theorem lexUnsigned_complete {s : Array Char} {pos : Nat} {input rest : List Char} {n : Nat}
    (hinput : Suffix.toList s pos = input) (hm : Magnitude input n rest)
    (hpos : pos ≤ s.size) :
    ∃ q : { q : Nat // pos < q },
      lexUnsigned s pos = .ok ((n : Int),q) ∧ Suffix.toList s q.val = rest ∧ q.val ≤ s.size := by
  cases hm with
  | @decimal ds n rest hne hd hb hp =>
      apply lexUnsigned_complete_of_format s pos isDigit 10 0 "integer" ds rest n
      · exact intFormat_decimal (by simpa [hinput] using hp)
      · exact baseDigit10_iff
      · simpa using hinput
      · exact hd
      · exact hne
      · exact hb
      · simpa using hpos
  | @hex ds n rest hne hd hb =>
      have hinv := suffix_two_inv hinput
      apply lexUnsigned_complete_of_format s pos isHexDigit 16 2 "hexadecimal" ds rest n
      · exact intFormat_hex hinput
      · exact baseDigit16_iff
      · exact hinv.2.2.2
      · exact hd
      · exact hne
      · exact hb
      · omega
  | @octal ds n rest hne hd hb =>
      have hinv := suffix_two_inv hinput
      apply lexUnsigned_complete_of_format s pos isOctDigit 8 2 "octal" ds rest n
      · exact intFormat_octal hinput
      · exact baseDigit8_iff
      · exact hinv.2.2.2
      · exact hd
      · exact hne
      · exact hb
      · omega

/-- Value/suffix facts for a successful scanner after a selected radix. -/
theorem lexUnsigned_sound_of_format (s : Array Char) (pos : Nat)
    (p : Char → Bool) (base offset : Nat) (kind : String)
    (hfmt : intFormat s pos = (p,base,offset,kind))
    (hp : ∀ c, BaseDigit base c ↔ p c = true) (hstart : pos+offset ≤ s.size)
    {v : Int} {q : { q : Nat // pos < q }}
    (h : lexUnsigned s pos = .ok (v,q)) :
    ∃ ds, ∃ n : Nat, v = (n : Int) ∧ ds ≠ [] ∧ Digits base ds n ∧
      Suffix.toList s (pos+offset) = ds ++ Suffix.toList s q.val ∧
      Boundary (BaseDigit base) (Suffix.toList s q.val) ∧ q.val ≤ s.size := by
  simp only [lexUnsigned,hfmt] at h
  split at h
  · cases h
  · rename_i hnonempty
    obtain ⟨ds,n,hstr,hd,hs,hb,hbound⟩ := takeWhile_digits p base s (pos+offset) hp hstart
    have hne : ds ≠ [] := by
      intro he
      simp [hstr,he] at hnonempty
    simp only [hstr,parseNatBase_of_digits hd,Except.ok.injEq,Prod.mk.injEq] at h
    have hq : (takeWhile p s (pos+offset) "").2 = q.val := congrArg Subtype.val h.2
    exact ⟨ds,n,h.1.symm,hne,hd,by simpa [hq] using hs,
      by simpa [hq] using hb,by simpa [hq] using hbound⟩

/-- Successful unsigned lexing has an independent magnitude derivation and
never returns a position past the input. -/
theorem lexUnsigned_sound {s : Array Char} {pos : Nat} (hpos : pos ≤ s.size)
    {v : Int} {q : { q : Nat // pos < q }}
    (h : lexUnsigned s pos = .ok (v,q)) :
    ∃ n : Nat, v = (n : Int) ∧ Magnitude (Suffix.toList s pos) n (Suffix.toList s q.val) ∧
      q.val ≤ s.size := by
  by_cases hh : pos+1 < s.size && s[pos]! == '0' && s[pos+1]! == 'x'
  · have hh' := hh
    simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hh'
    obtain ⟨⟨hb,h0⟩,hx⟩ := hh'
    have hs := suffix_two s pos hb
    rw [h0,hx] at hs
    have hf : intFormat s pos = (isHexDigit,16,2,"hexadecimal") := by
      simp only [intFormat,hh,ite_true]
    obtain ⟨ds,n,hv,hne,hd,ht,hstop,hbound⟩ :=
      lexUnsigned_sound_of_format s pos isHexDigit 16 2 "hexadecimal" hf baseDigit16_iff
        (by omega) h
    refine ⟨n,hv,?_,hbound⟩
    rw [hs,ht]
    exact .hex hne hd hstop
  · by_cases ho : pos+1 < s.size && s[pos]! == '0' && s[pos+1]! == 'o'
    · have ho' := ho
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at ho'
      obtain ⟨⟨hb,h0⟩,hochar⟩ := ho'
      have hs := suffix_two s pos hb
      rw [h0,hochar] at hs
      have hf : intFormat s pos = (isOctDigit,8,2,"octal") := by
        simp [intFormat,hh,ho]
      obtain ⟨ds,n,hv,hne,hd,ht,hstop,hbound⟩ :=
        lexUnsigned_sound_of_format s pos isOctDigit 8 2 "octal" hf baseDigit8_iff
          (by omega) h
      refine ⟨n,hv,?_,hbound⟩
      rw [hs,ht]
      exact .octal hne hd hstop
    · have hf : intFormat s pos = (isDigit,10,0,"integer") := by
        simp [intFormat,hh,ho]
      obtain ⟨ds,n,hv,hne,hd,ht,hstop,hbound⟩ :=
        lexUnsigned_sound_of_format s pos isDigit 10 0 "integer" hf baseDigit10_iff
          (by simpa using hpos) h
      have hn : ¬ RadixPrefix (Suffix.toList s pos) := by
        intro hpref
        unfold RadixPrefix at hpref
        split at hpref
        · rename_i rest hs
          obtain ⟨hb,h0,hx,_⟩ := suffix_two_inv hs
          apply hh
          simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
          exact ⟨⟨hb,h0⟩,hx⟩
        · rename_i rest hs
          obtain ⟨hb,h0,hochar,_⟩ := suffix_two_inv hs
          apply ho
          simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
          exact ⟨⟨hb,h0⟩,hochar⟩
        · cases hpref
      refine ⟨n,hv,?_,hbound⟩
      have ht' : Suffix.toList s pos = ds ++ Suffix.toList s q.val := by simpa using ht
      rw [ht'] at hn ⊢
      exact .decimal hne hd hstop hn

theorem magnitude_starts_digit {input rest : List Char} {n : Nat}
    (h : Magnitude input n rest) :
    ∃ c cs, input = c :: cs ∧ isDigit c = true := by
  cases h with
  | @decimal ds n rest hne hd hb hp =>
      cases ds with
      | nil => exact (hne rfl).elim
      | cons c cs =>
          cases hd with
          | cons hc ht => exact ⟨c,cs ++ rest,rfl,(baseDigit10_iff c).mp ⟨_,hc⟩⟩
  | hex => exact ⟨'0',_,rfl,rfl⟩
  | octal => exact ⟨'0',_,rfl,rfl⟩

theorem suffix_one_inv {s : Array Char} {pos : Nat} {c : Char} {rest : List Char}
    (h : Suffix.toList s pos = c :: rest) :
    pos < s.size ∧ s[pos]! = c ∧ Suffix.toList s (pos+1) = rest := by
  have hl := congrArg List.length h
  rw [Suffix.toList_size] at hl
  simp only [List.length_cons] at hl
  have hb : pos < s.size := by omega
  rw [Suffix.toList_getElem s pos hb] at h
  exact ⟨hb,by simpa only [getElem!_pos s pos hb] using (List.cons.inj h).1,(List.cons.inj h).2⟩

theorem digit_ne {c d : Char} (hc : isDigit c = true) (hd : isDigit d = false) : c ≠ d := by
  intro he
  subst d
  rw [hd] at hc
  contradiction

/-- The signed integer scanner emits precisely a natural/negative Lexeme. -/
theorem lexInt_sound {s : Array Char} {pos : Nat} (hpos : pos ≤ s.size)
    {tok : Token} {q : { q : Nat // pos < q }}
    (h : lexInt s pos = .ok (tok,q)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q.val) ∧ q.val ≤ s.size := by
  unfold lexInt at h
  split at h
  · rename_i hminus
    have hh := hminus
    simp only [Bool.and_eq_true,decide_eq_true_iff,beq_iff_eq] at hh
    obtain ⟨hb,hm⟩ := hh
    cases hu : lexUnsigned s (pos+1) with
    | error e => simp [hu] at h
    | ok result =>
      obtain ⟨v,p⟩ := result
      simp only [hu] at h
      cases h
      obtain ⟨n,hv,hmag,hbound⟩ := lexUnsigned_sound (by omega) hu
      subst v
      constructor
      · have hs := Suffix.toList_getElem s pos hb
        have hm' : s[pos] = '-' := by simpa only [getElem!_pos s pos hb] using hm
        rw [hs,hm']
        exact .negative hmag
      · exact hbound
  · cases hu : lexUnsigned s pos with
    | error e => simp [hu] at h
    | ok result =>
      obtain ⟨v,p⟩ := result
      simp only [hu] at h
      cases h
      obtain ⟨n,hv,hmag,hbound⟩ := lexUnsigned_sound hpos hu
      subst v
      exact ⟨.natural hmag,hbound⟩

/-- Completeness of signed integer scanning for a nonnegative magnitude. -/
theorem lexInt_natural_complete {s : Array Char} {pos : Nat} {input rest : List Char} {n : Nat}
    (hinput : Suffix.toList s pos = input) (hm : Magnitude input n rest)
    (hpos : pos ≤ s.size) :
    ∃ q : { q : Nat // pos < q }, lexInt s pos = .ok (.intLit (n : Int),q) ∧
      Suffix.toList s q.val = rest ∧ q.val ≤ s.size := by
  obtain ⟨c,cs,hcs,hdigit⟩ := magnitude_starts_digit hm
  have hinv := suffix_one_inv (hinput.trans hcs)
  have hminus : (decide (pos < s.size) && s[pos]! == '-') = false := by
    have hn : c ≠ '-' := digit_ne hdigit rfl
    have hc : s[pos] = c := by simpa only [getElem!_pos s pos hinv.1] using hinv.2.1
    simp [hinv.1,hc,hn]
  obtain ⟨q,hq,ht,hb⟩ := lexUnsigned_complete hinput hm hpos
  refine ⟨q,?_,ht,hb⟩
  simp only [lexInt,hminus,Bool.false_eq_true,ite_false,hq]

/-- Completeness for an adjacent minus followed by a valid magnitude. -/
theorem lexInt_negative_complete {s : Array Char} {pos : Nat} {input rest : List Char} {n : Nat}
    (hinput : Suffix.toList s pos = '-' :: input) (hm : Magnitude input n rest)
    (hpos : pos ≤ s.size) :
    ∃ q : { q : Nat // pos < q }, lexInt s pos = .ok (.intLit (-(n : Int)),q) ∧
      Suffix.toList s q.val = rest ∧ q.val ≤ s.size := by
  obtain ⟨hstart,hminus,htail⟩ := suffix_one_inv hinput
  have hminus' : s[pos] = '-' := by simpa only [getElem!_pos s pos hstart] using hminus
  have hneg : (decide (pos < s.size) && s[pos]! == '-') = true := by simp [hstart,hminus']
  obtain ⟨q,hq,ht,hb⟩ := lexUnsigned_complete htail hm (by omega)
  refine ⟨⟨q.val,by have := q.property; omega⟩,?_,ht,hb⟩
  simp only [lexInt,hneg,ite_true,hq]

theorem isAlpha_false_of_digit {c : Char} (hc : isDigit c = true) : isAlpha c = false := by
  cases ha : isAlpha c with
  | false => rfl
  | true =>
    have hd := (decimal_iff_digit c).mpr hc
    have hl := (char_le_nat '0' c).mp hd.1
    have hu := (char_le_nat c '9').mp hd.2
    have hw := (letter_iff_alpha c).mpr ha
    rcases hw with hw | hw
    · have := (char_le_nat 'A' c).mp hw.1
      digit_omega
    · have := (char_le_nat 'a' c).mp hw.1
      digit_omega

theorem identStart_false_of_digit {c : Char} (hc : isDigit c = true) :
    (isAlpha c || c == '_') = false := by
  have hn : c ≠ '_' := digit_ne hc rfl
  simp [isAlpha_false_of_digit hc,hn]

/-- Numeral scanner dispatch is also the executable significant-token branch. -/
theorem lexToken_of_numeric (s : Array Char) (pos : Nat) (hpos : pos < s.size)
    (hnum : (isDigit s[pos] || s[pos] == '-') = true) :
    lexToken s pos hpos = lexInt s pos := by
  unfold lexToken
  dsimp only
  split
  all_goals try (simp_all [isDigit]; done)
  have hw : (isAlpha s[pos] || s[pos] == '_') = false := by
    simp only [Bool.or_eq_true,beq_iff_eq] at hnum
    rcases hnum with hd | hm
    · exact identStart_false_of_digit hd
    · rw [hm]
      rfl
  simp only [hw,Bool.false_eq_true,ite_false,hnum,ite_true]

end LeanFzn.Parser.Lexer








/-
Purpose: Decimal rendering facts used to verify solution output tokenization.
Dependencies: Parser.Lexer provides the executable digit decoder; Lean's
natural-number rendering lemmas characterize decimal digit strings.
DAG: Lexer -> LexerRender -> Integration.Emit round-trip proofs.
-/
import LeanFzn.Parser.SolutionRender
import Lean
import Init.Data.Nat.ToString

namespace LeanFzn.Parser.Lexer

/-- The decimal digit predicate agrees with Lean's standard digit predicate. -/
theorem isDigit_eq_char_isDigit (c : Char) : isDigit c = c.isDigit := by
  rfl

/-- Every character printed for a natural number is a decimal digit. -/
theorem isDigit_of_mem_nat_repr {n : Nat} {c : Char}
    (h : c ∈ n.repr.toList) : isDigit c = true := by
  rw [Nat.toList_repr] at h
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- The lexer's base decoder is the standard decimal decoder on digit strings. -/
theorem parseNatBase_ten_eq_ofDigitChars (s : String)
    (h : ∀ c ∈ s.toList, isDigit c = true) :
    parseNatBase 10 s = Nat.ofDigitChars 10 s.toList 0 := by
  unfold parseNatBase
  rw [String.foldl_eq_foldl_toList, Nat.ofDigitChars_eq_foldl]
  generalize s.toList = cs at *
  suffices hfold : ∀ init, cs.foldl (fun n c => n * 10 + digitValue c) init =
      cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) init by
    exact hfold 0
  induction cs with
  | nil => intro init; rfl
  | cons c cs ih =>
    intro init
    simp only [List.foldl_cons]
    rw [show init * 10 + digitValue c = 10 * init + (c.toNat - '0'.toNat) by
      simp only [digitValue, h c List.mem_cons_self, ite_true]
      omega]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) _

/-- Decimal rendering is read back as the original natural number by the lexer. -/
theorem parseNatBase_nat_repr (n : Nat) : parseNatBase 10 n.repr = n := by
  rw [parseNatBase_ten_eq_ofDigitChars _ (fun c hc => isDigit_of_mem_nat_repr hc)]
  simp only [Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]


/-- A word followed by a space is consumed exactly, independently of context. -/
theorem takeWhile_word (p : Char → Bool) (cs : List Char)
    (hall : ∀ c ∈ cs, p c = true) (hspace : p ' ' = false)
    (pre tail : Array Char) (acc : String) :
    takeWhile p (pre ++ cs.toArray ++ #[' '] ++ tail) pre.size acc =
      (acc ++ String.ofList cs, pre.size + cs.length) := by
  induction cs generalizing pre acc with
  | nil =>
    rw [takeWhile.eq_def]
    simp [hspace]
  | cons c cs ih =>
    have hc := hall c List.mem_cons_self
    have hcs : ∀ d ∈ cs, p d = true := fun d hd => hall d (List.mem_cons_of_mem _ hd)
    rw [List.toArray_cons, takeWhile.eq_def]
    have hlt : pre.size < (pre ++ (#[c] ++ cs.toArray) ++ #[' '] ++ tail).size := by
      simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
      omega
    simp only [dif_pos hlt]
    have hget : (pre ++ (#[c] ++ cs.toArray) ++ #[' '] ++ tail)[pre.size] = c := by
      simp (disch := omega) [Array.getElem_append]
    simp only [hget, hc, ite_true]
    have hh := ih hcs (pre.push c) (acc.push c)
    rw [Array.push_eq_append] at hh
    simp only [Array.size_push, List.length_cons, String.ofList_cons,
      String.push_eq_append, String.append_assoc, Nat.add_assoc] at hh ⊢
    simpa only [Array.append_assoc, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh


theorem input_get_head (pre : Array Char) (c : Char) (tail : Array Char) :
    (pre ++ #[c] ++ tail)[pre.size]'(by simp; omega) = c := by
  simp (disch := omega) [Array.getElem_append]

theorem input_getElem!_head (pre : Array Char) (c : Char) (tail : Array Char) :
    (pre ++ #[c] ++ tail)[pre.size]! = c := by
  rw [getElem!_pos _ _ (by simp; omega)]
  exact input_get_head pre c tail

/-- Whitespace-free word scanning with an arbitrary left context. -/
theorem lexToken_word (w : String) (c : Char) (cs : List Char)
    (hw : w.toList = c :: cs)
    (hc : (isAlpha c || c == '_') = true)
    (hcs : ∀ d ∈ cs, isIdentChar d = true)
    (hr : reservedNonFzn.contains w = false)
    (pre tail : Array Char) (h : pre.size < (pre ++ w.toList.toArray ++ #[' '] ++ tail).size) :
    lexToken (pre ++ w.toList.toArray ++ #[' '] ++ tail) pre.size h =
      .ok ((keywordToken w).getD (.ident w),
        ⟨pre.size + w.length, by
          have : 0 < w.length := by rw [← String.length_toList, hw]; simp
          omega⟩) := by
  have hw' : w = String.ofList (c :: cs) := by
    exact String.toList_inj.mp (by simpa using hw)
  have ht := takeWhile_word isIdentChar cs hcs (by decide) (pre.push c) tail (String.singleton c)
  have htake : takeWhile isIdentChar (pre ++ w.toList.toArray ++ #[' '] ++ tail)
      (pre.size + 1) (String.singleton c) = (w, pre.size + w.length) := by
    rw [hw, List.toArray_cons]
    rw [Array.push_eq_append] at ht
    simp only [Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add] at ht
    have hlen : w.length = cs.length + 1 := by
      rw [← String.length_toList, hw]; rfl
    rw [hlen, hw', String.ofList_cons]
    simpa only [Array.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  have hin : pre ++ w.toList.toArray ++ #[' '] ++ tail =
      pre ++ #[c] ++ (cs.toArray ++ #[' '] ++ tail) := by
    rw [hw, List.toArray_cons]
    simp only [Array.append_assoc]
  have hget : (pre ++ w.toList.toArray ++ #[' '] ++ tail)[pre.size] = c := by
    simp only [hin]
    exact input_get_head pre c _
  unfold lexToken
  simp only [hget]
  split <;> try { simp_all [isAlpha] }
  simp only [hc, ite_true, htake]
  cases hk : keywordToken w with
  | some t => simp only [hk, Option.getD]; rfl
  | none => simp only [hk, hr, Bool.false_eq_true, ite_false, Option.getD]; rfl



theorem input_getElem!_word_first (pre tail : Array Char) (c : Char) (cs : List Char) :
    (pre ++ (c :: cs).toArray ++ #[' '] ++ tail)[pre.size]! = c := by
  rw [List.toArray_cons]
  simpa only [Array.append_assoc] using
    input_getElem!_head pre c (cs.toArray ++ #[' '] ++ tail)

private theorem intFormat_digits (cs : List Char) (hne : cs ≠ [])
    (hall : ∀ c ∈ cs, isDigit c = true) (pre tail : Array Char) :
    intFormat (pre ++ cs.toArray ++ #[' '] ++ tail) pre.size =
      (isDigit, 10, 0, "integer") := by
  cases cs with
  | nil => contradiction
  | cons c cs =>
    cases cs with
    | nil =>
      have hh := input_getElem!_head (pre.push c) ' ' tail
      rw [Array.push_eq_append] at hh
      simp only [Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil, Nat.zero_add] at hh
      have hh' : (pre ++ [c].toArray ++ #[' '] ++ tail)[pre.size+1]! = ' ' := hh
      unfold intFormat
      simp only [hh', show (' ' == 'x') = false from rfl,
        show (' ' == 'o') = false from rfl,
        Bool.and_false, Bool.false_eq_true, ite_false]
    | cons d cs =>
      have hd := hall d (by simp)
      have hdx : d ≠ 'x' := by intro he; subst d; contradiction
      have hdo : d ≠ 'o' := by intro he; subst d; contradiction
      have hh := input_getElem!_word_first (pre.push c) tail d cs
      rw [Array.push_eq_append] at hh
      simp only [Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil, Nat.zero_add] at hh
      have heq : pre ++ (c :: d :: cs).toArray ++ #[' '] ++ tail =
          (pre ++ #[c]) ++ (d :: cs).toArray ++ #[' '] ++ tail := by
        rw [List.toArray_cons c]
        simp only [Array.append_assoc]
      simp only [heq, intFormat]
      -- The position is the original prefix size, not the shifted one.
      simp only [hh, beq_eq_false_iff_ne.mpr hdx, beq_eq_false_iff_ne.mpr hdo,
        Bool.and_false, Bool.false_eq_true, ite_false]

/-- The unsigned lexer reads every printed natural number in any token context. -/
theorem lexUnsigned_nat_repr (n : Nat) (pre tail : Array Char) :
    lexUnsigned (pre ++ n.repr.toList.toArray ++ #[' '] ++ tail) pre.size =
      .ok ((n : Int), ⟨pre.size + n.repr.length, by
        have := Nat.length_repr_pos (n := n); omega⟩) := by
  have hne : n.repr.toList ≠ [] := by
    rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
  have hf := intFormat_digits n.repr.toList hne
    (fun c hc => isDigit_of_mem_nat_repr hc) pre tail
  have ht := takeWhile_word isDigit n.repr.toList
    (fun c hc => isDigit_of_mem_nat_repr hc) (by decide) pre tail ""
  simp only [String.empty_append, String.ofList_toList, String.length_toList] at ht
  unfold lexUnsigned
  rw [hf]
  simp only [Nat.add_zero, ht, parseNatBase_nat_repr]
  have hn : n.repr.isEmpty = false := by
    simp [String.isEmpty_iff, Nat.repr_ne_empty]
  simp only [hn, Bool.false_eq_true]
  split
  · contradiction
  · rfl



/-- Indexed variant used after consuming a leading minus sign. -/
theorem lexUnsigned_nat_repr_at (n : Nat) (pre tail : Array Char) (pos : Nat)
    (hpos : pos = pre.size) :
    lexUnsigned (pre ++ n.repr.toList.toArray ++ #[' '] ++ tail) pos =
      .ok ((n : Int), ⟨pos + n.repr.length, by
        have := Nat.length_repr_pos (n := n); omega⟩) := by
  subst pos
  exact lexUnsigned_nat_repr n pre tail

/-- The signed integer lexer is a left inverse to arbitrary integer rendering. -/
theorem lexInt_toString (i : Int) (pre tail : Array Char) :
    lexInt (pre ++ (toString i).toList.toArray ++ #[' '] ++ tail) pre.size =
      .ok (.intLit i, ⟨pre.size + (toString i).length, by
        cases i with
        | ofNat n => have := Nat.length_repr_pos (n := n); change pre.size < pre.size + n.repr.length; omega
        | negSucc n =>
          change pre.size < pre.size + ("-" ++ (n+1).repr).length
          rw [String.length_append, show "-".length = 1 from rfl]
          omega⟩) := by
  cases i with
  | ofNat n =>
    change lexInt (pre ++ n.repr.toList.toArray ++ #[' '] ++ tail) pre.size = _
    have hne : n.repr.toList ≠ [] := by rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have hc : isDigit c = true := isDigit_of_mem_nat_repr (by rw [hcs]; simp)
    have hcneg : c ≠ '-' := by intro he; subst c; contradiction
    have hh : (pre ++ n.repr.toList.toArray ++ #[' '] ++ tail)[pre.size]! = c := by
      rw [hcs]; exact input_getElem!_word_first pre tail c cs
    unfold lexInt
    simp only [hh, beq_eq_false_iff_ne.mpr hcneg, Bool.and_false,
      Bool.false_eq_true, ite_false, lexUnsigned_nat_repr]
    rfl
  | negSucc n =>
    change lexInt (pre ++ ("-" ++ (n+1).repr).toList.toArray ++ #[' '] ++ tail) pre.size = _
    have heq : pre ++ ("-" ++ (n+1).repr).toList.toArray ++ #[' '] ++ tail =
        (pre.push '-') ++ (n+1).repr.toList.toArray ++ #[' '] ++ tail := by
      rw [String.toList_append, show "-".toList = ['-'] from rfl,
        List.singleton_append, List.toArray_cons, Array.push_eq_append]
      simp only [Array.append_assoc]
    have hh : (pre ++ ("-" ++ (n+1).repr).toList.toArray ++ #[' '] ++ tail)[pre.size]! = '-' := by
      rw [heq, Array.push_eq_append]
      simpa only [Array.append_assoc] using input_getElem!_head pre '-' ((n+1).repr.toList.toArray ++ #[' '] ++ tail)
    unfold lexInt
    have hlt : pre.size < (pre ++ ("-" ++ (n+1).repr).toList.toArray ++ #[' '] ++ tail).size := by
      rw [heq]
      simp only [Array.size_append, Array.size_push, List.size_toArray,
        List.length_cons, List.length_nil]
      omega
    simp only [hlt, hh, beq_self_eq_true, decide_true, Bool.true_and, ite_true]
    have hu := lexUnsigned_nat_repr_at (n+1) (pre.push '-') tail (pre.size+1)
      (by simp only [Array.size_push])
    rw [← heq] at hu
    rw [hu]
    apply congrArg Except.ok
    apply Prod.ext
    · change Token.intLit (-((n+1 : Nat) : Int)) = Token.intLit (Int.negSucc n)
      congr 1
    · apply Subtype.ext
      change pre.size + 1 + (n+1).repr.length = pre.size + ("-" ++ (n+1).repr).length
      rw [String.length_append, show "-".length = 1 from rfl]
      omega



private theorem decimalDigit_not_alpha {c : Char} (h : isDigit c = true) : isAlpha c = false := by
  simp only [isDigit, isAlpha, Char.le_def, UInt32.le_iff_toNat_le, Bool.and_eq_true,
    Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_true_eq,
    decide_eq_false_iff_not] at *
  change 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 at h
  change (65 ≤ c.val.toNat → ¬ c.val.toNat ≤ 90) ∧
    (97 ≤ c.val.toNat → ¬ c.val.toNat ≤ 122)
  constructor <;> intro hh <;> omega

private theorem numeric_head (i : Int) : ∃ c cs,
    (toString i).toList = c :: cs ∧ (isDigit c || c == '-') = true ∧
    isAlpha c = false ∧ (c == '_') = false := by
  cases i with
  | ofNat n =>
      have hne : n.repr.toList ≠ [] := by rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
      obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
      have hc : isDigit c = true := isDigit_of_mem_nat_repr (by rw [hcs]; simp)
      refine ⟨c, cs, hcs, by simp [hc], decimalDigit_not_alpha hc, ?_⟩
      apply beq_eq_false_iff_ne.mpr
      intro h
      subst c
      contradiction
  | negSucc n =>
      refine ⟨'-', (n+1).repr.toList, ?_, by decide, by decide, by decide⟩
      change ("-" ++ (n+1).repr).toList = _
      rw [String.toList_append]
      rfl

/-- Every printed integer is consumed as the intended integer token. -/
theorem lexToken_toString (i : Int) (pre tail : Array Char)
    (h : pre.size < (pre ++ (toString i).toList.toArray ++ #[' '] ++ tail).size) :
    lexToken (pre ++ (toString i).toList.toArray ++ #[' '] ++ tail) pre.size h =
      .ok (.intLit i, ⟨pre.size + (toString i).length, by
        cases i with
        | ofNat n => have := Nat.length_repr_pos (n := n); change pre.size < pre.size + n.repr.length; omega
        | negSucc n =>
          change pre.size < pre.size + ("-" ++ (n+1).repr).length
          rw [String.length_append, show "-".length = 1 from rfl]
          omega⟩) := by
  obtain ⟨c, cs, hcs, hnum, halpha, hunder⟩ := numeric_head i
  have hin : pre ++ (toString i).toList.toArray ++ #[' '] ++ tail =
      pre ++ #[c] ++ (cs.toArray ++ #[' '] ++ tail) := by
    rw [hcs, List.toArray_cons]
    simp only [Array.append_assoc]
  have hget : (pre ++ (toString i).toList.toArray ++ #[' '] ++ tail)[pre.size] = c := by
    simp only [hin]
    exact input_get_head pre c _
  unfold lexToken
  simp only [hget]
  split <;> try { simp_all [isDigit] }
  simp only [halpha, hunder, Bool.false_or, Bool.false_eq_true,
    ite_false, hnum, ite_true]
  exact lexInt_toString i pre tail

/-- Printed naturals cannot introduce a physical newline. -/
theorem nat_repr_noNewline (n : Nat) : '\n' ∉ n.repr.toList := by
  intro h
  have := isDigit_of_mem_nat_repr h
  contradiction

/-- Printed integers cannot introduce a physical newline. -/
theorem int_toString_noNewline (i : Int) : '\n' ∉ (toString i).toList := by
  cases i with
  | ofNat n => exact nat_repr_noNewline n
  | negSucc n =>
    change '\n' ∉ ("-" ++ (n+1).repr).toList
    simp only [String.toList_append, List.mem_append, List.mem_cons, List.mem_singleton]
    simpa using nat_repr_noNewline (n+1)

/-- A printable name contains no physical newlines. -/
theorem printableSolutionName_noNewline (s : String) (h : PrintableSolutionName s) :
    '\n' ∉ s.toList := by
  obtain ⟨⟨c, cs, heq, hfirst, htail⟩, _, _⟩ := h
  rw [heq]
  intro hm
  rcases List.mem_cons.mp hm with heq | hm
  · subst c; contradiction
  · have hd := htail '\n' hm
    contradiction

/-- Every printable solution token is newline-free. -/
theorem renderSolutionToken_noNewline (t : Token) (h : PrintableSolutionToken t) :
    '\n' ∉ (renderSolutionToken t).toList := by
  cases t with
  | ident s => exact printableSolutionName_noNewline s h
  | intLit i => exact int_toString_noNewline i
  | boolLit b => cases b <;> decide
  | lParen | rParen | lBrack | rBrack | lBrace | rBrace | comma | semi | eq | dotDot => decide
  | _ => cases h

/-- Canonical solution token strings cannot hide a separator on another line. -/
theorem renderSolutionTokens_noNewline (ts : List Token)
    (h : ∀ t ∈ ts, PrintableSolutionToken t) :
    '\n' ∉ (renderSolutionTokens ts).toList := by
  induction ts with
  | nil => decide
  | cons t ts ih =>
    simp only [renderSolutionTokens, String.toList_append, List.mem_append,
      not_or, List.mem_cons, List.mem_singleton]
    exact ⟨⟨renderSolutionToken_noNewline t (h t List.mem_cons_self), by decide⟩,
      ih (fun t ht => h t (List.mem_cons_of_mem _ ht))⟩

end LeanFzn.Parser.Lexer

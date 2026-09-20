import solver.Emit.Roundtrip

namespace LeanFzn.Solver

open LeanFzn.Lexer

-- position transport for lexToken calls (proof-irrelevant bounds):
theorem lexToken_pos_trans {a : Array Char} {q1 q2 : Nat} (hqq : q1 = q2)
    (h1 : q1 < a.size) (h2 : q2 < a.size) :
    lexToken a q1 h1 = lexToken a q2 h2 := by
  subst hqq
  rfl

-- the bool token at the ws-length position via the segment lemma:
example {nm tl : List Char} {b : Bool} (htl : tl ≠ []) :
    lexToken ((nm ++ [' ', '=', ' '] ++ boolLitChars b ++ [';'] ++ tl).toArray)
        (nm.length + 3) (entry_bound (j := 3) (by omega) htl)
      = .ok (.boolLit b, ⟨(nm ++ [' ', '=', ' '] ++ boolLitChars b).length, by
          have hw : (([' ', '=', ' '] : List Char)).length = 3 := rfl
          have hbpos : (0 : Nat) < (boolLitChars b).length := by
            cases b <;> simp [boolLitChars]
          have h1 : (nm ++ [' ', '=', ' '] ++ boolLitChars b).length
              = nm.length + 3 + (boolLitChars b).length := by
            rw [List.length_append, List.length_append, hw]
          omega⟩) := by
  have hbne : boolLitChars b ≠ [] := boolLitChars_ne b
  obtain ⟨c, cs, hbc⟩ : ∃ c cs, boolLitChars b = c :: cs := by
    cases hbc' : boolLitChars b with
    | nil => exact absurd hbc' hbne
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hbpos : (0 : Nat) < (boolLitChars b).length := by
    cases b <;> simp [boolLitChars]
  have hctf : b = true ∧ c = 't' ∨ b = false ∧ c = 'f' := by
    cases b with
    | true =>
        rw [boolLitChars] at hbc
        injection hbc with h1 _
        exact Or.inl ⟨rfl, h1.symm⟩
    | false =>
        rw [boolLitChars] at hbc
        injection hbc with h1 _
        exact Or.inr ⟨rfl, h1.symm⟩
  -- the word-split array facts:
  have hW : (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length = nm.length + 3 := by
    rw [List.length_append]
    rfl
  have harr : ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
      ++ (boolLitChars b ++ ((';' : Char) :: tl))).toArray
      = ((nm ++ [' ', '=', ' '] ++ boolLitChars b ++ [';'] ++ tl)).toArray := by
    apply congrArg List.toArray
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- the head read of the word (prim read at ws.length):
  have hread : ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
      ++ (boolLitChars b))[(nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length] = c := by
    rw [hbc]
    exact composite_read_at_join
  -- the tail membership (the drop past the word head is the word tail):
  have hdrop : ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
      ++ (boolLitChars b)).drop
      ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length + 1)
      = (boolLitChars b).drop 1 := by
    rw [hbc]
    exact entry_lit_drop_rest
  -- the segment lemma itself:
  have hseg := lexToken_bool_segment
    (x := (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]) ++ boolLitChars b)
    (y := ((';' : Char) :: tl))
    (q := (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length)
    (hle := by
      show (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length
          < ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
            ++ boolLitChars b).length
      rw [List.length_append]
      show nm.length + 3 < nm.length + 3 + (boolLitChars b).length
      omega)
    (hstart := by
      have hhead : (boolLitChars b)[0] = c := by
        rw [hbc]
        rfl
      rw [show ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
        ++ boolLitChars b)[(nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length]
        = (boolLitChars b)[0] from hread]
      rw [hhead]
      rcases hctf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (hall := by
      intro ch hch
      rw [hdrop] at hch
      have hmem : ch ∈ boolLitChars b := List.mem_of_mem_drop hch
      exact boolLitChars_ident b ch hmem)
    (hfail := by
      intro ch hc
      have hc' : ch = ';' := by
        injection hc with hcc
        exact hcc.symm
      subst hc'
      decide)
    (hkw := by
      have hdrop0 : ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
        ++ boolLitChars b).drop
        ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length)
        = boolLitChars b := entry_lit_drop
      rw [hdrop0]
      exact keywordToken_bool b)
  -- transport along the array equality and the position spelling:
  rw [lexToken_eq_trans harr (nm.length + 3) (by
      rw [show ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
          ++ ((boolLitChars b) ++ ((';' : Char) :: tl))).toArray.size
          = ((nm ++ [' ', '=', ' '] ++ boolLitChars b ++ [';'] ++ tl)).toArray.size from by
        rw [harr]]) (entry_bound (j := 3) (by omega) htl)] at hseg
  sorry

end LeanFzn.Solver

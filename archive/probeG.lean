import solver.Emit
open LeanFzn LeanFzn.Solver LeanFzn.Lexer

/-- The tokenizer walk past the join is the tail's walk, under the
    walk-level premise that (a) every scan from every position the
    walk visits stops inside `t` (`htw`), and (b) the tail's lexing
    never errors from `k` (`hnoerr` — needed because the lexer's
    error MESSAGES embed the absolute position, so error results
    genuinely differ between `s ++ t` and `t`). -/
theorem tokenizeAux_append_right_ok {s t : Array Char}
    (htw : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p t q "").2 < t.size)
    (hnoerr : ∀ (k : Nat) (h : k < t.size),
      (lexToken t k h).isOk = true)
    (hnostr : ∀ (k : Nat) (h : k < t.size), t[k]'h ≠ '"') :
    ∀ (k : Nat) (acc : Array Token),
      tokenizeAux (s ++ t) (s.size + k) acc
        = tokenizeAux t k acc := by
  intro k acc
  induction k, acc using tokenizeAux.induct (s := t) with
  | case1 k acc hsk hpos ih =>
      -- the trivia skip at the offset
      have hskip : skipTrivia (s ++ t) (s.size + k)
          = s.size + skipTrivia t k :=
        skipTrivia_append_right
      -- both sides unfold with aligned trivia skips
      rw [tokenizeAux.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [tokenizeAux.eq_def (s := t) (pos := k)]
      -- the goal: two do-blocks with the shared structure. Both
      -- trivia skips are s.size + q vs q; both bounds agree; the
      -- token agrees by lexToken_append_right_ok (needs the
      -- success hypothesis). Split the ifs.
      -- rewrite the s++t side's trivia skip to the offset form
      simp only [] at *
      -- substitute the skip
      rw [hskip]
      -- both bounds: (s.size + skipTrivia t k < s.size + t.size) iff
      -- (skipTrivia t k < t.size)
      have hbound : s.size + hsk < (s ++ t).size := by
        rw [Array.size_append]
        omega
      rw [dif_pos hbound, dif_pos hpos]
      -- the token at the offset agrees (success-transport)
      have hsklt : hsk < t.size := hpos
      cases htok : lexToken t hsk hsklt with
      | ok tp =>
          obtain ⟨tok, p', hp'⟩ := tp
          have hoffset : lexToken (s ++ t) (s.size + hsk) hbound
              = .ok (tok, ⟨s.size + p', by omega⟩) :=
            lexToken_append_right_ok (s := s) (t := t) (k := hsk)
              hsklt (fun p q _ => htw p q) (hnostr hsk hsklt) htok
          rw [hoffset]
          -- hsk < p' from the token's structure: lexToken's tokens
          -- all end strictly after the start. Derive by casing the
          -- lexToken definition on the t side (htok).
          have hgtp : hsk < p' := by
            have hdef := htok
            rw [lexToken.eq_def (s := t) (pos := hsk) (h := hsklt)] at hdef
            simp only [] at hdef
            -- split the whole match/lexUnsigned structure at once:
            -- every branch puts the end position > hsk. Reduce by
            -- `split at hdef` repeatedly and use omega on the
            -- resulting position equations.
            repeat' (first | split at hdef | skip)
            all_goals
              first
              | (injection hdef with hpair; obtain ⟨_, hpos'⟩ :=
                  Prod.mk.inj hpair; injection hpos' with hv; omega)
              | omega
          exact ih tok p' hgtp
      | error e =>
          -- the error case is impossible: hnoerr says the t-side
          -- lexToken at any in-bounds position succeeds
          exfalso
          have hsome := hnoerr hsk hsklt
          rw [htok] at hsome
          exact Bool.noConfusion hsome
  | case2 k acc hsk hpos =>
      have hskip : skipTrivia (s ++ t) (s.size + k)
          = s.size + skipTrivia t k :=
        skipTrivia_append_right
      rw [tokenizeAux.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [tokenizeAux.eq_def (s := t) (pos := k)]
      simp only [] at *
      rw [hskip]
      -- both sides' trivia runs are past the end: pure acc
      have hbound : ¬ (s.size + hsk < (s ++ t).size) := by
        rw [Array.size_append]
        omega
      rw [dif_neg hbound, dif_neg hpos]

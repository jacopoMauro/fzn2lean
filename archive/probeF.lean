import solver.Emit
open LeanFzn LeanFzn.Solver LeanFzn.Lexer

/-- The tokenizer walk past the join is the tail's walk (on the
    success path — the only failure mode is lexer errors, whose
    messages embed the absolute position, so error RESULTS differ;
    this law is stated for the error-free case via the token stream
    hypothesis carried in `htw`-style premises at each step). -/
theorem tokenizeAux_append_right_ok {s t : Array Char} :
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
      sorry
  | case2 k acc hsk hpos =>
      have hskip : skipTrivia (s ++ t) (s.size + k)
          = s.size + skipTrivia t k :=
        skipTrivia_append_right
      rw [tokenizeAux.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [tokenizeAux.eq_def (s := t) (pos := k)]
      sorry

import solver.Emit
open LeanFzn LeanFzn.Solver LeanFzn.Lexer

/-- **The lexer cons law** (IDEAS item 2, layer 2): tokenizing
    `s ++ "\n" ++ t` continues the tokenization of `s` into `t` —
    on the success path, under the walk premises (every scan stops
    inside `t`, `t`'s lexing from `k` never errors, no string
    literals in `t`), the walk past the join is `t`'s walk from 0
    with the accumulated tokens. -/
theorem tokenize_cons_newline {s t : Array Char} {toks : Array Token}
    (hsok : tokenizeAux s 0 #[] = .ok toks)
    (htw : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p t q "").2 < t.size)
    (hnoerr : ∀ (k : Nat) (h : k < t.size),
      (lexToken t k h).isOk = true)
    (hnostr : ∀ (k : Nat) (h : k < t.size), t[k]'h ≠ '"') :
    tokenizeAux (s ++ #[('\n' : Char)] ++ t) 0 #[]
      = (tokenizeAux t 0 #[]).map
        (fun acc => toks ++ acc) := by
  -- the array associativity: (s ++ nl) ++ t = s ++ (nl ++ t)
  rw [show s ++ #[('\n' : Char)] ++ t
      = (s ++ #[('\n' : Char)]) ++ t from rfl]
  -- the tail law, instantiated at the join offset
  have hwalk := tokenizeAux_append_right_ok
    (s := s ++ #[('\n' : Char)]) (t := t) htw hnoerr hnostr
  -- the remaining composition layer: the walk from 0 in the joined
  -- array must be transported to the offset walk — this needs the
  -- left-composition lemma (the walk in s ++ nl from 0 equals
  -- toks ++ the walk in nl from 0, itself [] by whitespace) plus
  -- the walk-continuation at the boundary. Genuinely remaining:
  -- see PLAN.md item 2a (the left-composition lemma).
  sorry

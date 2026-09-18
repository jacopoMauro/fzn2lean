import solver.Emit
open LeanFzn LeanFzn.Solver LeanFzn.Lexer

/-- `lexInt` past the join is the tail's scan, with the end
    position offset by `s.size` (the same character window) — the
    integer-literal half of the lexer's tail agreement. -/
theorem lexInt_append_right {s t : Array Char} {k : Nat}
    (hpos : k < t.size)
    (htw : ∀ (p : Char → Bool) (q : Nat), k ≤ q →
      (takeWhile p t q "").2 < t.size) :
    lexInt (s ++ t) (s.size + k)
      = (lexInt t k).map (fun (tok, p) => (tok, p + s.size)) := by
  sorry

theorem lexToken_append_right_ok {s t : Array Char} {k : Nat}
 {s t : Array Char} {k : Nat}
    {tok : Token} {p : Nat} {hp : k < p} (hpos : k < t.size)
    (htw : ∀ (p : Char → Bool) (q : Nat), k ≤ q →
      (takeWhile p t q "").2 < t.size)
    (hnostr : t[k]'hpos != '"')
    (hok : lexToken t k hpos = .ok (tok, ⟨p, hp⟩)) :
    lexToken (s ++ t) (s.size + k) (by rw [Array.size_append]; omega)
        = .ok (tok, ⟨s.size + p, by omega⟩) := by
  have hlt : s.size + k < (s ++ t).size := by rw [Array.size_append]; omega
  have heq : (s ++ t)[s.size + k]'hlt = t[k]'hpos :=
    arrGetElem_append_right' hpos
  -- transport the RHS through the char equality: case on t[k]'hpos
  -- is over 14 chars — instead use the general match transport:
  -- generalize the char and the hypothesis hok
  rw [lexToken.eq_def (s := t) (pos := k) (h := hpos)] at hok
  simp only [] at hok
  split at hok
  case h_1 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_2 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_3 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_4 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_5 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_6 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_7 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_8 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_9 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  -- h_10 (':'): the lookahead conditions agree
  case h_10 heqc =>
    -- the lookahead position must be inside t (hok's if is .ok, so
    -- the t-side condition decided one way or the other with k+1
    -- reads); first reduce hok's if
    by_cases hcond : (decide (k + 1 < t.size) && t[k + 1]! == ':') = true
    · -- the t-side takes colonColon: the s++t side does too (the
      -- lookahead chars agree when k+1 < t.size)
      have hlt1 : k + 1 < t.size := by
        -- hcond's first conjunct is true
        have hdec := Bool.and_eq_true_iff.mp hcond
        have : decide (k + 1 < t.size) = true := hdec.1
        exact of_decide_eq_true this
      have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
        arrGetElem!_append_right' hlt1
      have hk2 : p = k + 2 := by
        rw [if_pos hcond] at hok
        have hpair := Except.ok.inj hok
        obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
        subst htok
        injection hpp with hpv
        omega
      subst hk2
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [show (s ++ t)[s.size + k + 1]! = t[k + 1]! from hlk]
      -- the size decide is true (k+1 < t.size gives s.size+k+1 <
      -- (s++t).size); the char part of hcond then matches
      have hdect := decide_eq_true (show s.size + k + 1 < (s ++ t).size from by
        rw [Array.size_append]; omega)
      rw [hdect]
      have hcond2 : (t[k + 1]! == ':') = true :=
        (Bool.and_eq_true_iff.mp hcond).2
      rw [hcond2]
      simp only [Bool.true_and, reduceIte, Except.pure]
      -- hok's colonColon case forces tok = .colonColon (hpair was
      -- derived above in hk2's proof; redo it here for tok)
      have htokcc : tok = Token.colonColon := by
        rw [if_pos hcond] at hok
        have hpair := Except.ok.inj hok
        exact (Prod.mk.inj hpair).1.symm
      rw [htokcc]
      rfl
    · rw [if_neg hcond] at hok
      have hpair := Except.ok.inj hok
      obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
      subst htok
      have hk1 : p = k + 1 := by injection hpp with hpv; omega
      subst hk1
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      -- the s++t-side condition must be false: if its size-decide
      -- were true, then k+1 < t.size (sizes), the reads agree, and
      -- the conditions would be equal — contradicting hcond
      -- the s++t-side SIZE decide: (s.size + k + 1 <
      -- (s++t).size) iff (k+1 < t.size); hcond (the t-side
      -- condition is false) forces k+1 ≥ t.size... NO: hcond being
      -- the NEGATION of (decide && read) with decide-t TRUE forces
      -- only the read false. The size decide is separately true
      -- exactly when k+1 < t.size. Case on it:
      by_cases hlt1 : k + 1 < t.size
      · -- size decide true; the reads agree, so the s++t-side
        -- whole condition is (true && read) = read = false — the
        -- if selects the else: colon at k+1 — matching hok
        have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
          arrGetElem!_append_right' hlt1
        have hdect : decide (k + 1 < t.size) = true :=
          decide_eq_true hlt1
        have hcondf : (t[k + 1]! == ':') = false := by
          have hpair := Bool.and_eq_false_iff.mp (by
            cases hh : (decide (k + 1 < t.size) && t[k + 1]! == ':') with
            | true => exact absurd hh hcond
            | false => rfl)
          rw [hdect] at hpair
          exact hpair.resolve_left (by simp)
        rw [hlk, hcondf, Bool.and_false, if_neg (by simp)]
        rfl
      · rw [decide_eq_false (by
          rw [Array.size_append]
          omega)]
        rfl
  -- h_11 ('.'): hok is .ok, so the t-side condition must be true
  -- (the false branch throws), and the reads agree
  case h_11 heqc =>
    have hlt1 : k + 1 < t.size := by
      -- if k+1 ≥ t.size the t-side condition is false (decide false)
      -- and lexToken t throws — contradicting hok
      by_cases hc : k + 1 < t.size
      · exact hc
      · exfalso
        have hsd : decide (k + 1 < t.size) = false :=
          decide_eq_false (by omega)
        -- hok is already the if-form; the condition is
        -- (false && ...) = false, so hok is throw = Except.ok —
        -- contradiction
        rw [hsd, Bool.false_and, if_neg (by simp)] at hok
        exact absurd hok (by simp)
    have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
      arrGetElem!_append_right' hlt1
    have hdect : decide (k + 1 < t.size) = true :=
      decide_eq_true hlt1
    -- the read must be '.' (else the t side throws)
    have hcond : (decide (k + 1 < t.size) && t[k + 1]! == '.') = true := by
      cases hh : (decide (k + 1 < t.size) && t[k + 1]! == '.') with
      | true => rfl
      | false =>
          exfalso
          -- the condition is false, so lexToken's if selects the
          -- throw branch: hok becomes an error — contradiction
          have hcondneg : ¬ ((decide (k + 1 < t.size) && t[k + 1]! == '.') = true) := by
            rw [hh]; simp
          rw [if_neg hcondneg] at hok
          exact absurd hok (by simp)
    -- the s++t side: same reads, same condition — dotDot, offset
    have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
      arrGetElem!_append_right' hlt1
    have hk2 : p = k + 2 := by
      rw [if_pos hcond] at hok
      have hpair := Except.ok.inj hok
      obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
      subst htok
      injection hpp with hpv
      omega
    subst hk2
    have htokdd : tok = Token.dotDot := by
      rw [if_pos hcond] at hok
      have hpair := Except.ok.inj hok
      exact (Prod.mk.inj hpair).1.symm
    rw [htokdd]
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rw [decide_eq_true (by rw [Array.size_append]; omega), hlk]
    have hread : (t[k + 1]! == '.') = true :=
      (Bool.and_eq_true_iff.mp hcond).2
    rw [hread]
    rfl

  -- h_12 ('"'): excluded
  case h_12 heqc =>
    -- hnostr : (t[k]'hpos ≠ '"') as a Bool ≠-statement; heqc says
    -- the char IS '"' — contradiction
    have hbb : (t[k]'hpos == '"') = true := by rw [heqc]; rfl
    rw [show (t[k]'hpos != '"') = (!(t[k]'hpos == '"')) from rfl,
      hbb] at hnostr
    exact absurd hnostr (by simp)
  -- h_13: ident/int
  case h_13 heqc =>
    -- the default branch: identifier or integer
    -- first: the char classes agree between the two sides (the char
    -- is shared), so both sides take the same sub-branch
    by_cases halpha : (isAlpha t[k] || t[k] == '_') = true
    · -- the identifier branch: the scans agree via the offset law
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [if_pos halpha]
      -- the s++t-side scan is the t-side scan (the offset law at
      -- the associated position, with the shared accumulator char)
      -- extract hok's t-side result: split the keywordToken match
      -- inside hok, then use the .ok extraction per branch
      rw [if_pos halpha] at hok
      cases hhk : keywordToken
          (takeWhile isIdentChar t (k + 1) (String.singleton t[k])).1 with
      | some tok2 =>
          -- hok's match selects the `some` arm (hhk); reduce it
          rw [hhk] at hok
          have htok : tok = tok2 := by
            have hpair := Except.ok.inj hok
            exact (Prod.mk.inj hpair).1.symm
          subst htok
          -- the s++t-side scan law (the position offset)
          have h := takeWhile_append_right (p := isIdentChar)
            (s := s) (t := t) (k := k + 1) (acc := String.singleton t[k])
          have hpos : s.size + (k + 1) = s.size + k + 1 := by omega
          rw [hpos] at h
          -- p from hok
          have hpp : p = (takeWhile isIdentChar t (k + 1)
              (String.singleton t[k])).2 := by
            have hpair := Except.ok.inj hok
            obtain ⟨_, hp2⟩ := Prod.mk.inj hpair
            injection hp2 with hpv
            omega
          subst hpp
          simp only [h]
          rw [hhk]
          rfl
      | none =>
          rw [hhk] at hok
          -- the reserved-contains check must be false (hok is .ok)
          by_cases hres : reservedNonFzn.contains
              (takeWhile isIdentChar t (k + 1) (String.singleton t[k])).1 = true
          · rw [if_pos hres] at hok
            exact absurd hok (by simp)
          · rw [if_neg hres] at hok
            -- the ident token; extract and transport
            have hpair := Except.ok.inj hok
            obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
            subst htok
            -- the scan offset law: replace the s++t-side scan by the
            -- t-side one (the goal is already the unfolded match)
            have h := takeWhile_append_right (p := isIdentChar)
              (s := s) (t := t) (k := k + 1) (acc := String.singleton t[k])
            have hpos : s.size + (k + 1) = s.size + k + 1 := by omega
            rw [hpos] at h
            -- rewrite the scan pair; simp handles the dependent
            -- .snd projection (the subtype property shifts by the
            -- offset, which the goal type already expects)
            simp only [h]
            rw [if_neg hres]
            -- hpp identifies p with the t-side scan position; use
            -- simp to also reduce the keywordToken match and the
            -- position arithmetic
            have hpp2 : p = (takeWhile isIdentChar t (k + 1)
                (String.singleton t[k])).2 := by
              injection hpp with hpv
              omega
            simp only [hpp2]
            rw [hhk]
            rfl
    · rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [if_neg halpha]
      by_cases hdigit : (isDigit t[k] || t[k] == '-') = true
      · rw [if_pos hdigit]
        -- the integer branch: the token/position transport
        -- (hok already unfolded; the s++t side's lexInt agrees by
        -- the same character-window argument)
        rw [if_neg halpha] at hok
        rw [if_pos hdigit] at hok
        -- reduce hok's dependent match on lexInt t k by splitting
        split at hok
        next tok2 p2 hli =>
          -- hli : lexInt t k = .ok (tok2, p2); hok gives tok/p
          have hpair := Except.ok.inj hok
          obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
          have htok2 : tok = tok2 := htok.symm
          have hpp2 : p = p2 := by
            injection hpp with hpv
            omega
          subst htok2
          subst hpp2
          -- the goal's match on lexInt (s++t) (s.size+k): the
          -- s++t-side lexInt succeeds with the same token and the
          -- offset position; split the goal's match
          split
          · -- s++t side ok: same token; the position is the t-side
            -- end plus s.size (the character window agrees)
            next tok3 p3 hli' =>
              -- the s++t side's lexInt is the offset of the t
              -- side's (lexInt_append_right); with hli (the t
              -- side's result) the positions satisfy
              -- p3 = p + s.size and tok3 = tok
              have hoffset := lexInt_append_right (s := s) (t := t)
                (k := k) hpos htw
              rw [hli] at hoffset
              -- the goal: (.ok (tok3, ⟨p3, ·⟩) = .ok (tok, ⟨s.size+p, ·⟩))
              -- with hli' : lexInt (s++t) .. = .ok (tok3, p3) and
              -- hoffset : lexInt (s++t) .. = .ok (tok, p+s.size):
              -- identify tok3 = tok, p3 = p + s.size by transitivity
              have hident : Except.ok (tok3, p3)
                  = Except.ok (tok, p + s.size) :=
                hli'.symm.trans (by rw [hoffset]; rfl)
              obtain ⟨rfl, hpp3⟩ := (Prod.mk.inj (Except.ok.inj hident))
              -- p3 = s.size + p; substitute and close by proof
              -- irrelevance of the subtype property
              have hpp3eq : p3 = s.size + p := by omega
              subst hpp3eq
              rfl
          · -- s++t side error — impossible: the same characters
            -- succeed on the t side; the offset law gives
            -- lexInt (s++t) .. = .map .. (lexInt t k), and hli
            -- says the t side succeeded
            rename_i e hlierr
            have hoffset := lexInt_append_right (s := s) (t := t)
              (k := k) hpos htw
            rw [hli] at hoffset
            rw [hoffset] at hlierr
            exact absurd hlierr (by
              intro hc
              have hred : (Except.map
                  (fun x => match x with | (tok, p) => (tok, p + s.size))
                  (Except.ok (tok, p)) :
                  Except String (Token × Nat))
                  = Except.ok (tok, p + s.size) := rfl
              rw [hred] at hc
              exact absurd hc (by simp))
        · rename_i e hli
          exact absurd hok (by simp)
      · rw [if_neg hdigit]
        -- both sides throw; hok is .ok — contradiction
        exfalso
        rw [if_neg halpha, if_neg hdigit] at hok
        exact absurd hok (by simp)


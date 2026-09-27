import solver.Direct.Proofs.Compile
import solver.Direct.Compile

open LeanFzn LeanFzn.Solver LeanFzn.Solver.Direct

/-! ## A: the slot-position machinery (produced, then located) -/

/-- Membership in a slot list gives the position whose bang-read
    returns the member. -/
theorem slot_getElem!_of_mem : ∀ (l : List (String × List Value))
    (x : String × List Value), x ∈ l →
    ∃ i, i < l.length ∧ l[i]! = x := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | htl
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨i, hilt, higet⟩ := ih x htl
        exact ⟨i + 1, by
          simp only [List.length_cons]
          omega, by
          rw [List.getElem!_cons_succ]
          exact higet⟩

/-! ## B: the production membership (the var-decls half's foundation) -/

/-- Every successfully-extracted slot pair of a declared variable is
    IN the produced slot list (production, no uniqueness). -/
theorem declSlots_produce : ∀ (vars : List VarDeclItem)
    (slots : List (String × List Value)),
    declSlots vars = .ok slots →
    ∀ (d : VarDeclItem), d ∈ vars → ∀ p, declSlot d = .ok (some p) →
    p ∈ slots := by
  intro vars
  induction vars with
  | nil => intro _ _ _ hmem _ _; cases hmem
  | cons d rest ih =>
      intro slots h d' hd' p hds
      rw [declSlots] at h
      match hhead : declSlot d with
      | .error e =>
          rw [hhead] at h; exact absurd h (by simp)
      | .ok none =>
          rw [hhead] at h
          rcases List.mem_cons.mp hd' with rfl | htl
          · rw [hds] at hhead; exact absurd hhead (by simp)
          · exact ih slots h d' htl p hds
      | .ok (some p0) =>
          rw [hhead] at h
          match hrest : declSlots rest with
          | .error e =>
              rw [hrest] at h
              exact absurd h (by simp [Except.map])
          | .ok restslots =>
              rw [hrest] at h
              have hmapstep : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok slots := h
              have hmapred : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok (p0 :: restslots) := rfl
              rw [hmapred] at hmapstep
              have hcons : p0 :: restslots = slots := Except.ok.inj hmapstep
              rw [← hcons]
              rcases List.mem_cons.mp hd' with rfl | htl
              · rw [hds] at hhead
                injection hhead with h1
                injection h1 with h2
                rw [h2]
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem _
                  (ih restslots (by rw [hrest]) d' htl p hds)

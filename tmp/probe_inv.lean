import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- Generic three-argument evaluation inversion: the first two
    arguments are the given identifiers, the third arbitrary. -/
theorem eval_three_inv {store : Store}
    {x y : Ident} {e3 : Expr} {l : List Value}
    (h3 : [Expr.basic (.ident x), Expr.basic (.ident y), e3].mapM
        (Expr.eval store) = some l) :
    ∃ v1 v2 v3, store x = some v1 ∧ store y = some v2 ∧
      Expr.eval store e3 = some v3 ∧ l = [v1, v2, v3] := by
  -- normalize to the three-step bind chain
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => Option.bind (Expr.eval store e3)
          (fun v3 => some [v1, v2, v3]))) = some l := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using h3
  -- the ident evals are the store reads
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred1, hred2] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some v1 =>
      rw [hsx] at hchain
      simp only [Option.bind_some, pure] at hchain
      cases hsy : store y with
      | none => rw [hsy] at hchain; simp at hchain
      | some v2 =>
          rw [hsy] at hchain
          simp only [Option.bind_some, pure] at hchain
          cases he3 : Expr.eval store e3 with
          | none => rw [he3] at hchain; simp at hchain
          | some v3 =>
              rw [he3] at hchain
              simp only [Option.bind_some, pure] at hchain
              exact ⟨v1, v2, v3, rfl, rfl, rfl, by simpa using hchain.symm⟩

theorem holds_int_plus_E_inv {store : Store} {c : ConstraintItem}
    {x y : Ident} {k : Int} {E : Expr}
    (hname : c.name.name = "int_plus")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧
      p + q = k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨v1, v2, v3, hsx, hsy, he3, hargsv⟩ := eval_three_inv hmap
  have hv3 : v3 = .int k := (Option.some.inj (he3.symm.trans hE))
  subst hv3
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_plus") [v1, v2, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide :
    ¬ "int_plus" ∈ globalsNames)] at h1
  have hmatch : (match [v1, v2, .int k] with
    | [Value.int a, Value.int b, Value.int w] => a + b = w
    | _ => False) := h1
  cases v1 with
  | int p =>
      cases v2 with
      | int q =>
          have hk : p + q = k := by simpa using hmatch
          exact ⟨p, q, rfl, rfl, hk⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

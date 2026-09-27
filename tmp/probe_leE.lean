import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The E-generalized `int_le(x, E)` inversion. -/
theorem holds_int_le_const_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p ≤ k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1, hE] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .int k] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_le") [vx, .int k] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_le" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .int k] with
        | [Value.int a, Value.int b] => a ≤ b
        | _ => False) := h1
      cases vx with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

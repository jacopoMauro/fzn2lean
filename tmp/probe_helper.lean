import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- A bang read equal to `.int p` from a `some (.int p)` read. -/
theorem int_of_some_read {a : List Value} {i : Nat} {p : Int}
    (h : some a[i]! = some (Value.int p)) : a[i]! = Value.int p := by
  cases hai : a[i]! with
  | int v =>
      have hiv : Value.int v = Value.int p := h
      rw [hai]
      exact congrArg _ (by injection hiv)
  | bool w => exact absurd h (by simp)
  | setOfInt w => exact absurd h (by simp)
  | array w => exact absurd h (by simp)

import solver.Direct.Proofs.CompileCore

open LeanFzn.Solver.Direct LeanFzn

theorem auxshape_pin2_pin' {sh : AuxShape} {v2 : LeanFzn.Value}
    (h : sh.pin2 = some v2) : sh.pin ≠ none := by
  cases sh with
  | timesRKK x k k' => rw [AuxShape.pin]; simp
  | timesKRR x k k' => rw [AuxShape.pin]; simp
  | timesKKR x k k' => rw [AuxShape.pin]; simp
  | _ => simp [AuxShape.pin2] at h

example (x y : LeanFzn.Ident) (k : Int) (v : LeanFzn.Value)
    (h : (AuxShape.timesRK x y k).pin2 = some v) : False := by
  simp [AuxShape.pin2] at h

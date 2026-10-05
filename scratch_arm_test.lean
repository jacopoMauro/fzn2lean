import solver.Direct.Proofs.CompileCore

open LeanFzn.Solver.Direct LeanFzn

-- GOAL SHAPE of the two disjuncts in pieces_mem no-slot arm
example (sh : AuxShape) : True := by
  have goal1 : (sh.pin = none ∨ ∃ v, sh.pin = some v ∧ True) := by
    left; rfl
  trivial

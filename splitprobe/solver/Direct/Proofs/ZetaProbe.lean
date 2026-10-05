import solver.Core
import solver.Direct.Compile

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core

theorem probe_zeta {taken : List String} (c : ConstraintItem)
    (rest : List ConstraintItem) (auxs auxs' : List (String × List Value))
    (cs' : List ConstraintItem)
    (h : expandPlan taken auxs (c :: rest) = (auxs', cs')) : True := by
  rw [expandPlan] at h
  split at h
  · trivial
  · rename_i sh hshape
    split at h
    · rename_i v v2 hpin hpin2
      cases hrec : expandPlan taken
          (auxs ++ [(auxName taken auxs.length, [v]),
             ((auxName taken auxs.length).push '$', [v2])]) rest with
      | mk auxs2 cs2 =>
          simp only [] at h
          rw [hrec] at h
          simp only at h
          trace_state
          trivial
    · rename_i v h1 hpin
      trace_state
      cases hrec : expandPlan taken
          (auxs ++ [(auxName taken auxs.length, [v])]) rest with
      | mk auxs2 cs2 =>
          rw [hrec] at h
          simp only at h
          trace_state
          trivial
    · trivial

end LeanFzn.Solver.Direct

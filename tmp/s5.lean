import solver.LCG.Engine
import solver.LCG.Encoding
import solver.LCG.Invariants
import solver.LCG.Proofs.Lift

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Probe: unfold + zeta + branch split for enqueueNorm's conflict slot. -/
example (st : State) (l0 : Literal) (reason : Option Reason)
    (hnone : st.conflict = none) :
    (enqueueNorm st l0 reason).conflict = none := by
  unfold enqueueNorm
  split
  · exact hnone
  · split
    · -- opposing: conflict becomes the pair — NOT none; treat as false goal
      exfalso
      -- cannot happen here without justification: derive contradiction
      -- from hnone? No — the opposing branch GENUINELY sets a conflict.
      -- So this example is only true assuming justification; stop here.
      sorry
    · rename_i h1 h2
      show ((let st' := enqueue st l0.norm reason
        { st' with domains := domOfLit st'.domains l0.norm }) : State).conflict
          = none
      have hdom : (enqueue st l0.norm reason).conflict = st.conflict := rfl
      rw [hdom]; exact hnone

end LeanFzn.Solver.LCG

/-
File: LeanFzn/Solver/Propagation/Proofs/EngDup.lean

Purpose:
  Domain-update plumbing for the propagation-loop lift (PLAN.md Step 2):
  the in-range read-back for `updateSlot` — updating slot `s` and reading
  it back gives exactly the update's image. This is what the FIRING
  lemma needs (fits + satisfied literal ⇒ fits the narrowed domains).

Dependencies:
  - LeanFzn.Solver.Reference.Engine: `updateSlot`, `domOfLit`.

DAG:
  LeanFzn.Solver.UIP.Engine -> LeanFzn.Solver.Propagation.Proofs.EngDup -> LeanFzn.Solver.UIP.Proofs.Lift
-/

import LeanFzn.Solver.Reference.Engine


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Reference
open LeanFzn LeanFzn.Solver.Core

/-- In-range read-back: updating slot `s` (with `s` in the doms range)
    and reading it back gives exactly the update's image. -/
theorem updateSlot_getD_eq : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain), s < doms.length →
    (updateSlot doms s f).getD s Dom.empty = f (doms.getD s Dom.empty) := by
  intro doms
  induction doms with
  | nil => intro s f h; exact absurd h (Nat.not_lt_zero s)
  | cons d ds ih =>
      intro s f h
      cases s with
      | zero => rfl
      | succ s' =>
          -- unfold updateSlot on the tail
          have hunfold : updateSlot (d :: ds) (s' + 1) f
              = d :: updateSlot ds s' f := by
            show (d :: ds).set (s' + 1)
                (f ((d :: ds).getD (s' + 1) Dom.empty))
              = d :: ds.set s' (f (ds.getD s' Dom.empty))
            have hgetD : (d :: ds).getD (s' + 1) Dom.empty = ds.getD s' Dom.empty := rfl
            rw [hgetD]
            rfl
          rw [hunfold]
          -- read back at the same index: List.getD_cons_succ fires
          rw [List.getD_cons_succ]
          -- the image side:
          rw [show (d :: ds).getD (s' + 1) Dom.empty = ds.getD s' Dom.empty from rfl]
          exact ih s' f (by
            show s' < ds.length
            simpa using h)

/-- Forward same-slot membership: a value in the update's image is in
    the updated slot domain (in-range read-back, membership form). -/
theorem mem_updateSlot_of_mem : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain) (v : Value),
    s < doms.length →
    v ∈ f (doms.getD s Dom.empty) →
    v ∈ (updateSlot doms s f).getD s Dom.empty := by
  intro doms
  induction doms with
  | nil => intro s f v h _; exact absurd h (Nat.not_lt_zero s)
  | cons d ds ih =>
      intro s f v h hmem
      cases s with
      | zero => exact hmem
      | succ s' =>
          -- both sides reduce by List.getD_cons_succ to tail reads
          have hupd : updateSlot (d :: ds) (s' + 1) f
              = d :: updateSlot ds s' f := by
            show (d :: ds).set (s' + 1) (f ((d :: ds).getD (s' + 1) Dom.empty))
              = d :: ds.set s' (f (ds.getD s' Dom.empty))
            rw [show (d :: ds).getD (s' + 1) Dom.empty = ds.getD s' Dom.empty from rfl]
            rfl
          show v ∈ (updateSlot (d :: ds) (s' + 1) f).getD (s' + 1) Dom.empty
          rw [hupd, List.getD_cons_succ]
          -- now the goal is the IH's conclusion modulo the reduction of
          -- the premise's getD to the tail's
          exact ih s' f v (by
            show s' < ds.length
            simpa using h) hmem

/-- At an untouched slot `s ≠ s0`, `updateSlot doms s0 f` leaves the
    slot domain alone. Proved by a plain structural induction (the
    past-the-end degenerate case included). -/
theorem updateSlot_getD_ne : ∀ (doms : List Domain) (s0 : Nat)
    (f : Domain → Domain) (s : Nat), s ≠ s0 →
    (updateSlot doms s0 f).getD s Dom.empty = doms.getD s Dom.empty := by
  intro doms
  induction doms with
  | nil =>
      intro s0 f s hne
      cases s <;> cases s0 <;> rfl
  | cons d ds ih =>
      intro s0 f s hne
      cases s0 with
      | zero =>
          cases s with
          | zero => exact absurd rfl hne
          | succ s' => rfl
      | succ s0' =>
          show (d :: updateSlot ds s0' f).getD s Dom.empty = (d :: ds).getD s Dom.empty
          cases s with
          | zero => rfl
          | succ s' =>
              show (updateSlot ds s0' f).getD s' Dom.empty = ds.getD s' Dom.empty
              exact ih s0' f s' (fun hcon => hne (by rw [hcon]))

end LeanFzn.Solver.Propagation

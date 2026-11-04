/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunDropDef.lean
H2f: the stack-soundness invariant of an LCG run (definitions and set-theoretic stack lemmas).

`StackSoundFrom leaf U l` says: for the frames `l = g0 :: g1 :: ...` (current branch frame first,
then the pending stack), every leaf solution `a` extending the pin prefix of `g_i` and lying in the
box of `g_i` fails to be covered by `g_i` only if it is already covered by one of the frames above
(`U`, accumulated). For the head (`U = ⊥`) this is `FrameSnd`: the frame holds every solution of its
own pin prefix. The dropped values of a consumed pending frame are then dead because the failed
branch above it covers no solution (`DeadSound`).
-/
import LeanFzn.Legacy.Solver.UIP.SchedulerStep
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.UIP.LcgRunDrop

variable {leaf : Assignment → Bool}

/-- The frame holds every leaf solution extending its pin prefix. -/
def FrameSnd (leaf : Assignment → Bool) (g : BranchFrame) : Prop :=
  ∀ a, leaf a = true → Frame.PinsAgree g a → FrameCovers g a

/-- Decision-pin agreement: the assignment reads the recorded value at
every DECIDED slot of the frame (the sparse form of the old prefix test
`f.2 <+: a`). Unlike `Frame.PinsAgree`, this does not constrain incidental
singleton domains at UNDECIDED slots. -/
def Frame.PinsOnOrder (f : BranchFrame) (a : Assignment) : Prop :=
  ∀ k ∈ f.order, ∀ v, f.doms[k]?.map Dom.enum = some [v] → a[k]? = some v

theorem pinsAgree_implies_pinsOnOrder {f : BranchFrame} {a : Assignment}
    (h : Frame.PinsAgree f a) : Frame.PinsOnOrder f a :=
  fun k _ v hv => h k v hv

/-- The order-refined frame-soundness law: the faithful sparse form of the
old positional `FrameSnd` (agreement with the DECIDED prefix, not with every
incidental singleton domain). -/
def FrameSndOrder (leaf : Assignment → Bool) (g : BranchFrame) : Prop :=
  ∀ a, leaf a = true → Frame.PinsOnOrder g a → FrameCovers g a

/-- The order-refined law is stronger than the all-singleton law. -/
theorem frameSnd_of_frameSndOrder {g : BranchFrame} (h : FrameSndOrder leaf g) :
    FrameSnd leaf g :=
  fun a ha hp => h a ha (pinsAgree_implies_pinsOnOrder hp)

/-- Stack soundness relative to the already-seen coverage `U`. -/
def StackSoundFrom (leaf : Assignment → Bool) : (Assignment → Prop) → List BranchFrame → Prop
  | _, [] => True
  | U, g :: rest =>
      (∀ a, leaf a = true → Frame.PinsOnOrder g a → ¬ FrameCovers g a → U a) ∧
        StackSoundFrom leaf (fun a => U a ∨ FrameCovers g a) rest

/-- Stack soundness of a configuration (current frame, then pending). -/
def StackSound (cfg : SchedulerConfig leaf) : Prop :=
  StackSoundFrom leaf (fun _ => False) (cfg.branch.frame :: cfg.pending)

/-- A dead (or conflicted) branch frame covers no leaf solution. -/
def DeadSound (cfg : SchedulerConfig leaf) : Prop :=
  (cfg.status = .dead ∨ cfg.conflict ≠ none) →
    ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a

/-- Every saved checkpoint frame holds the solutions of its pin prefix. -/
def CpSound (cfg : SchedulerConfig leaf) : Prop :=
  ∀ cp ∈ cfg.checkpoints, FrameSndOrder leaf cp.frame

theorem frameSnd_root {orig : List Domain} (hfits : ∀ a, leaf a = true → a.Fits orig) :
    FrameSnd leaf (⟨orig, []⟩ : BranchFrame) := by
  intro a ha _
  obtain ⟨hlen, hmem⟩ := hfits a ha
  exact mem_allAssigns_of_getElem? orig a hlen (fun k v hv => hmem k v hv)

theorem frameSndOrder_root {orig : List Domain} (hfits : ∀ a, leaf a = true → a.Fits orig) :
    FrameSndOrder leaf (⟨orig, []⟩ : BranchFrame) := by
  intro a ha _
  obtain ⟨hlen, hmem⟩ := hfits a ha
  exact mem_allAssigns_of_getElem? orig a hlen (fun k v hv => hmem k v hv)

theorem stackSoundFrom_mono {U U' : Assignment → Prop}
    (h : ∀ a, leaf a = true → U a → U' a) :
    ∀ {l : List BranchFrame}, StackSoundFrom leaf U l → StackSoundFrom leaf U' l := by
  intro l
  induction l generalizing U U' with
  | nil => intro _; trivial
  | cons g rest ih =>
      intro hs
      refine ⟨fun a ha hp hc => h a ha (hs.1 a ha hp hc), ih ?_ hs.2⟩
      intro a ha hu
      rcases hu with hu | hu
      · exact Or.inl (h a ha hu)
      · exact Or.inr hu

theorem frameSnd_of_head {g : BranchFrame} {l : List BranchFrame}
    (h : StackSoundFrom leaf (fun _ => False) (g :: l)) : FrameSndOrder leaf g := by
  intro a ha hp
  refine Classical.byContradiction fun hc => ?_
  exact h.1 a ha hp hc

theorem stackSoundFrom_tail {U : Assignment → Prop} {g : BranchFrame} {l : List BranchFrame}
    (h : StackSoundFrom leaf U (g :: l)) :
    StackSoundFrom leaf (fun a => U a ∨ FrameCovers g a) l := h.2

/-- Replace the head frame by a frame that is sound and covers every leaf solution the old head
covered (propagation, redundant-pin skip, and the jump, where the old head covers none). -/
theorem stackSound_replace_head {B B' : BranchFrame} {P : List BranchFrame}
    (h : StackSoundFrom leaf (fun _ => False) (B :: P))
    (hB' : FrameSndOrder leaf B')
    (hcov : ∀ a, leaf a = true → FrameCovers B a → FrameCovers B' a) :
    StackSoundFrom leaf (fun _ => False) (B' :: P) := by
  refine ⟨fun a ha hp hc => hc (hB' a ha hp), ?_⟩
  refine stackSoundFrom_mono ?_ h.2
  intro a ha hu
  rcases hu with hu | hu
  · exact absurd hu id
  · exact Or.inr (hcov a ha hu)

/-- Consume: a dead head is dropped; the next pending frame becomes the head. -/
theorem stackSound_consume {B f : BranchFrame} {rest : List BranchFrame}
    (h : StackSoundFrom leaf (fun _ => False) (B :: f :: rest))
    (hdead : ∀ a, leaf a = true → ¬ FrameCovers B a) :
    StackSoundFrom leaf (fun _ => False) (f :: rest) := by
  have h1 := h.2
  refine ⟨fun a ha hp hc => ?_, ?_⟩
  · rcases h1.1 a ha hp hc with hu | hu
    · exact hu
    · exact hdead a ha hu
  · refine stackSoundFrom_mono ?_ h1.2
    intro a ha hu
    rcases hu with (hu | hu) | hu
    · exact Or.inl hu
    · exact absurd hu (hdead a ha)
    · exact Or.inr hu

/-- Split: the head is replaced by the pinned child, the sibling pushed below it. -/
theorem stackSound_split {B C S : BranchFrame} {P : List BranchFrame}
    (h : StackSoundFrom leaf (fun _ => False) (B :: P))
    (hC : FrameSndOrder leaf C)
    (hS : ∀ a, leaf a = true → Frame.PinsOnOrder S a → ¬ FrameCovers S a → FrameCovers C a)
    (hsplit : ∀ a, FrameCovers B a → FrameCovers C a ∨ FrameCovers S a) :
    StackSoundFrom leaf (fun _ => False) (C :: S :: P) := by
  refine ⟨fun a ha hp hc => hc (hC a ha hp), fun a ha hp hc => ?_, ?_⟩
  · exact Or.inr (hS a ha hp hc)
  · refine stackSoundFrom_mono ?_ h.2
    intro a ha hu
    rcases hu with hu | hu
    · exact absurd hu id
    · rcases hsplit a hu with hc | hs
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hs

end LeanFzn.Solver.UIP.LcgRunDrop

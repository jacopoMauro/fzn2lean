import solver.LCG.Engine
import solver.LCG.Encoding
import solver.LCG.Invariants
import solver.LCG.Proofs.Lift

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

structure PropSafe (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  impliedTrueAt : ∀ p ∈ props, ∀ l r,
    p.run st = .implied l r →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      l.eval a = some true
  conflictExcludes : ∀ p ∈ props, ∀ c,
    p.run st = .conflict c →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      ¬ c.SatisfiedBy a

def PropSafeUniv (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) : Prop :=
  ∀ st, PropSafe problem constraintHolds props st

def SolvedBy (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
  ∀ a, ProblemSolution problem constraintHolds a → st.Represents a

theorem negOnTrail_falsifies_entry {st : State} {l : Literal}
    {a : Assignment}
    (hneg : st.negOnTrail l = true)
    (hsat : st.TrailSatisfied a) :
    l.eval a = some false := by
  unfold State.negOnTrail at hneg
  rw [List.any_eq_true] at hneg
  obtain ⟨e, hem, heb⟩ := hneg
  have hlit : e.literal = l.negate.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit, Literal.norm_eval (l.negate) a, Literal.eval_negate l a] at hev
  cases h : l.eval a with
  | none => rw [h] at hev; simp at hev
  | some b =>
      rw [h] at hev
      cases b <;> simp at hev <;> rfl

theorem enqueueNorm_no_opposing
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a)
    (hrep : st.Represents a)
    (halt : l0.norm.eval a = some true)
    (hneg : st.negOnTrail l0.norm = true) :
    False := by
  obtain ⟨_, htrail, _, _⟩ := hrep
  have hf : l0.norm.eval a = some false :=
    negOnTrail_falsifies_entry hneg htrail
  rw [halt] at hf
  exact absurd hf (by simp)

theorem enqueueNorm_fresh_solvedBy
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true)
    (hsol : SolvedBy problem constraintHolds st) :
    SolvedBy problem constraintHolds
      (enqueueNorm st l0 reason) := by
  intro a ha
  have hrep := hsol a ha
  obtain ⟨hfit, htrail, hclauses, hlearned⟩ := hrep
  have hal : l0.norm.eval a = some true := hlit a ha
  have hinrange : l0.norm.atom.slot < a.length :=
    eval_lit_some_slot_lt (l := l0.norm) hal
  have hfitN : a.Fits (domOfLit st.domains l0.norm) :=
    firing (doms := st.domains) (l := l0.norm) (a := a) hfit hinrange hal
  have htrailN : (enqueueNorm st l0 reason).TrailSatisfied a :=
    enqueueNorm_fresh_trailSat (st := st) (l0 := l0)
      (reason := reason) hnew hneg ha htrail hal
  unfold enqueueNorm at htrailN ⊢
  simp only [hnew, hneg, Bool.false_eq_true, if_false] at htrailN ⊢
  refine ⟨?_, htrailN, hclauses, hlearned⟩
  have hdom : (enqueue st l0.norm reason).domains = st.domains := rfl
  rw [hdom]; exact hfitN

theorem enqueueNorm_conflictNone_of_justified
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnone : st.conflict = none)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hrep : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    (enqueueNorm st l0 reason).conflict = none := by
  obtain ⟨b, hb⟩ := hsolvable
  unfold enqueueNorm
  show ((if st.litOnTrail l0.norm = true then st
    else if st.negOnTrail l0.norm = true then
      { st with conflict := some [l0.norm, l0.norm.negate] }
    else
      let st' := enqueue st l0.norm reason
      { st' with domains := domOfLit st'.domains l0.norm }) : State).conflict
    = none
  split
  · exact hnone
  · split
    · exfalso
      rename_i hneg
      exact enqueueNorm_no_opposing (problem := problem)
        (constraintHolds := constraintHolds) (st := st) (l0 := l0)
        (a := b) hb (hrep b hb) (hlit b hb) hneg
    · rename_i h1 h2
      show ((let st' := enqueue st l0.norm reason
        { st' with domains := domOfLit st'.domains l0.norm }) : State).conflict
          = none
      have hdom : (enqueue st l0.norm reason).conflict = st.conflict := rfl
      rw [hdom]; exact hnone

theorem enqueueNorm_solvedBy_of_justified
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hrep : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    SolvedBy problem constraintHolds
      (enqueueNorm st l0 reason) := by
  obtain ⟨b, hb⟩ := hsolvable
  unfold enqueueNorm SolvedBy
  intro a ha
  show ((if st.litOnTrail l0.norm = true then st
    else if st.negOnTrail l0.norm = true then
      { st with conflict := some [l0.norm, l0.norm.negate] }
    else
      let st' := enqueue st l0.norm reason
      { st' with domains := domOfLit st'.domains l0.norm })).Represents a
  split
  · exact hrep a ha
  · split
    · exfalso
      rename_i hneg
      exact enqueueNorm_no_opposing (problem := problem)
        (constraintHolds := constraintHolds) (st := st) (l0 := l0)
        (a := b) hb (hrep b hb) (hlit b hb) hneg
    · rename_i hnew hneg
      have hnew' : st.litOnTrail l0.norm = false := by
        cases hb2 : st.litOnTrail l0.norm with
        | true => exact absurd hb2 hnew
        | false => rfl
      have hneg' : st.negOnTrail l0.norm = false := by
        cases hb2 : st.negOnTrail l0.norm with
        | true => exact absurd hb2 hneg
        | false => rfl
      show ((let st' := enqueue st l0.norm reason
        { st' with domains := domOfLit st'.domains l0.norm })).Represents a
      have conv : ((let st' := enqueue st l0.norm reason
          { st' with domains := domOfLit st'.domains l0.norm }) : State)
          = (enqueueNorm st l0 reason) := by
        simp only [enqueueNorm, hnew', hneg', Bool.false_eq_true, if_false]
      rw [conv]
      exact enqueueNorm_fresh_solvedBy (st := st) (l0 := l0)
        (reason := reason) hnew' hneg' hlit hrep a ha

/-! ## The sweep fold -/

/-- THE SWEEP TRANSFER: folding sound (state-universally) propagators
    over a solved-by conflict-free state yields either a conflict-free
    state that still solves-by (arm (i)), or a conflict clause that no
    internal solution satisfies (arm (ii)). -/
theorem sweep_solvedBy
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : PropSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (st0 : State)
    (hsol : SolvedBy problem constraintHolds st0)
    (hnone : st0.conflict = none) :
    ((runPropagators props st0).conflict = none ∧
      SolvedBy problem constraintHolds (runPropagators props st0)) ∨
    (∃ c, (runPropagators props st0).conflict = some c ∧
      ∀ a, ProblemSolution problem constraintHolds a →
        ¬ c.SatisfiedBy a) := by
  have goInv : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      SolvedBy problem constraintHolds acc →
        ((runPropagators.go ps acc).conflict = none ∧
          SolvedBy problem constraintHolds (runPropagators.go ps acc)) ∨
        (∃ c, (runPropagators.go ps acc).conflict = some c ∧
          ∀ a, ProblemSolution problem constraintHolds a →
            ¬ c.SatisfiedBy a) := by
    intro ps
    induction ps with
    | nil =>
        intro _ acc hacnone hacc
        exact Or.inl ⟨hacnone, hacc⟩
    | cons p rest ih =>
        intro acc hmem hacnone hacc
        -- the safety contract at acc, restricted to p (and rest)
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hsafep := hsafe acc
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        simp only [runPropagators.go]
        split
        · -- guard-true: acc.conflict.isSome, contradicting hacnone
          rename_i his
          rw [hacnone] at his
          exact absurd his (by simp)
        · split
          · -- stable: recurse with acc
            rename_i hres
            exact ih acc hrest hacnone hacc
          · -- conflict: p's own report wrote it
            rename_i c heq
            refine Or.inr ⟨c, ?_, ?_⟩
            · show (some c : Option Clause) = some c
              exact rfl
            · -- p.sound at acc excludes every represented solution
              intro a ha
              exact (hsafep.conflictExcludes p hp c heq a ⟨ha, hacc a ha⟩)
          · -- implied: recurse at the enqueued state; the enqueue
            -- output keeps the conflict slot clear and solves-by
            rename_i l rsn hres
            have hlita : ∀ a, ProblemSolution problem constraintHolds a →
              l.norm.eval a = some true := by
              intro a ha
              rw [Literal.norm_eval l a]
              exact (hsafep.impliedTrueAt p hp l rsn hres a ⟨ha, hacc a ha⟩)
            have hconf := enqueueNorm_conflictNone_of_justified
              (problem := problem) (constraintHolds := constraintHolds)
              (st := acc) (l0 := l) (reason := some rsn)
              hacnone hsolvable hacc hlita
            have hsol2 := enqueueNorm_solvedBy_of_justified
              (problem := problem) (constraintHolds := constraintHolds)
              (st := acc) (l0 := l) (reason := some rsn)
              hsolvable hacc hlita
            exact ih (enqueueNorm acc l (some rsn)) hrest hconf hsol2
  exact goInv props st0 (fun _ hq => hq) hnone hsol

/-! ## The clause-database scan verdicts -/

/-- `scanClause`'s conflict verdict reports the scanned clause itself. -/
theorem scanClause_inl_eq {st : State} {c d : Clause}
    (h : scanClause st d = some (Sum.inl c)) : c = d := by
  unfold scanClause at h
  split at h
  · exact absurd h (by simp)
  · rename_i _
    match hh : d.filter (fun l => !st.negOnTrail l) with
    | [] =>
      rw [hh] at h
      cases h
      rfl
    | [l] => rw [hh] at h; exact absurd h (by simp)
    | l1 :: l2 :: rest => rw [hh] at h; exact absurd h (by simp)

/-- The clause database is sound when every clause in it is satisfied by
    every internal solution (`Invariants.Clause.EntailedBy` over
    `st.allClauses`). -/
def DbSound (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
  ∀ d ∈ st.allClauses, d.EntailedBy problem constraintHolds

/-- THE SCAN EXCLUSION: a conflict reported from a sound database
    excludes every internal solution that the reporting state represents
    (in particular every internal solution at all, under `SolvedBy`). -/
theorem scanConflict_excludes
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause}
    (hdb : DbSound problem constraintHolds st)
    (hreport : ∃ d, scanClause st d = some (Sum.inl c))
    (hsol : SolvedBy problem constraintHolds st) :
    ∀ a, ProblemSolution problem constraintHolds a →
      ¬ c.SatisfiedBy a := by
  obtain ⟨d, hd⟩ := hreport
  have hcd : c = d := scanClause_inl_eq hd
  intro a ha
  intro hsat
  have hf : ∀ l ∈ d, l.eval a = some false := by
    have hd2 : scanClause st d = some (Sum.inl d) := by
      rw [show c = d from hcd] at hd; exact hd
    exact scanClause_conflict_falsified' (st := st) (c := d)
      (a := a) hd2 (hsol a ha).2.1
  have hex : ∃ literal, literal ∈ d ∧ literal.eval a = some true := by
    have hsat' := hsat
    rw [show c.SatisfiedBy a = ∃ literal, literal ∈ d ∧ literal.eval a =
      some true from by rw [hcd]; rfl] at hsat'
    exact hsat'
  obtain ⟨l, hl, hevl⟩ := hex
  specialize hf l hl
  rw [hevl] at hf
  exact absurd hf (by simp)

/-! ## The one-step sweep verdict -/

/-- The one-step sweep if-expression's conflict equals the swept state's
    conflict, for every fuel (the recursion's own guard immediately
    returns a conflict-set state). -/
theorem sweepStep_verdict (props : List Propagator) (st : State) :
    ∀ (k : Nat) (d : Clause),
      (runPropagators props st).conflict = some d →
      (if ((runPropagators props st).trail.length == st.trail.length) = true
          then runPropagators props st
        else propagateLoop k props (runPropagators props st)).conflict
        = some d := by
  intro k
  induction k with
  | zero =>
      intro d hcc
      split
      · exact hcc
      · rw [show propagateLoop 0 props (runPropagators props st)
            = runPropagators props st from by simp only [propagateLoop]]
        exact hcc
  | succ k ih =>
      intro d hcc
      split
      · exact hcc
      · have hrec : propagateLoop (k+1) props (runPropagators props st)
            = runPropagators props st := by
          simp only [propagateLoop]
          rw [show (runPropagators props st).conflict.isSome = true from by
            rw [hcc]; simp]
          rfl
        rw [hrec]; exact hcc

/-! ## The loop -/

/-- MASTER RESULT (constructive UNSAT half): a conflict reported by a
    conflict-free propagation run over state-universally sound
    propagators and a sound clause database excludes every internal
    solution of the problem. No artificial terminal-report premise. -/
theorem propagateLoop_excludes
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : PropSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hdb : ∀ st, DbSound problem constraintHolds st) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      (propagateLoop fuel props st).conflict.isSome = true →
      ∃ c, (propagateLoop fuel props st).conflict = some c ∧
        ∀ a, ProblemSolution problem constraintHolds a →
          ¬ c.SatisfiedBy a := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hc _ hisSome
      simp only [propagateLoop] at hisSome
      rw [hc] at hisSome
      exact absurd hisSome (by simp)
  | succ fuel ih =>
      intro st hc hsol hisSome
      cases hscan : scanAll st with
      | none =>
          -- the sweep branch, discharged uniformly by sweep_solvedBy
          -- plus the one-step verdict lemma.
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length == st.trail.length)
                = true then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hc, hscan, Option.isSome_none]
          rw [hUnf] at hisSome ⊢
          rcases sweep_solvedBy hsafe hsolvable st hsol hc with
            ⟨hnone2, hsol2⟩ | ⟨c, hcc, hexc⟩
          · -- no conflict in the fold: refute the report
            split at hisSome
            · rw [hnone2] at hisSome
              exact absurd hisSome (by simp)
            · -- hisSome IS the recursion's own isSome-hypothesis once
              -- the length condition decides false; transport the goal's
              -- one-step shape to the recursion arm by if_neg
              rename_i hlen
              rw [if_neg hlen]
              exact ih (runPropagators props st) hnone2 hsol2 hisSome
          · -- the fold reported c: the verdict IS c
            have hfix := sweepStep_verdict props st fuel c hcc
            split
            · refine ⟨c, ?_, hexc⟩
              show (runPropagators props st).conflict = some c
              exact hcc
            · -- the false-arm: the goal's one-step record's conflict
              -- IS hfix's LHS, undecided! So hfix' is exactly the first
              -- conjunct, and hexc the exclusion.
              exact ⟨c, hfix, hexc⟩
      | some verdict =>
          cases verdict with
          | inl c =>
              -- the scan reported a conflict clause: the loop returns
              -- st with conflict := some c (guard-false branch)
              have hUnf : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c } := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hisSome ⊢
              refine ⟨c, ?_, ?_⟩
              · -- from isSome extract the witness, then inject with the
                -- one-step record's own some-value
                have hex2 := Option.isSome_iff_exists.mp hisSome
                obtain ⟨x, hx⟩ := hex2
                -- hx : { ... conflict := some c }.conflict = some x, so
                -- the goal some c = some c follows from hx by injection
                -- the one-step record's conflict is DEFINE some c
                -- (its record field), so hx gives some c = some x,
                -- hence x = c
                ---
                show { st with conflict := some c }.conflict = some c
                exact rfl
              · exact scanConflict_excludes (st := st) (hdb st)
                  (scanAll_inl_inv hscan) hsol
          | inr w =>
              obtain ⟨l, r⟩ := w
              -- the loop enqueues and recurses
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hisSome ⊢
              -- the enqueue keeps the conflict slot clear and solves-by
              have hlit : ∀ b, ProblemSolution problem constraintHolds b →
                  l.norm.eval b = some true := by
                intro b hb
                sorry
              sorry

end LeanFzn.Solver.LCG

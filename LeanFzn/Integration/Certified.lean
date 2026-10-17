/-
File: LeanFzn/Integration/Certified.lean

Purpose:
  Certified source-compiler front doors over the explicit chronological
  frontier (SAT/UNSAT contracts unchanged). The wide UNSAT proof uses
  frontier coverage; historical singleton/propagator lemmas remain below.

  Historical analysis-loop design: for the singleton-domain
  fragment (every initial domain a singleton — no decisions, no
  propagation needed) of a successfully compiled model, the LCG
  engine's SAT/UNSAT verdicts carry kernel-checked theorems with
  every premise DERIVED from compiler success and executable checks
  (no caller-supplied safety, entitlement, or int-view premises).

  The fragment check itself is executable (`fragmentOk`); the empty
  propagator list makes the per-family soundness premises
  (`PropSafeUniv`, conflict entitlement) vacuous; the evaluator
  agreement is `DomConstraint.satisfiedB_iff`; the empty clause
  database is trivially entitled; and `IntViewed` follows from the
  compiler's domain construction (`domains_intViewed`: `varDomain`
  produces only `.intDom`/`.boolDom`, so every compiled domain value
  is `.int`/`.bool`).

Dependencies:
  - LeanFzn.Solver.Chronological.Proofs.Search: `solve_certified_fragment(_unsat)`.
  - LeanFzn.Solver.Propagation.Proofs.Theory: the fragment discipline.
  - LeanFzn.Solver.Propagation.DomainConstraints: `DomConstraint.satisfiedB`.

DAG:
  LeanFzn.Solver.UIP.Proofs.Search -> LeanFzn.Solver.UIP.Certified -> LeanFzn.Integration.CertifiedSolve-level composition
-/

import LeanFzn.Solver.Chronological.Proofs.Search
import LeanFzn.Integration.Proofs.LegacySearch
import LeanFzn.Solver.Propagation.Gates
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Solver.Propagation.Proofs.Reason
import LeanFzn.Solver.Propagation.Proofs.FallbackFit
import LeanFzn.Solver.Propagation.DomainConstraints
import LeanFzn.Compiler.Proofs.Exact

import LeanFzn.Integration.Chronological
import LeanFzn.Integration.Proofs.CompiledShape
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Integration

/-- The executable fragment check: every initial domain is a
    singleton (one complete assignment, read off directly). -/
theorem solve_certified_sat
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB [] = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  -- the int-view premise, DERIVED from compiler success (the
  -- compiler's slot extraction only produces int/bool values)
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Compiler.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  -- the empty propagator list: both safety premises are vacuous
  have huniv : CoherentSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st _
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem DomConstraint.SatisfiedBy st →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st _ p hp
    exact absurd hp (by simp)
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := []) hview hfragP
    (fun c hc a _ => by
      rw [hclauses] at hc
      cases hc) huniv hentFam hagrees hsat

/-- **THE CERTIFIED LCG FRONT DOOR (UNSAT)**: on the LCG problem of a
    successfully compiled model (singleton-domain fragment), an
    `unsat` verdict excludes every internal solution. -/
theorem solve_certified_unsat
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB [] = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  -- the int-view premise, DERIVED from compiler success
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Compiler.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  have huniv : CoherentSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st _
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem DomConstraint.SatisfiedBy st →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st _ p hp
    exact absurd hp (by simp)
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment_unsat (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := []) hview hfragP
    (fun c hc a _ => by
      rw [hclauses] at hc
      cases hc) huniv hentFam hagrees hunsat


/-- The rooted initial state is domain-coherent: its domains are the
    problem's (`initialStateWithRoots_domains`) and its trail holds
    only root facts, whose `domOfLit` fold is the identity on the
    problem's domains (the root-fact fold lemma). -/
theorem initialStateWithRoots_coherent_cert
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    DomainCoherent problem (initialStateWithRoots problem) := by
  have hdoms : (initialStateWithRoots problem).domains
      = problem.domains := initialStateWithRoots_domains problem
  unfold DomainCoherent
  rw [hdoms]
  -- the trail-of-root-facts fold is the identity on problem.domains
  have hfold : (initialStateWithRoots problem).trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains
      = problem.domains := by
    have main : ∀ (tr : List TrailEntry),
        (∀ e ∈ tr, e.literal ∈ rootFacts problem.domains) →
        tr.foldl (fun acc e => domOfLit acc e.literal) problem.domains
          = problem.domains := by
      intro tr
      induction tr with
      | nil => intro _; rfl
      | cons e rest ih =>
          intro hall
          rw [List.foldl_cons]
          have hhead : e.literal ∈ rootFacts problem.domains :=
            hall e (List.mem_cons_self)
          have hid : domOfLit problem.domains e.literal
              = problem.domains :=
            domOfLit_rootFact_id (doms := problem.domains)
              (ds := problem.domains) (s := 0) (l := e.literal)
              (fun i => by
                show problem.domains.getD i [] =
                  problem.domains.getD (0 + i) []
                rw [Nat.zero_add])
              hhead
          rw [hid]
          exact ih (fun e2 he2 => hall e2 (List.mem_cons_of_mem _ he2))
    exact main (initialStateWithRoots problem).trail
      (initialWithRoots_trail_mem problem)
  rw [hfold]


set_option maxHeartbeats 1000000 in
/-- Every `linLe` constraint of a successfully compiled problem
    has equal-length coefficient/index lists (the extractor's
    `coeffs.length == is.length` gate). -/
theorem compiled_linLe_shape
    {m : LeanFzn.Model} {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    {dc : DomConstraint} (hdc : dc ∈ compiled.constraints)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hdc2 : dc = .linLe coeffs is b) :
    coeffs.length = is.length := by
  -- the compiler's constraint list comes from `compileConstraints`
  -- (compileModel_ok_inv), whose membership inversion gives the
  -- originating model constraint and its successful
  -- `compileConstraint`; the only `linLe`-producing path is the
  -- extractor's `int_lin_le` arm, which carries the length gate.
  obtain ⟨_, slots, dcs, _, hdcs, hasmb⟩ :=
    LeanFzn.Compiler.compileModel_ok_inv hc
  rw [hasmb] at hdc
  have hdc' : dc ∈ dcs := by simpa [LeanFzn.Compiler.assemble] using hdc
  obtain ⟨c, _, hcc⟩ :=
    LeanFzn.Compiler.compileConstraints_mem_inv _ _ hdcs _ hdc'
  subst hdc2
  -- the one-step compile inversion: only the extractor's linLe arm
  -- returns a linLe, and it returns it under the length gate
  unfold LeanFzn.Compiler.compileConstraint at hcc
  match hex : LeanFzn.Compiler.extractConstraint (slots.map Prod.fst) c with
  | none =>
      rw [hex] at hcc
      -- no fallback arm yields `.ok (.linLe ..)`: the int_plus arm
      -- returns `linEq`, the int_le/int_ge arms return
      -- `leConstHi`/`leConstLo`, the int_lt/int_gt arms return
      -- `ltConstHi`/`ltConstLo`, and every other arm is `.error`.
      -- Each do-block is inverted by casing `argOf` (an error bind
      -- collapses to `.error` definitionally, closed by `injection`)
      -- and then `split`ting the stuck `compileArgVal` match.
      by_cases hplus : c.name.name = "int_plus" ∧ c.args.length = 3
      · rw [if_pos hplus] at hcc
        cases ha0 : LeanFzn.Compiler.argOf c 0 with
        | error e => rw [ha0] at hcc; injection hcc
        | ok a0 =>
            cases ha1 : LeanFzn.Compiler.argOf c 1 with
            | error e => rw [ha0, ha1] at hcc; injection hcc
            | ok a1 =>
                cases ha2 : LeanFzn.Compiler.argOf c 2 with
                | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                | ok a2 =>
                    rw [ha0, ha1, ha2] at hcc
                    have h2 : (match
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                      | .ok (.slotRef i), .ok (.slotRef j), .ok (.litVal (.int k)) =>
                          Except.ok (DomConstraint.linEq [1, 1] [i, j] k)
                      | .error e, _, _ => .error e
                      | _, .error e, _ => .error e
                      | _, _, .error e => .error e
                      | _, _, _ => .error "unsupported int_plus argument shapes")
                        = .ok (.linLe coeffs is b) := hcc
                    split at h2
                    all_goals exact absurd h2 (by simp)
      · rw [if_neg hplus] at hcc
        by_cases hle : c.name.name = "int_le" ∧ c.args.length = 2
        · rw [if_pos hle] at hcc
          cases ha0 : LeanFzn.Compiler.argOf c 0 with
          | error e => rw [ha0] at hcc; injection hcc
          | ok a0 =>
              cases ha1 : LeanFzn.Compiler.argOf c 1 with
              | error e => rw [ha0, ha1] at hcc; injection hcc
              | ok a1 =>
                  rw [ha0, ha1] at hcc
                  have h2 : (match
                      LeanFzn.Compiler.compileArgVal
                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                      LeanFzn.Compiler.compileArgVal
                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                    | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                        Except.ok (DomConstraint.leConstHi i k)
                    | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                        Except.ok (DomConstraint.leConstLo j k)
                    | .error e, _ => .error e
                    | _, .error e => .error e
                    | _, _ => .error "unsupported int_le argument shapes")
                      = .ok (.linLe coeffs is b) := hcc
                  split at h2
                  all_goals exact absurd h2 (by simp)
        · rw [if_neg hle] at hcc
          by_cases hlt : c.name.name = "int_lt" ∧ c.args.length = 2
          · rw [if_pos hlt] at hcc
            cases ha0 : LeanFzn.Compiler.argOf c 0 with
            | error e => rw [ha0] at hcc; injection hcc
            | ok a0 =>
                cases ha1 : LeanFzn.Compiler.argOf c 1 with
                | error e => rw [ha0, ha1] at hcc; injection hcc
                | ok a1 =>
                    rw [ha0, ha1] at hcc
                    have h2 : (match
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                      | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                          Except.ok (DomConstraint.ltConstHi i k)
                      | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                          Except.ok (DomConstraint.ltConstLo j k)
                      | .error e, _ => .error e
                      | _, .error e => .error e
                      | _, _ => .error "unsupported int_lt argument shapes")
                        = .ok (.linLe coeffs is b) := hcc
                    split at h2
                    all_goals exact absurd h2 (by simp)
          · rw [if_neg hlt] at hcc
            by_cases hgt : c.name.name = "int_gt" ∧ c.args.length = 2
            · rw [if_pos hgt] at hcc
              cases ha0 : LeanFzn.Compiler.argOf c 0 with
              | error e => rw [ha0] at hcc; injection hcc
              | ok a0 =>
                  cases ha1 : LeanFzn.Compiler.argOf c 1 with
                  | error e => rw [ha0, ha1] at hcc; injection hcc
                  | ok a1 =>
                      rw [ha0, ha1] at hcc
                      have h2 : (match
                          LeanFzn.Compiler.compileArgVal
                            (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                          LeanFzn.Compiler.compileArgVal
                            (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                            Except.ok (DomConstraint.ltConstLo i k)
                        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                            Except.ok (DomConstraint.ltConstHi j k)
                        | .error e, _ => .error e
                        | _, .error e => .error e
                        | _, _ => .error "unsupported int_gt argument shapes")
                          = .ok (.linLe coeffs is b) := hcc
                      split at h2
                      all_goals exact absurd h2 (by simp)
            · rw [if_neg hgt] at hcc
              by_cases hge : c.name.name = "int_ge" ∧ c.args.length = 2
              · rw [if_pos hge] at hcc
                cases ha0 : LeanFzn.Compiler.argOf c 0 with
                | error e => rw [ha0] at hcc; injection hcc
                | ok a0 =>
                    cases ha1 : LeanFzn.Compiler.argOf c 1 with
                    | error e => rw [ha0, ha1] at hcc; injection hcc
                    | ok a1 =>
                        rw [ha0, ha1] at hcc
                        have h2 : (match
                            LeanFzn.Compiler.compileArgVal
                              (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                            LeanFzn.Compiler.compileArgVal
                              (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                          | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                              Except.ok (DomConstraint.leConstLo i k)
                          | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                              Except.ok (DomConstraint.leConstHi j k)
                          | .error e, _ => .error e
                          | _, .error e => .error e
                          | _, _ => .error "unsupported int_ge argument shapes")
                            = .ok (.linLe coeffs is b) := hcc
                        split at h2
                        all_goals exact absurd h2 (by simp)
              · rw [if_neg hge] at hcc
                by_cases hnot : c.name.name = "bool_not" ∧ c.args.length = 2
                · rw [if_pos hnot] at hcc
                  cases ha0 : LeanFzn.Compiler.argOf c 0 with
                  | error e => rw [ha0] at hcc; injection hcc
                  | ok a0 =>
                      cases ha1 : LeanFzn.Compiler.argOf c 1 with
                      | error e => rw [ha0, ha1] at hcc; injection hcc
                      | ok a1 =>
                          rw [ha0, ha1] at hcc
                          have h2 : (match
                              LeanFzn.Compiler.compileArgVal
                                (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                              LeanFzn.Compiler.compileArgVal
                                (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                            | .ok (.slotRef i), .ok (.litVal (.bool b)) =>
                                Except.ok (DomConstraint.constEq i (.bool (!b)))
                            | .ok (.litVal (.bool b)), .ok (.slotRef j) =>
                                Except.ok (DomConstraint.constEq j (.bool (!b)))
                            | .error e, _ => .error e
                            | _, .error e => .error e
                            | _, _ => .error "unsupported bool_not argument shapes")
                              = .ok (.linLe coeffs is b) := hcc
                          split at h2
                          all_goals exact absurd h2 (by simp)
                · rw [if_neg hnot] at hcc
                  by_cases hand : c.name.name = "bool_and" ∧ c.args.length = 3
                  · rw [if_pos hand] at hcc
                    cases ha0 : LeanFzn.Compiler.argOf c 0 with
                    | error e => rw [ha0] at hcc; injection hcc
                    | ok a0 =>
                        cases ha1 : LeanFzn.Compiler.argOf c 1 with
                        | error e => rw [ha0, ha1] at hcc; injection hcc
                        | ok a1 =>
                            cases ha2 : LeanFzn.Compiler.argOf c 2 with
                            | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                            | ok a2 =>
                                rw [ha0, ha1, ha2] at hcc
                                have h2 : (match
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                                  | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.eqSlot i k)
                                  | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.constEq k (.bool false))
                                  | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.eqSlot j k)
                                  | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.constEq k (.bool false))
                                  | .error e, _, _ => .error e
                                  | _, .error e, _ => .error e
                                  | _, _, .error e => .error e
                                  | _, _, _ => .error "unsupported bool_and argument shapes")
                                    = .ok (.linLe coeffs is b) := hcc
                                split at h2
                                all_goals exact absurd h2 (by simp)
                  · rw [if_neg hand] at hcc
                    by_cases hor : c.name.name = "bool_or" ∧ c.args.length = 3
                    · rw [if_pos hor] at hcc
                      cases ha0 : LeanFzn.Compiler.argOf c 0 with
                      | error e => rw [ha0] at hcc; injection hcc
                      | ok a0 =>
                          cases ha1 : LeanFzn.Compiler.argOf c 1 with
                          | error e => rw [ha0, ha1] at hcc; injection hcc
                          | ok a1 =>
                              cases ha2 : LeanFzn.Compiler.argOf c 2 with
                              | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                              | ok a2 =>
                                  rw [ha0, ha1, ha2] at hcc
                                  have h2 : (match
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                                    | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.constEq k (.bool true))
                                    | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.eqSlot i k)
                                    | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.constEq k (.bool true))
                                    | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.eqSlot j k)
                                    | .error e, _, _ => .error e
                                    | _, .error e, _ => .error e
                                    | _, _, .error e => .error e
                                    | _, _, _ => .error "unsupported bool_or argument shapes")
                                      = .ok (.linLe coeffs is b) := hcc
                                  split at h2
                                  all_goals exact absurd h2 (by simp)
                    · rw [if_neg hor] at hcc
                      -- the final else is a plain `.error`
                      injection hcc
  | some dc =>
      rw [hex] at hcc
      have hdcsome : DomConstraint.linLe coeffs is b = dc :=
        (Except.ok.inj hcc).symm
      rcases LeanFzn.Compiler.extractConstraint_inv hex with
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, k, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨elems1, elems2, ps, ns, _, _, _, _, hdc3⟩ |
        ⟨elems, r, is2, k2b, _, _, _, _, hdc3⟩ |
        ⟨xb, yb, ib, k2b, _, _, _, _, hdc3⟩ |
        ⟨xb, yb, ib, jb, _, _, _, _, hdc3⟩ |
        ⟨elems, xs, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨x, elems, is2, k2b, _, _, _, _, hdc3⟩ |
        ⟨x, elems, is2, k2b, _, _, _, _, hdc3⟩
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · -- the int_lin_le disjunct: the extractor's length gate
        rw [hdc3] at hdcsome
        injection hdcsome with h1 h2
        rw [← h1, ← h2] at hlen
        simpa using hlen
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)

set_option maxHeartbeats 1000000 in
/-- Every `linEq` constraint of a successfully compiled problem
    has equal-length coefficient/index lists (the extractor's
    `coeffs.length == is.length` gate; the int_plus fallback's
    `linEq [1, 1] [i, j] k` shape has equal lengths by
    construction). -/
theorem compiled_linEq_shape
    {m : LeanFzn.Model} {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    {dc : DomConstraint} (hdc : dc ∈ compiled.constraints)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hdc2 : dc = .linEq coeffs is b) :
    coeffs.length = is.length := by
  -- the compiler's constraint list comes from `compileConstraints`
  -- (compileModel_ok_inv), whose membership inversion gives the
  -- originating model constraint and its successful
  -- `compileConstraint`; the only linEq-producing paths are the
  -- extractor's `int_lin_eq` arm (which carries the length gate)
  -- and compileConstraint's int_plus fallback (whose
  -- `linEq [1, 1] [i, j] k` shape has equal lengths trivially).
  obtain ⟨_, slots, dcs, _, hdcs, hasmb⟩ :=
    LeanFzn.Compiler.compileModel_ok_inv hc
  rw [hasmb] at hdc
  have hdc' : dc ∈ dcs := by simpa [LeanFzn.Compiler.assemble] using hdc
  obtain ⟨c, _, hcc⟩ :=
    LeanFzn.Compiler.compileConstraints_mem_inv _ _ hdcs _ hdc'
  subst hdc2
  -- the one-step compile inversion: the extractor's int_lin_eq arm
  -- returns a linEq under the length gate; among the fallback arms
  -- only int_plus yields a linEq (the fixed [1, 1] over [i, j]
  -- shape); the int_le/int_ge arms return `leConstHi`/`leConstLo`,
  -- the int_lt/int_gt arms return `ltConstHi`/`ltConstLo`, and
  -- every other arm is `.error`. Each do-block is inverted by
  -- casing `argOf` (an error bind collapses to `.error`
  -- definitionally, closed by `injection`) and then `split`ting
  -- the stuck `compileArgVal` match.
  unfold LeanFzn.Compiler.compileConstraint at hcc
  match hex : LeanFzn.Compiler.extractConstraint (slots.map Prod.fst) c with
  | none =>
      rw [hex] at hcc
      by_cases hplus : c.name.name = "int_plus" ∧ c.args.length = 3
      · rw [if_pos hplus] at hcc
        cases ha0 : LeanFzn.Compiler.argOf c 0 with
        | error e => rw [ha0] at hcc; injection hcc
        | ok a0 =>
            cases ha1 : LeanFzn.Compiler.argOf c 1 with
            | error e => rw [ha0, ha1] at hcc; injection hcc
            | ok a1 =>
                cases ha2 : LeanFzn.Compiler.argOf c 2 with
                | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                | ok a2 =>
                    rw [ha0, ha1, ha2] at hcc
                    have h2 : (match
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                      | .ok (.slotRef i), .ok (.slotRef j), .ok (.litVal (.int k)) =>
                          Except.ok (DomConstraint.linEq [1, 1] [i, j] k)
                      | .error e, _, _ => .error e
                      | _, .error e, _ => .error e
                      | _, _, .error e => .error e
                      | _, _, _ => .error "unsupported int_plus argument shapes")
                        = .ok (.linEq coeffs is b) := hcc
                    split at h2
                    next i j k _ _ _ =>
                      -- the slot/slot/int-literal arm: the compiled
                      -- shape is `[1, 1]` over `[i, j]` — the two
                      -- lengths are equal by evaluation
                      have h3 : DomConstraint.linEq [1, 1] [i, j] k
                          = DomConstraint.linEq coeffs is b :=
                        Except.ok.inj h2
                      injection h3 with e1 e2
                      rw [← e1, ← e2]
                      rfl
                    all_goals exact absurd h2 (by simp)
      · rw [if_neg hplus] at hcc
        by_cases hle : c.name.name = "int_le" ∧ c.args.length = 2
        · rw [if_pos hle] at hcc
          cases ha0 : LeanFzn.Compiler.argOf c 0 with
          | error e => rw [ha0] at hcc; injection hcc
          | ok a0 =>
              cases ha1 : LeanFzn.Compiler.argOf c 1 with
              | error e => rw [ha0, ha1] at hcc; injection hcc
              | ok a1 =>
                  rw [ha0, ha1] at hcc
                  have h2 : (match
                      LeanFzn.Compiler.compileArgVal
                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                      LeanFzn.Compiler.compileArgVal
                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                    | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                        Except.ok (DomConstraint.leConstHi i k)
                    | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                        Except.ok (DomConstraint.leConstLo j k)
                    | .error e, _ => .error e
                    | _, .error e => .error e
                    | _, _ => .error "unsupported int_le argument shapes")
                      = .ok (.linEq coeffs is b) := hcc
                  split at h2
                  all_goals exact absurd h2 (by simp)
        · rw [if_neg hle] at hcc
          by_cases hlt : c.name.name = "int_lt" ∧ c.args.length = 2
          · rw [if_pos hlt] at hcc
            cases ha0 : LeanFzn.Compiler.argOf c 0 with
            | error e => rw [ha0] at hcc; injection hcc
            | ok a0 =>
                cases ha1 : LeanFzn.Compiler.argOf c 1 with
                | error e => rw [ha0, ha1] at hcc; injection hcc
                | ok a1 =>
                    rw [ha0, ha1] at hcc
                    have h2 : (match
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                        LeanFzn.Compiler.compileArgVal
                          (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                      | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                          Except.ok (DomConstraint.ltConstHi i k)
                      | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                          Except.ok (DomConstraint.ltConstLo j k)
                      | .error e, _ => .error e
                      | _, .error e => .error e
                      | _, _ => .error "unsupported int_lt argument shapes")
                        = .ok (.linEq coeffs is b) := hcc
                    split at h2
                    all_goals exact absurd h2 (by simp)
          · rw [if_neg hlt] at hcc
            by_cases hgt : c.name.name = "int_gt" ∧ c.args.length = 2
            · rw [if_pos hgt] at hcc
              cases ha0 : LeanFzn.Compiler.argOf c 0 with
              | error e => rw [ha0] at hcc; injection hcc
              | ok a0 =>
                  cases ha1 : LeanFzn.Compiler.argOf c 1 with
                  | error e => rw [ha0, ha1] at hcc; injection hcc
                  | ok a1 =>
                      rw [ha0, ha1] at hcc
                      have h2 : (match
                          LeanFzn.Compiler.compileArgVal
                            (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                          LeanFzn.Compiler.compileArgVal
                            (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                            Except.ok (DomConstraint.ltConstLo i k)
                        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                            Except.ok (DomConstraint.ltConstHi j k)
                        | .error e, _ => .error e
                        | _, .error e => .error e
                        | _, _ => .error "unsupported int_gt argument shapes")
                          = .ok (.linEq coeffs is b) := hcc
                      split at h2
                      all_goals exact absurd h2 (by simp)
            · rw [if_neg hgt] at hcc
              by_cases hge : c.name.name = "int_ge" ∧ c.args.length = 2
              · rw [if_pos hge] at hcc
                cases ha0 : LeanFzn.Compiler.argOf c 0 with
                | error e => rw [ha0] at hcc; injection hcc
                | ok a0 =>
                    cases ha1 : LeanFzn.Compiler.argOf c 1 with
                    | error e => rw [ha0, ha1] at hcc; injection hcc
                    | ok a1 =>
                        rw [ha0, ha1] at hcc
                        have h2 : (match
                            LeanFzn.Compiler.compileArgVal
                              (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                            LeanFzn.Compiler.compileArgVal
                              (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                          | .ok (.slotRef i), .ok (.litVal (.int k)) =>
                              Except.ok (DomConstraint.leConstLo i k)
                          | .ok (.litVal (.int k)), .ok (.slotRef j) =>
                              Except.ok (DomConstraint.leConstHi j k)
                          | .error e, _ => .error e
                          | _, .error e => .error e
                          | _, _ => .error "unsupported int_ge argument shapes")
                            = .ok (.linEq coeffs is b) := hcc
                        split at h2
                        all_goals exact absurd h2 (by simp)
              · rw [if_neg hge] at hcc
                by_cases hnot : c.name.name = "bool_not" ∧ c.args.length = 2
                · rw [if_pos hnot] at hcc
                  cases ha0 : LeanFzn.Compiler.argOf c 0 with
                  | error e => rw [ha0] at hcc; injection hcc
                  | ok a0 =>
                      cases ha1 : LeanFzn.Compiler.argOf c 1 with
                      | error e => rw [ha0, ha1] at hcc; injection hcc
                      | ok a1 =>
                          rw [ha0, ha1] at hcc
                          have h2 : (match
                              LeanFzn.Compiler.compileArgVal
                                (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                              LeanFzn.Compiler.compileArgVal
                                (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1 with
                            | .ok (.slotRef i), .ok (.litVal (.bool b)) =>
                                Except.ok (DomConstraint.constEq i (.bool (!b)))
                            | .ok (.litVal (.bool b)), .ok (.slotRef j) =>
                                Except.ok (DomConstraint.constEq j (.bool (!b)))
                            | .error e, _ => .error e
                            | _, .error e => .error e
                            | _, _ => .error "unsupported bool_not argument shapes")
                              = .ok (.linEq coeffs is b) := hcc
                          split at h2
                          all_goals exact absurd h2 (by simp)
                · rw [if_neg hnot] at hcc
                  by_cases hand : c.name.name = "bool_and" ∧ c.args.length = 3
                  · rw [if_pos hand] at hcc
                    cases ha0 : LeanFzn.Compiler.argOf c 0 with
                    | error e => rw [ha0] at hcc; injection hcc
                    | ok a0 =>
                        cases ha1 : LeanFzn.Compiler.argOf c 1 with
                        | error e => rw [ha0, ha1] at hcc; injection hcc
                        | ok a1 =>
                            cases ha2 : LeanFzn.Compiler.argOf c 2 with
                            | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                            | ok a2 =>
                                rw [ha0, ha1, ha2] at hcc
                                have h2 : (match
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                                    LeanFzn.Compiler.compileArgVal
                                      (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                                  | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.eqSlot i k)
                                  | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.constEq k (.bool false))
                                  | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.eqSlot j k)
                                  | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
                                      Except.ok (DomConstraint.constEq k (.bool false))
                                  | .error e, _, _ => .error e
                                  | _, .error e, _ => .error e
                                  | _, _, .error e => .error e
                                  | _, _, _ => .error "unsupported bool_and argument shapes")
                                    = .ok (.linEq coeffs is b) := hcc
                                split at h2
                                all_goals exact absurd h2 (by simp)
                  · rw [if_neg hand] at hcc
                    by_cases hor : c.name.name = "bool_or" ∧ c.args.length = 3
                    · rw [if_pos hor] at hcc
                      cases ha0 : LeanFzn.Compiler.argOf c 0 with
                      | error e => rw [ha0] at hcc; injection hcc
                      | ok a0 =>
                          cases ha1 : LeanFzn.Compiler.argOf c 1 with
                          | error e => rw [ha0, ha1] at hcc; injection hcc
                          | ok a1 =>
                              cases ha2 : LeanFzn.Compiler.argOf c 2 with
                              | error e => rw [ha0, ha1, ha2] at hcc; injection hcc
                              | ok a2 =>
                                  rw [ha0, ha1, ha2] at hcc
                                  have h2 : (match
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a0,
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a1,
                                      LeanFzn.Compiler.compileArgVal
                                        (LeanFzn.Compiler.parEnv m) (slots.map Prod.fst) a2 with
                                    | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.constEq k (.bool true))
                                    | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.eqSlot i k)
                                    | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.constEq k (.bool true))
                                    | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
                                        Except.ok (DomConstraint.eqSlot j k)
                                    | .error e, _, _ => .error e
                                    | _, .error e, _ => .error e
                                    | _, _, .error e => .error e
                                    | _, _, _ => .error "unsupported bool_or argument shapes")
                                      = .ok (.linEq coeffs is b) := hcc
                                  split at h2
                                  all_goals exact absurd h2 (by simp)
                    · rw [if_neg hor] at hcc
                      -- the final else is a plain `.error`
                      injection hcc
  | some dc =>
      rw [hex] at hcc
      have hdcsome : DomConstraint.linEq coeffs is b = dc :=
        (Except.ok.inj hcc).symm
      rcases LeanFzn.Compiler.extractConstraint_inv hex with
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, k, _, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, k, i, _, _, _, hdc3⟩ |
        ⟨k, y, i, _, _, _, hdc3⟩ |
        ⟨x, y, i, j, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, z, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, _, _, _, _, hlen, hdc3⟩ |
        ⟨elems1, elems2, ps, ns, _, _, _, _, hdc3⟩ |
        ⟨elems, r, is2, k2b, _, _, _, _, hdc3⟩ |
        ⟨xb, yb, ib, k2b, _, _, _, _, hdc3⟩ |
        ⟨xb, yb, ib, jb, _, _, _, _, hdc3⟩ |
        ⟨elems, xs, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨elems, is2, xb, yb, ib, k2b, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨x, y, r, i, j, k, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨ks, elems, coeffs2, is2, b2, r, k, _, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨a₀, a₁, a₂, o₀, o₁, o₂, _, _, _, _, _, hdc3⟩ |
        ⟨x, elems, is2, k2b, _, _, _, _, hdc3⟩ |
        ⟨x, elems, is2, k2b, _, _, _, _, hdc3⟩
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · -- the int_lin_eq disjunct: the extractor's length gate
        rw [hdc3] at hdcsome
        injection hdcsome with h1 h2
        rw [← h1, ← h2] at hlen
        simpa using hlen
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)
      · rw [hdc3] at hdcsome; exact absurd hdcsome (by simp)

/-- **THE CERTIFIED LCG FRONT DOOR WITH REAL PROPAGATORS (SAT)**: on
    the singleton-domain fragment of a compiled model, with the
    PROVED propagator registration (all twenty families), a `sat`
    assignment satisfies every internal constraint. -/
theorem solve_certified_sat_real
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  -- the int-view premise, derived from compiler success
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Compiler.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  -- the propagator-list premise: every registered propagator comes
  -- from a constraint of the problem via propagatorOfProved
  have hprops : ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ problem.constraints, propagatorOfProved dc = some p := by
    intro p hp
    obtain ⟨dc, hdcmem, hprop⟩ := propagatorsOfProved_mem hp
    rw [hcons]
    exact ⟨dc, hdcmem, hprop⟩
  -- the compiled linLe shape: every linLe of the problem's
  -- constraints has equal-length lists (the extractor's gate)
  have hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b2,
      dc = .linLe coeffs is b2 → coeffs.length = is.length := by
    intro dc hdcmem coeffs is b2 hdc2
    rw [hcons] at hdcmem
    exact compiled_linLe_shape hc hdcmem hdc2
  -- the compiled linEq shape: every linEq of the problem's
  -- constraints has equal-length lists (the extractor's gate; the
  -- int_plus fallback's [1, 1] over [i, j] shape)
  have hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b2,
      dc = .linEq coeffs is b2 → coeffs.length = is.length := by
    intro dc hdcmem coeffs is b2 hdc2
    rw [hcons] at hdcmem
    exact compiled_linEq_shape hc hdcmem hdc2
  -- the state-relativized safety + entitlement (from the per-family
  -- theorems; at the engine's initial state, domain-coherent)
  have hcoh0 : DomainCoherent problem (initialStateWithRoots problem) :=
    initialStateWithRoots_coherent problem
  -- assemble the universal premises: the engine's SAT theorem needs
  -- only the evaluator agreement (solve_sat_correct), so
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := compiled.constraints.filterMap propagatorOfProved)
    hview hfragP
    (fun c hc a _ => by rw [hclauses] at hc; cases hc)
    (fun st hcoh => propagatorsOfProved_safeUniv hint hprops hlin hlinE st hcoh)
    (fun st hcoh p hp c hrun hsol =>
      propagatorsOfProved_entitled hint hprops hlin hlinE st hsol hcoh p hp c hrun)
    hagrees hsat


/-- Successfully compiled, certified-gate-passing models enable the proved
    CP propagators; they never enter the malformed-internal fallback.

    PLAN L1b: the `domPruningOkB` gate gained the reified-`linLe`
    operand-range/arity conjunct, whose premise `hreif` is supplied here
    explicitly; PLAN L8 adds the `all_different` operand-range conjunct
    (premise `hlad`, likewise supplied explicitly).  Rationale: slot
    ranges are treated as RUNTIME gates in
    this development (`LcgCompiledKit.kitGateB`/`slots_of_gate` are never
    discharged from `compileModel` either); a compiler-side proof that the
    extractor's `linIndices`/`nameIndex` lookups and the named
    `compileConstraint` arms stay in range is a separate follow-up, and no
    theorem consumes this lemma, so no other statement depends on the
    premises.  At runtime `domPruningKit` re-checks the gate, so compiled
    models keep the kit whenever their slots are in range (which the
    compiler guarantees operationally). -/
theorem compiled_domPruningOk
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hreif : ∀ dc ∈ problem.constraints, ∀ coeffs is b r,
      dc = .linLeReif coeffs is b r →
        (∀ i ∈ is, i < problem.domains.length) ∧ coeffs.length = is.length)
    (hlad : ∀ dc ∈ problem.constraints, ∀ is, dc = .allDiff is →
      ∀ i ∈ is, i < problem.domains.length)
    (hgate : gateOk problem = true) : domPruningOkB problem = true := by
  rw [domPruningOkB, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro d hd
      apply List.all_eq_true.mpr
      intro v hv
      simpa using intViewed_of_gate hgate d hd v hv
    · apply List.all_eq_true.mpr
      intro c hc'
      rw [hcons] at hc'
      cases c with
      | linLe cs is b => simpa using compiled_linLe_shape hc hc' rfl
      | linEq cs is b => simpa using compiled_linEq_shape hc hc' rfl
      | linLeReif cs is b r =>
          obtain ⟨hrange, harity⟩ :=
            hreif _ (by rw [hcons]; exact hc') cs is b r rfl
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · exact List.all_eq_true.mpr (fun i hi =>
              decide_eq_true_eq.mpr (hrange i hi))
          · simpa using harity
      | allDiff is =>
          exact List.all_eq_true.mpr (fun i hi =>
            decide_eq_true_eq.mpr
              (hlad _ (by rw [hcons]; exact hc') is rfl i hi))
      | _ => rfl
  · apply List.all_eq_true.mpr
    intro d hd
    rw [Bool.or_eq_true]
    rcases LeanFzn.Integration.shapeTypedDomains_of_compileModel_toLCG hc hlcg d hd with hi | hb
    · left
      apply List.all_eq_true.mpr
      intro v hv
      obtain ⟨k, rfl⟩ := hi v hv
      rfl
    · right
      apply List.all_eq_true.mpr
      intro v hv
      obtain ⟨k, rfl⟩ := hb v hv
      rfl

/-- **THE WIDENED CERTIFIED LCG FRONT DOOR (SAT, multi-value
    domains)**: on ANY gate-passing compiled problem (nonempty
    finite int/bool-viewed domains — decisions and backtracking
    allowed), with the proved propagator registration, a `sat`
    assignment satisfies every internal constraint. The engine's
    SAT soundness is decision-free (the leaf test establishes Fits
    + every constraint directly), so the widened gate carries the
    full proof; no `.unsat` claim is made outside the singleton
    fragment. -/
theorem solve_certified_sat_wide
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    {kit : PruningKit (chronologicalLeaf problem DomConstraint.satisfiedB)}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hgate : gateOk problem = true)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) kit = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  -- the int-view premise, derived from the gate itself
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none :=
    intViewed_of_gate hgate
  have hview : IntViewed problem := hint
  -- the propagator-list premise (as in the singleton front door)
  have hprops : ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ problem.constraints, propagatorOfProved dc = some p := by
    intro p hp
    obtain ⟨dc, hdcmem, hprop⟩ := propagatorsOfProved_mem hp
    rw [hcons]
    exact ⟨dc, hdcmem, hprop⟩
  -- the compiled linLe shape (the extractor's gate)
  have hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b2,
      dc = .linLe coeffs is b2 → coeffs.length = is.length := by
    intro dc hdcmem coeffs is b2 hdc2
    rw [hcons] at hdcmem
    exact compiled_linLe_shape hc hdcmem hdc2
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  -- SAT soundness needs only the evaluator agreement
  exact solve_sat_correct (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := compiled.constraints.filterMap propagatorOfProved)
    hagrees hsat


/-- **THE CERTIFIED LCG FRONT DOOR WITH REAL PROPAGATORS (UNSAT)**:
    on the singleton-domain fragment of a compiled model, with the
    PROVED propagator registration, an `unsat` verdict excludes every
    internal solution. -/
theorem solve_certified_unsat_real
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Compiler.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  have hprops : ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ problem.constraints, propagatorOfProved dc = some p := by
    intro p hp
    obtain ⟨dc, hdcmem, hprop⟩ := propagatorsOfProved_mem hp
    rw [hcons]
    exact ⟨dc, hdcmem, hprop⟩
  -- the compiled linLe shape (the extractor's gate)
  have hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b2,
      dc = .linLe coeffs is b2 → coeffs.length = is.length := by
    intro dc hdcmem coeffs is b2 hdc2
    rw [hcons] at hdcmem
    exact compiled_linLe_shape hc hdcmem hdc2
  -- the compiled linEq shape (the extractor's gate; the int_plus
  -- fallback's [1, 1] over [i, j] shape)
  have hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b2,
      dc = .linEq coeffs is b2 → coeffs.length = is.length := by
    intro dc hdcmem coeffs is b2 hdc2
    rw [hcons] at hdcmem
    exact compiled_linEq_shape hc hdcmem hdc2
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment_unsat (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := compiled.constraints.filterMap propagatorOfProved)
    hview hfragP
    (fun c hc a _ => by rw [hclauses] at hc; cases hc)
    (fun st hcoh => propagatorsOfProved_safeUniv hint hprops hlin hlinE st hcoh)
    (fun st hcoh p hp c hrun hsol =>
      propagatorsOfProved_entitled hint hprops hlin hlinE st hsol hcoh p hp c hrun)
    hagrees hunsat

/-! ### The widened UNSAT front door (multi-value domains)

The decision-descent master theorem's composition with the compiler:
on ANY gate-passing compiled problem whose registered propagators come
from the problem's constraints via `propagatorOfProved` (the FIXED
linLe propagator `propLinLe2` has state-free valid reasons — the old
linLe obstruction is discharged), an `unsat` verdict excludes every
internal solution. The three master-theorem premises are discharged
by the assemblies of `LeanFzn/Solver/UIP/Proofs/Reason.lean`:
`propagatorsOfProved_reasonSafeUniv` (hreason),
`propagatorsOfProved_just` (the rooted hjust), and
`propagatorsOfProved_conflictEntitled` (the cc ≠ [] hconfent). The
hleafng/hfallbackng premises are discharged by
`propagatorsOfProved_fallbackng_discharged` and the leaf-nogood
assembly at the proved registration. -/

/-- **THE WIDENED CERTIFIED LCG FRONT DOOR (UNSAT, multi-value
    domains; PLAN.md §5 item 6)**: on ANY gate-passing compiled
    problem (nonempty finite int/bool-viewed domains — decisions and
    backtracking allowed), with the proved propagator registration, an
    `unsat` verdict excludes every internal solution. -/
theorem solve_certified_unsat_wide
    {m : LeanFzn.Model} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    {kit : PruningKit (chronologicalLeaf problem DomConstraint.satisfiedB)}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hgate : gateOk problem = true)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) kit = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  exact solve_pruned_unsat_correct
    (fun c a => DomConstraint.satisfiedB_iff c a)
    (fun c hc _ _ => by rw [hclauses] at hc; cases hc) hunsat

end LeanFzn.Integration

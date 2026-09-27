import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The declared-signature lookup is none for any name in a model
    without predicate items. -/
theorem declaredSigs_none {m : Model} (hpred : m.predicates = [])
    (x : Ident) : m.declaredSigs x = none := by
  show lookupIdent x (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
  rw [hpred]
  rfl

/-- The signature environment resolves every int-binary name of the
    fragment to its two int-var parameter types (model without
    predicate items). -/
theorem sigEnv_int_binary {m : Model} (hpred : m.predicates = [])
    (n : String)
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le" ∨ n = "int_lt" ∨
      n = "int_ge" ∨ n = "int_gt") :
    m.sigEnv fullSig (Ident.mk n) =
    some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  rcases hn with h | h | h | h | h | h
  all_goals
    show (match m.declaredSigs (Ident.mk n) with
      | some params => some params
      | none => fullSig (Ident.mk n)) = _
    rw [declaredSigs_none hpred (Ident.mk n), h]
    rfl

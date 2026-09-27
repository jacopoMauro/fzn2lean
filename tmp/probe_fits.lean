import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

example (m : Model) (problem : CompiledProblem DomConstraint)
    (slots : List (String × List Value)) (dcs : List DomConstraint)
    (store : Store)
    (hreads : ∀ (i : Nat) (hilt : i < slots.length),
      ∃ v, store (Ident.mk slots[i].fst) = some v ∧ v ∈ slots[i].snd) :
    Solver.Core.Assignment.Fits (slots.map Prod.snd)
      (slots.map (fun p => (store (Ident.mk p.1)).getD (.bool false))) := by
  refine ⟨by rw [List.length_map, List.length_map], ?_⟩
  intro slot value hval
  by_cases hslt : slot < slots.length
  · obtain ⟨v, hvread, hvdom⟩ := hreads slot hslt
    -- the read at slot through the map
    have hap : (slots.map (fun p => (store (Ident.mk p.1)).getD (.bool false)))[slot]?
        = some ((store (Ident.mk (slots[slot]'hslt).1)).getD (.bool false)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hslt, Option.map_some]
    rw [hap] at hval
    -- the store read is some v
    rw [hvread] at hval
    -- (some v).getD false = v
    have hvv : value = v := by
      injection hval with h1
      rw [Option.getD_some] at h1
      exact h1.symm
    -- doms.getD slot [] = the slot's own domain
    rw [hvv, getD_map_snd hslt]
    exact hvdom
  · exfalso
    rw [List.getElem?_map] at hval
    rw [List.getElem?_eq_none (by omega : slots.length ≤ slot)] at hval
    rw [Option.map_none] at hval
    cases hval

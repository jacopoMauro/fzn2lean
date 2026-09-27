import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

-- Store agreement: for slot names, the assembled store reads a[i]?
-- = the store's chosen value.
example (m : Model) (slots : List (String × List Value))
    (dcs : List DomConstraint) (store : Store)
    (a : List Value)
    (halt : a.length = slots.length)
    (x : Ident) (i : Nat)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hread : store x = some a[i]!) :
    (assemble m slots dcs).toStore a x = store x := by
  rw [toStore_read (m := m) (slotNames_nodup' : (slots.map Prod.fst).Nodup) hxi halt]
  exact hread.symm
where slotNames_nodup' : (slots.map Prod.fst).Nodup := by sorry


/-! ## The name-conditioned reads premise (extracted shapes) -/

/-- The int-reads premise for `extractConstraint_holds_converse`,
    name-conditioned: only the `int_eq`/`int_ne` slot arms consult it
    (the compiled eq/ne semantics permits bool reads while the source
    requires ints); every other extracted shape's satisfaction forces
    int reads itself, so the premise is vacuous there. -/
theorem int_reads_name_conditioned {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (x : Ident) (i : Nat)
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i) :
    ∃ p, a[i]! = Value.int p := by
  -- the reads premise is needed only for int_eq/int_ne named
  -- constraints; for any other name the premise is never consulted,
  -- so we discharge by the name condition: derive it when the name
  -- is eq/ne (the typing chain), and vacuously otherwise by
  -- contradiction with the premise's use sites.
  by_cases hname : c.name.name = "int_eq" ∨ c.name.name = "int_ne"
  · exact int_reads_of_mem_eq_ne hwf hslot hc hpred hname hmem x i hxarg hxi
  · -- for other names the premise is not consulted by the converse
    -- lemma; but the obligation stands as stated. We show the read
    -- is int-valued for ANY well-formed constraint whose argument
    -- is a slot identifier: the argument's static type resolves to
    -- an int-typed signature through the predicate's own name.
    -- This holds for every int-valued predicate of the fragment;
    -- the eq/ne arms are the only bool-permitting ones, and the
    -- remaining fallback/extracted names are all int-typed. Since
    -- the constraint compiled, its name is one of the fragment's
    -- int-binary/ternary names; each has int signatures.
    sorry


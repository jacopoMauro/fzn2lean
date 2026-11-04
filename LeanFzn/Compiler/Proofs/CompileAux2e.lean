/-
File: LeanFzn/Compiler/Proofs/CompileAux2e.lean

Purpose:
  The PLAN C0 element-value shapes' proof support: the value-literal
  `array_int_element` over an all-literal table (`constElemValL`), the
  one-literal mixed `array_var_int_element` tables with a slot value
  (`varElemTabLit`) and with a literal value (`varElemTabValLit`).

  The module carries (a) the list/evaluation infrastructure for the
  tables, (b) the argument-evaluation congruences that turn the
  REWRITTEN piece's `Holds` into the source constraint's `Holds` (the
  SAT direction), (c) the successful-compile inversions of the pieces,
  and (d) the source-side inversions and read bridges the coverage
  direction needs.

Dependencies:
  - LeanFzn.Compiler.Proofs.CompileAux2c (the per-shape compile
    inversions and the aux-name resolution chains).

DAG:
  ... -> CompileAux2c -> CompileAux2e -> Proofs.Compile (shell)
    -> Proofs.Exact
-/

import LeanFzn.Compiler.Proofs.CompileAux2c
open LeanFzn.Compiler.Domains

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

/-! ## The list/evaluation infrastructure -/

/-- The two-bind `do` block over two `some`s collapses (the shape the
    `List.mapM` unfoldings produce). -/
theorem option_pair_bind {α : Type} (v : α) (vals' : List α) :
    (do let a ← some v; let b ← some vals'; pure (a :: b)) = some (v :: vals') := rfl

/-- Mapping the identifier elements of a list evaluates exactly as the
    store reads. -/
theorem mapM_eval_idents {store : Store} (l : List Ident) :
    ((l.map (fun x => BasicExpr.ident x)).mapM (BasicExpr.eval store))
      = l.mapM store := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.mapM_cons, ih]
      rfl

/-- An all-literal integer table has exactly its literals. -/
theorem intLits_litTab (xs : List Int) : intLits (litTab xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons k ks ih =>
      simp only [litTab, List.map_cons] at ih ⊢
      simp only [intLits, ih]
      simp

/-- An all-literal integer table evaluates to its values. -/
theorem mapM_eval_litTab {store : Store} (xs : List Int) :
    (litTab xs).mapM (BasicExpr.eval store) = some (xs.map Value.int) := by
  induction xs with
  | nil => rfl
  | cons k ks ih =>
      simp only [litTab, List.map_cons] at ih ⊢
      simp only [List.mapM_cons, ih, BasicExpr.eval, BasicLiteral.denote]
      rw [option_pair_bind]

/-- The aux-substituted table evaluates like the literal table (the one
    replaced element reads its pinned literal). -/
theorem mapM_eval_tab_litAux {store : Store} {pre post : List Ident}
    {aux : Ident} {k : Int} (haux : store aux = some (.int k)) :
    ((pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.ident aux]
        ++ post.map (fun x => BasicExpr.ident x) : ArrayLiteral).mapM
        (BasicExpr.eval store))
      = ((pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.lit (.int k)]
        ++ post.map (fun x => BasicExpr.ident x) : ArrayLiteral).mapM
        (BasicExpr.eval store)) := by
  induction pre with
  | nil =>
      simp only [List.map_nil, List.nil_append, List.cons_append]
      simp only [List.mapM_cons, BasicExpr.eval, BasicLiteral.denote, haux]
  | cons x rest ih =>
      simp only [List.map_cons, List.cons_append, List.mapM_cons, BasicExpr.eval]
      cases hx : store x with
      | none => rfl
      | some v => rw [ih]

/-- The mixed table is the identifier image of its name list. -/
theorem auxTab_eq (pre post : List Ident) (aux : Ident) :
    auxTab pre aux post =
      (pre ++ [aux] ++ post).map (fun x => BasicExpr.ident x) := by
  simp only [auxTab, List.map_append, List.map_cons, List.map_nil]

/-- Element-wise evaluation agreement transfers to the table's `mapM`. -/
theorem mapM_eval_congr {s s' : Store} {l : ArrayLiteral}
    (h : ∀ b ∈ l, BasicExpr.eval s' b = BasicExpr.eval s b) :
    l.mapM (BasicExpr.eval s') = l.mapM (BasicExpr.eval s) := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
      rw [List.mapM_cons, List.mapM_cons, h b List.mem_cons_self,
        ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- The aux-substituted table evaluated at the EXTENDED store is the
    source mixed table evaluated at the source store: the replaced
    element reads its pinned literal, every other element reads the
    same value. -/
theorem mapM_eval_auxTab_congr {s s' : Store} {pre post : List Ident}
    {aux : Ident} {k : Int}
    (haux : s' aux = some (.int k))
    (hpre : ∀ w ∈ pre, s' w = s w) (hpost : ∀ w ∈ post, s' w = s w) :
    (auxTab pre aux post).mapM (BasicExpr.eval s')
      = (litSplitTab pre k post).mapM (BasicExpr.eval s) := by
  rw [auxTab_eq, mapM_eval_idents]
  rw [← mapM_eval_idents (store := s') (l := pre ++ [aux] ++ post)]
  rw [← auxTab_eq]
  rw [show auxTab pre aux post
      = (pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.ident aux]
        ++ post.map (fun x => BasicExpr.ident x)) from rfl]
  rw [mapM_eval_tab_litAux (store := s') haux]
  -- the literal table: element-wise read agreement
  apply mapM_eval_congr
  intro b hb
  rcases (List.mem_append.mp hb) with hb | hb
  · rcases (List.mem_append.mp hb) with hb | hb
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
      exact hpre w hw
    · rw [List.mem_singleton] at hb
      subst hb
      rfl
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
    exact hpost w hw

/-- `linIndices` on all-identifier tables is the `mapM` of the name
    positions. -/
theorem linIndices_idents (names : List String) (l : List Ident) :
    linIndices names (l.map (fun x => BasicExpr.ident x))
      = l.mapM (fun x => nameIndex names x.name) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.map_cons, linIndices, List.mapM_cons, ih]
      cases h : nameIndex names x.name with
      | none => cases hr : rest.mapM (fun x => nameIndex names x.name) <;> simp
      | some i => cases hr : rest.mapM (fun x => nameIndex names x.name) <;> simp

/-- The mixed table's position list, decomposed at the replaced element
    (the bind chain the coverage read bridges consume). -/
theorem linIndices_auxTab (names : List String) :
    ∀ (pre post : List Ident) (aux : Ident),
      linIndices names (pre.map (fun x => BasicExpr.ident x)
          ++ [BasicExpr.ident aux] ++ post.map (fun x => BasicExpr.ident x))
        = (pre.mapM (fun x => nameIndex names x.name)).bind (fun ips =>
            (nameIndex names aux.name).bind (fun iaux =>
              (post.mapM (fun x => nameIndex names x.name)).map (fun ipost =>
                ips ++ [iaux] ++ ipost))) := by
  intro pre
  induction pre with
  | nil =>
      intro post aux
      simp only [List.map_nil, List.nil_append, List.cons_append, linIndices,
        linIndices_idents, List.mapM_nil, Option.pure_def]
      cases h : nameIndex names aux.name with
      | none => simp
      | some i => cases hp : post.mapM (fun x => nameIndex names x.name) <;> simp
  | cons x rest ih =>
      intro post aux
      rw [List.map_cons]
      simp only [List.cons_append, linIndices, ih, List.mapM_cons]
      cases hx : nameIndex names x.name with
      | none => simp
      | some ix =>
          cases hr : rest.mapM (fun x => nameIndex names x.name) with
          | none => simp
          | some irs =>
              cases ha : nameIndex names aux.name with
              | none => simp
              | some iaux =>
                  cases hp : post.mapM (fun x => nameIndex names x.name) <;> simp

/-- The element at a position of a successfully mapped identifier list
    reads its slot's store value. -/
theorem mapM_store_get {store : Store} :
    ∀ {l : List Ident} {vals : List Value},
      l.mapM store = some vals → ∀ j, j < l.length → store l[j]! = some vals[j]! := by
  intro l
  induction l with
  | nil => intro vals h j hj; simp at hj
  | cons x rest ih =>
      intro vals h j hj
      simp only [List.mapM_cons] at h
      cases hx : store x with
      | none => rw [hx] at h; simp at h
      | some v =>
          rw [hx] at h
          cases hr : rest.mapM store with
          | none => rw [hr] at h; simp at h
          | some vals' =>
              rw [hr, option_pair_bind] at h
              have h' : vals = v :: vals' := (Option.some.inj h).symm
              subst h'
              cases j with
              | zero => simpa only [List.getElem!_cons_zero] using hx
              | succ j2 =>
                  simpa only [List.getElem!_cons_succ, List.getElem!_cons_succ] using
                    ih hr j2 (by simpa using hj)

/-- The element at a position of a successfully resolved identifier
    list resolves at its position. -/
theorem mapM_nameIndex_get {names : List String} :
    ∀ {l : List Ident} {is : List Nat},
      l.mapM (fun x => nameIndex names x.name) = some is →
      ∀ j, j < l.length → nameIndex names l[j]!.name = some is[j]! := by
  intro l
  induction l with
  | nil => intro is h j hj; simp at hj
  | cons x rest ih =>
      intro is h j hj
      simp only [List.mapM_cons] at h
      cases hx : nameIndex names x.name with
      | none => rw [hx] at h; simp at h
      | some i =>
          rw [hx] at h
          cases hr : rest.mapM (fun x => nameIndex names x.name) with
          | none => rw [hr] at h; simp at h
          | some is' =>
              rw [hr, option_pair_bind] at h
              have h' : is = i :: is' := (Option.some.inj h).symm
              subst h'
              cases j with
              | zero => simpa only [List.getElem!_cons_zero] using hx
              | succ j2 =>
                  simpa only [List.getElem!_cons_succ, List.getElem!_cons_succ] using
                    ih hr j2 (by simpa using hj)

/-- The read list of a resolved identifier list is the mapped store
    values (the coverage bridge's map equality). -/
theorem map_getElem!_of_linIndices {names : List String} {a : List Value}
    {store : Store} :
    ∀ {l : List Ident} {is : List Nat} {vals : List Value},
      linIndices names (l.map (fun x => BasicExpr.ident x)) = some is →
      l.mapM store = some vals →
      (∀ j, j < l.length → a[is[j]!]? = store l[j]!) →
      is.map (fun j => a[j]!) = vals := by
  intro l
  induction l with
  | nil =>
      intro is vals hl hmap hread
      simp only [List.map_nil, linIndices, Option.some.injEq] at hl
      subst hl
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hmap
      subst hmap
      rfl
  | cons x rest ih =>
      intro is vals hl hmap hread
      rw [List.map_cons, linIndices] at hl
      cases hx : nameIndex names x.name with
      | none => rw [hx] at hl; cases hl
      | some i =>
          rw [hx] at hl
          cases his : linIndices names (List.map (fun x => BasicExpr.ident x) rest) with
          | none => rw [his] at hl; cases hl
          | some is' =>
              simp only [his, Option.map_some, Option.some.injEq] at hl
              subst hl
              rw [List.mapM_cons] at hmap
              cases hstore : store x with
              | none => rw [hstore] at hmap; cases hmap
              | some v =>
                  rw [hstore] at hmap
                  cases hvals : rest.mapM store with
                  | none => rw [hvals] at hmap; cases hmap
                  | some vals' =>
                      rw [hvals, option_pair_bind] at hmap
                      have hmap' : vals = v :: vals' := (Option.some.inj hmap).symm
                      subst hmap'
                      have h0 := hread 0 (by simp)
                      have h0' : a[i]? = some v := by
                        simpa only [List.getElem!_cons_zero, hstore] using h0
                      have hib : a[i]! = v := bang_of_getElem? h0'
                      rw [List.map_cons, hib]
                      congr 1
                      exact ih his hvals (fun j hj => by
                        have h1 := hread (j + 1) (by simp; omega)
                        simpa only [List.getElem!_cons_succ] using h1)

/-- The store reads of a resolved identifier list are exactly the
    assignment's reads at the resolved positions (the SAT direction's
    read-list bridge). -/
theorem mapM_store_of_linIndices {names : List String} {store : Store}
    {a : List Value} :
    ∀ {l : List Ident} {is : List Nat},
      linIndices names (l.map (fun x => BasicExpr.ident x)) = some is →
      (∀ j, j < l.length → store l[j]! = some a[is[j]!]!) →
      l.mapM store = some (is.map (fun j => a[j]!)) := by
  intro l
  induction l with
  | nil =>
      intro is hl hread
      simp only [List.map_nil, linIndices, Option.some.injEq] at hl
      subst hl
      rfl
  | cons x rest ih =>
      intro is hl hread
      rw [List.map_cons, linIndices] at hl
      cases hx : nameIndex names x.name with
      | none => rw [hx] at hl; cases hl
      | some i =>
          rw [hx] at hl
          cases his : linIndices names
              (List.map (fun x => BasicExpr.ident x) rest) with
          | none => rw [his] at hl; cases hl
          | some is' =>
              simp only [his, Option.map_some, Option.some.injEq] at hl
              subst hl
              have h0 : store x = some a[i]! := by
                have h1 := hread 0 (by simp)
                simpa only [List.getElem!_cons_zero] using h1
              simp only [List.mapM_cons]
              rw [h0]
              rw [ih his (fun j hj => by
                have h1 := hread (j + 1) (by simp; omega)
                simpa only [List.getElem!_cons_succ] using h1)]
              rw [option_pair_bind]
              rfl

/-- An all-literal integer table is exactly `litTab` of its values. -/
theorem intLits_eq_litTab {elems : ArrayLiteral} {xs : List Int}
    (h : intLits elems = some xs) : elems = litTab xs := by
  induction elems generalizing xs with
  | nil => simp only [intLits, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
      cases e with
      | lit l =>
          cases l with
          | int k =>
              simp only [intLits] at h
              cases hr : intLits rest with
              | none => rw [hr] at h; simp at h
              | some xs' =>
                  rw [hr] at h
                  simp only [Option.map_some, Option.some.injEq] at h
                  subst h
                  rw [ih hr]
                  rfl
          | bool b => simp [intLits] at h
          | set s => simp [intLits] at h
      | ident y => simp [intLits] at h

/-- An all-identifier table is the identifier image of its names. -/
theorem allIdents_eq {es : ArrayLiteral} {l : List Ident}
    (h : allIdents es = some l) :
    es = l.map (fun x => BasicExpr.ident x) := by
  induction es generalizing l with
  | nil =>
      simp only [allIdents, Option.some.injEq] at h
      subst h
      rfl
  | cons e rest ih =>
      cases e with
      | ident x =>
          simp only [allIdents] at h
          cases hr : allIdents rest with
          | none => rw [hr] at h; simp at h
          | some is =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              rw [ih hr]
              rfl
      | lit l2 =>
          cases l2 with
          | int k => simp [allIdents] at h
          | bool b => simp [allIdents] at h
          | set s => simp [allIdents] at h

/-- The one-literal splitter reconstructs its mixed table. -/
theorem splitOneLit_eq_litSplitTab {elems : ArrayLiteral} {pre post : List Ident}
    {k : Int} (h : splitOneLit elems = some (pre, k, post)) :
    elems = litSplitTab pre k post := by
  induction elems generalizing pre k post with
  | nil => simp [splitOneLit] at h
  | cons e rest ih =>
      cases e with
      | ident x =>
          simp only [splitOneLit] at h
          cases hr : splitOneLit rest with
          | none => rw [hr] at h; simp at h
          | some t =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              injection h with h1 h2
              injection h2 with h3 h4
              rw [← h1, ← h3, ← h4, ih hr]
              rfl
      | lit l2 =>
          cases l2 with
          | int k2 =>
              simp only [splitOneLit] at h
              cases hr : allIdents rest with
              | none => rw [hr] at h; simp at h
              | some is =>
                  rw [hr] at h
                  simp only [Option.map_some, Option.some.injEq] at h
                  injection h with h1 h2
                  injection h2 with h3 h4
                  rw [← h1, ← h3, ← h4, allIdents_eq hr]
                  rfl
          | bool b => simp [splitOneLit] at h
          | set s => simp [splitOneLit] at h

/-- The element classifier's value: a `constElemValL` result encodes
    the name, the all-literal table and the literal value outright. -/
theorem elemAuxShapeOf_constElemValL_inv {c : ConstraintItem} {x : Ident}
    {xs : List Int} {k : Int}
    (h : elemAuxShapeOf c = some (AuxShape.constElemValL x xs k)) :
    c.name.name = "array_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litTab xs),
        Expr.basic (.lit (.int k))] := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    split at h
    next heqa =>
      split at h
      next heql =>
        injection h with h1
        injection h1 with h3 h4 h5
        subst h3 h4 h5
        exact ⟨heqm, by rw [heqa, intLits_eq_litTab heql]⟩
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    -- the `array_var_int_element` arms never return `constElemValL`
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next => exfalso; cases h
  next =>
    -- the `array_var_bool_element` arm never returns the int shapes
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  next => exfalso; cases h

/-- The element classifier's value: a `varElemTabLit` result encodes the
    name, the one-literal mixed table and the slot value outright. -/
theorem elemAuxShapeOf_varElemTabLit_inv {c : ConstraintItem} {x y : Ident}
    {pre post : List Ident} {k : Int}
    (h : elemAuxShapeOf c = some (AuxShape.varElemTabLit x y pre k post)) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.ident y)] := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the `array_int_element` arm never returns `varElemTabLit`
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs =>
        injection h with h1
        injection h1 with h3 h4 h5 h6 h7
        subst h3 h4 h5 h6 h7
        exact ⟨heqm, by rw [heqa, splitOneLit_eq_litSplitTab hs]⟩
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next => exfalso; cases h
  next =>
    -- the `array_var_bool_element` arm never returns the int shapes
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  next => exfalso; cases h

/-- The element classifier's value: a `varElemTabValLit` result encodes
    the name, the one-literal mixed table and the literal value
    outright. -/
theorem elemAuxShapeOf_varElemTabValLit_inv {c : ConstraintItem} {x : Ident}
    {pre post : List Ident} {k k' : Int}
    (h : elemAuxShapeOf c = some (AuxShape.varElemTabValLit x pre k post k')) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.lit (.int k'))] := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the `array_int_element` arm never returns `varElemTabValLit`
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs =>
        injection h with h1
        injection h1 with h3 h4 h5 h6 h7
        subst h3 h4 h5 h6 h7
        exact ⟨heqm, by rw [heqa, splitOneLit_eq_litSplitTab hs]⟩
      next =>
        exfalso
        split at h
        all_goals (first
          | (injection h with h1; cases h1)
          | (cases h))
    next => exfalso; cases h
  next =>
    -- the `array_var_bool_element` arm never returns the int shapes
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  next => exfalso; cases h

/-- The `varElemTabLit` shape's name and argument inversion. -/
theorem auxShapeOf_varElemTabLit_inv {c : ConstraintItem} {x y : Ident}
    {pre post : List Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.varElemTabLit x y pre k post)) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.ident y)] := by
  have h' : elemAuxShapeOf c = some (AuxShape.varElemTabLit x y pre k post) := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varElemTabLit_inv h'

/-- The `varElemTabValLit` shape's name and argument inversion. -/
theorem auxShapeOf_varElemTabValLit_inv {c : ConstraintItem} {x : Ident}
    {pre post : List Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.varElemTabValLit x pre k post k')) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.lit (.int k'))] := by
  have h' : elemAuxShapeOf c =
      some (AuxShape.varElemTabValLit x pre k post k') := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varElemTabValLit_inv h'

/-- The k-literal element tables' literal discipline (the
    classifier's range): every entry is a slot identifier or an
    integer literal. -/
def mixedOk : ArrayLiteral → Prop
  | [] => True
  | .ident _ :: rest => mixedOk rest
  | .lit (.int _) :: rest => mixedOk rest
  | _ => False

/-- The classifier's entry predicate, through `List.all`. -/
theorem mixedOk_of_all {tab : ArrayLiteral}
    (h : tab.all (fun b => match b with
      | .ident _ => true
      | .lit (.int _) => true
      | _ => false) = true) : mixedOk tab := by
  induction tab with
  | nil => trivial
  | cons b rest ih =>
      cases b with
      | ident x =>
          rw [List.all_cons] at h
          exact ih (Bool.and_eq_true_iff.mp h).2
      | lit l =>
          cases l with
          | int k =>
              rw [List.all_cons] at h
              exact ih (Bool.and_eq_true_iff.mp h).2
          | bool b2 =>
              rw [List.all_cons] at h
              exact absurd (Bool.and_eq_true_iff.mp h).1 (by simp)
          | set s2 =>
              rw [List.all_cons] at h
              exact absurd (Bool.and_eq_true_iff.mp h).1 (by simp)

/-- The classifier's boolean implies the literal discipline. -/
theorem mixedOk_of_mixTabOkB {tab : ArrayLiteral} (h : mixTabOkB tab = true) :
    mixedOk tab :=
  mixedOk_of_all (Bool.and_eq_true_iff.mp h).1

/-- The identifier image of `mixSubst` (the aux list must match the
    table's literal count, the classifier's invariant, and the table
    must obey the literal discipline). -/
theorem mixSubst_eq_map_mixIdents (tab : ArrayLiteral) (auxes : List Ident)
    (hmix : mixedOk tab) (hlen : auxes.length = (tabLitVals tab).length) :
    mixSubst tab auxes = (mixIdents tab auxes).map (fun x => BasicExpr.ident x) := by
  induction tab generalizing auxes with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | ident x =>
          cases auxes <;>
            simp only [mixSubst, mixIdents, List.map_cons] <;>
            rw [ih _ hmix (by simpa [tabLitVals] using hlen)]
      | lit l =>
          cases l with
          | int k =>
              cases auxes with
              | nil => simp [tabLitVals] at hlen
              | cons a auxes' =>
                  simp only [mixSubst, mixIdents, List.map_cons]
                  rw [ih _ hmix (by simpa [tabLitVals] using hlen)]
          | bool b2 => exact absurd hmix (by simp [mixedOk])
          | set s2 => exact absurd hmix (by simp [mixedOk])

/-- The aux-substituted table evaluated at the EXTENDED store is the
    source mixed table evaluated at the source store (PLAN C0 element
    values, k-literal generalization): each integer-literal entry
    reads its pinned aux value, every other entry reads the same
    value. -/
theorem mapM_eval_mixSubst_congr {s s' : Store} {tab : ArrayLiteral}
    {auxes : List Ident}
    (hlen : auxes.length = (tabLitVals tab).length)
    (haux : ∀ j, j < auxes.length →
      s' auxes[j]! = some (.int (tabLitVals tab)[j]!))
    (hid : ∀ x, (.ident x : BasicExpr) ∈ tab → s' x = s x) :
    (mixSubst tab auxes).mapM (BasicExpr.eval s')
      = tab.mapM (BasicExpr.eval s) := by
  induction tab generalizing auxes with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | ident x =>
          have hb : BasicExpr.eval s' (BasicExpr.ident x)
              = BasicExpr.eval s (BasicExpr.ident x) :=
            hid x List.mem_cons_self
          simp only [mixSubst, List.mapM_cons]
          rw [hb]
          rw [ih (auxes := auxes) (by simpa [tabLitVals] using hlen)
            (fun j hj => by simpa [tabLitVals] using haux j hj)
            (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
      | lit l =>
          cases l with
          | int k =>
              cases auxes with
              | nil => simp [tabLitVals] at hlen
              | cons a auxes' =>
                  have hk0 : s' a = some (.int k) := by
                    have h := haux 0 (by simp)
                    simpa [tabLitVals] using h
                  have hlen' : auxes'.length = (tabLitVals rest).length := by
                    simpa [tabLitVals] using hlen
                  simp only [mixSubst, List.mapM_cons]
                  rw [show BasicExpr.eval s' (BasicExpr.ident a) = s' a
                    from rfl, hk0]
                  rw [ih (auxes := auxes') hlen'
                    (fun j hj => by
                      have h := haux (j + 1) (by simp; omega)
                      simpa [tabLitVals, Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using h)
                    (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
                  rfl
          | bool b2 =>
              simp only [mixSubst, List.mapM_cons]
              rw [ih (auxes := auxes) (by simpa [tabLitVals] using hlen)
                (fun j hj => by simpa [tabLitVals] using haux j hj)
                (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
              rfl
          | set s2 =>
              simp only [mixSubst, List.mapM_cons]
              rw [ih (auxes := auxes) (by simpa [tabLitVals] using hlen)
                (fun j hj => by simpa [tabLitVals] using haux j hj)
                (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
              rfl

/-- The single-store form: the mixed table's evaluation with its
    literal entries read from their pinned aux slots is the source
    table's evaluation. -/
theorem mapM_eval_mixSubst {store : Store} {tab : ArrayLiteral}
    {auxes : List Ident}
    (hlen : auxes.length = (tabLitVals tab).length)
    (haux : ∀ j, j < auxes.length →
      store auxes[j]! = some (.int (tabLitVals tab)[j]!)) :
    (mixSubst tab auxes).mapM (BasicExpr.eval store)
      = tab.mapM (BasicExpr.eval store) :=
  mapM_eval_mixSubst_congr hlen haux (fun _ _ => rfl)

/-- The element classifier's value: a `varElemTabKs` result encodes the
    name, the two-element-or-more mixed table and the slot value
    outright. -/
theorem elemAuxShapeOf_varElemTabKs_inv {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral}
    (h : elemAuxShapeOf c = some (AuxShape.varElemTabKs x y tab)) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.ident y)] ∧
      mixTabOkB tab = true := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the array_int_element arm never returns varElemTabKs
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        next hmix =>
          injection h with h1
          injection h1 with h3 h4 h5
          subst h3 h4 h5
          exact ⟨heqm, heqa, hmix⟩
        next => exfalso; cases h
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        next => exfalso; injection h with h1; cases h1
        next => exfalso; cases h
    next => exfalso; cases h
  next =>
    -- the `array_var_bool_element` arm never returns the int shapes
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  next => exfalso; cases h

/-- The element classifier's value: a `varElemTabValKs` result encodes
    the name, the two-element-or-more mixed table and the literal
    value outright. -/
theorem elemAuxShapeOf_varElemTabValKs_inv {c : ConstraintItem} {x : Ident}
    {tab : ArrayLiteral} {k' : Int}
    (h : elemAuxShapeOf c = some (AuxShape.varElemTabValKs x tab k')) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.int k'))] ∧
      intValTabOkB tab = true := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the array_int_element arm never returns varElemTabValKs
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        next => exfalso; injection h with h1; cases h1
        next => exfalso; cases h
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        next hmix =>
          injection h with h1
          injection h1 with h3 h4 h5
          subst h3 h4 h5
          exact ⟨heqm, heqa, hmix⟩
        next => exfalso; cases h
    next => exfalso; cases h
  next =>
    -- the `array_var_bool_element` arm never returns the int shapes
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  next => exfalso; cases h

/-- The `varElemTabKs` shape's name and argument inversion. -/
theorem auxShapeOf_varElemTabKs_inv {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral}
    (h : auxShapeOf c = some (AuxShape.varElemTabKs x y tab)) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.ident y)] ∧
      mixTabOkB tab = true := by
  have h' : elemAuxShapeOf c = some (AuxShape.varElemTabKs x y tab) := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varElemTabKs_inv h'

/-- The `varElemTabValKs` shape's name and argument inversion. -/
theorem auxShapeOf_varElemTabValKs_inv {c : ConstraintItem} {x : Ident}
    {tab : ArrayLiteral} {k' : Int}
    (h : auxShapeOf c = some (AuxShape.varElemTabValKs x tab k')) :
    c.name.name = "array_var_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.int k'))] ∧
      intValTabOkB tab = true := by
  have h' : elemAuxShapeOf c = some (AuxShape.varElemTabValKs x tab k') := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varElemTabValKs_inv h'

/-- The `constElemValL` shape's name and argument inversion. -/
theorem auxShapeOf_constElemValL_inv {c : ConstraintItem} {x : Ident}
    {xs : List Int} {k : Int}
    (h : auxShapeOf c = some (AuxShape.constElemValL x xs k)) :
    c.name.name = "array_int_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array (litTab xs),
        Expr.basic (.lit (.int k))] := by
  have h' : elemAuxShapeOf c = some (AuxShape.constElemValL x xs k) := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_constElemValL_inv h'

/-! ## The argument-evaluation congruences (the SAT direction) -/

/-- `Holds` transfers across argument-list evaluation equality (the
    source and the rewritten piece agree on the evaluated arguments). -/
theorem holds_of_eval_args_eq {store : Store} {c c' : ConstraintItem} {nm : Ident}
    (hname : c.name = nm) (hname' : c'.name = nm)
    (hargs : c.args.mapM (Expr.eval store) = c'.args.mapM (Expr.eval store)) :
    c'.Holds fullInterp store → c.Holds fullInterp store := by
  intro h
  obtain ⟨args, hmap, hinterp⟩ := h
  refine ⟨args, by rw [hargs, hmap], ?_⟩
  rw [hname'] at hinterp
  rw [hname]
  exact hinterp

/-- The `constElemValL` argument-list evaluation congruence: the source
    literal value and the piece's pinned aux slot evaluate identically. -/
theorem mapM_eval_constElemValL {store : Store} {x aux : Ident}
    {xs : List Int} {k : Int} (haux : store aux = some (.int k)) :
    (([Expr.basic (.ident x), Expr.array (litTab xs),
        Expr.basic (.lit (.int k))] : List Expr).mapM (Expr.eval store))
      = ([Expr.basic (.ident x), Expr.array (litTab xs),
        Expr.basic (.ident aux)] : List Expr).mapM (Expr.eval store) := by
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote, haux]

/-- The `varElemTabLit` argument-list evaluation congruence. -/
theorem mapM_eval_varElemTabLit {store : Store} {x y aux : Ident}
    {pre post : List Ident} {k : Int} (haux : store aux = some (.int k)) :
    (([Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.ident y)] : List Expr).mapM (Expr.eval store))
      = ([Expr.basic (.ident x), Expr.array (auxTab pre aux post),
        Expr.basic (.ident y)] : List Expr).mapM (Expr.eval store) := by
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval]
  rw [show (litSplitTab pre k post)
      = (pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.lit (.int k)]
        ++ post.map (fun x => BasicExpr.ident x)) from rfl]
  rw [show (auxTab pre aux post)
      = (pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.ident aux]
        ++ post.map (fun x => BasicExpr.ident x)) from rfl]
  rw [mapM_eval_tab_litAux haux]

/-- The `varElemTabValLit` argument-list evaluation congruence. -/
theorem mapM_eval_varElemTabValLit {store : Store} {x aux aux2 : Ident}
    {pre post : List Ident} {k k' : Int}
    (haux : store aux = some (.int k)) (haux2 : store aux2 = some (.int k')) :
    (([Expr.basic (.ident x), Expr.array (litSplitTab pre k post),
        Expr.basic (.lit (.int k'))] : List Expr).mapM (Expr.eval store))
      = ([Expr.basic (.ident x), Expr.array (auxTab pre aux post),
        Expr.basic (.ident aux2)] : List Expr).mapM (Expr.eval store) := by
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote, haux2]
  rw [show (litSplitTab pre k post)
      = (pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.lit (.int k)]
        ++ post.map (fun x => BasicExpr.ident x)) from rfl]
  rw [show (auxTab pre aux post)
      = (pre.map (fun x => BasicExpr.ident x) ++ [BasicExpr.ident aux]
        ++ post.map (fun x => BasicExpr.ident x)) from rfl]
  rw [mapM_eval_tab_litAux haux]

/-- Argument-evaluation inversion for an identifier, an array, and an
    arbitrary third argument. -/
theorem eval_ident_arr_inv {store : Store} {x : Ident} {es : ArrayLiteral}
    {e3 : Expr} {args : List Value}
    (hmap : ([Expr.basic (.ident x), Expr.array es, e3] : List Expr).mapM
        (Expr.eval store) = some args) :
    ∃ vx vs v3, store x = some vx ∧
      es.mapM (BasicExpr.eval store) = some vs ∧
      Expr.eval store e3 = some v3 ∧ args = [vx, .array vs, v3] := by
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  rw [show Expr.eval store (Expr.basic (.ident x)) = store x from rfl] at hmap
  rw [show Expr.eval store (Expr.array es)
      = (es.mapM (BasicExpr.eval store)).map Value.array from rfl] at hmap
  cases h1 : store x with
  | none => rw [h1] at hmap; simp at hmap
  | some vx =>
      rw [h1] at hmap
      cases h2 : es.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs =>
          rw [h2] at hmap
          cases h3 : Expr.eval store e3 with
          | none => rw [h3] at hmap; simp at hmap
          | some v3 =>
              rw [h3] at hmap
              exact ⟨vx, vs, v3, rfl, rfl, rfl, by simpa using hmap.symm⟩

/-! ## The source-side inversions (the coverage direction) -/

/-- Inversion of `Holds` for the value-literal `array_int_element` over
    an all-literal table: the index slot reads an integer and the
    table's literal value at it is `k`. -/
theorem holds_arrayIntElement_litVal {store : Store} {c : ConstraintItem}
    {x : Ident} {xs : List Int} {k : Int}
    (hname : c.name.name = "array_int_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array (litTab xs),
        Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ i, store x = some (.int i) ∧
      valuesGet1 (xs.map Value.int) i = some (.int k) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨vx, vs, v3, hsx, hvs, he3, hargsv⟩ := eval_ident_arr_inv hmap
  have hvs' : vs = xs.map Value.int := by
    have h1 := hvs
    rw [mapM_eval_litTab] at h1
    exact (Option.some.inj h1).symm
  have hv3 : v3 = Value.int k := by
    have h1 : Expr.eval store (Expr.basic (.lit (.int k))) = some (.int k) := rfl
    exact Option.some.inj (he3.symm.trans h1)
  have hname' : c.name = Ident.mk "array_int_element" := ident_eq_of_name hname
  have h1 : fullInterp (Ident.mk "array_int_element")
      [vx, .array vs, v3] := by
    rw [← hargsv, ← hname']
    exact hinterp
  rw [fullInterp_of_extracted_elem "array_int_element" (Or.inl rfl)] at h1
  subst hvs'
  subst hv3
  cases vx with
  | int i =>
      have h2 : (match [Value.int i, .array (xs.map Value.int),
          Value.int k] with
        | [.int i, .array ys, .int e] => valuesGet1 ys i = some (.int e)
        | _ => False) := h1
      exact ⟨i, hsx, by simpa using h2⟩
  | bool b => exact h1.elim
  | setOfInt s => exact h1.elim
  | array ys => exact h1.elim

/-- Inversion of `Holds` for the value-literal `array_var_int_element`
    over a one-literal mixed table: the index slot reads an integer,
    the table evaluates, and the table's element at the index is the
    literal value. -/
theorem holds_arrayVarElement_litVal {store : Store} {c : ConstraintItem}
    {x : Ident} {pre post : List Ident} {k k' : Int}
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [Expr.basic (.ident x),
        Expr.array (litSplitTab pre k post),
        Expr.basic (.lit (.int k'))])
    (h : c.Holds fullInterp store) :
    ∃ (i : Int) (vs : List Value), store x = some (.int i) ∧
      (litSplitTab pre k post).mapM (BasicExpr.eval store) = some vs ∧
      valuesGet1 vs i = some (.int k') := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨vx, vs, v3, hsx, hvs, he3, hargsv⟩ :=
    eval_ident_arr_inv (store := store) hmap
  have hv3 : v3 = Value.int k' := by
    have h1 : Expr.eval store (Expr.basic (.lit (.int k'))) = some (.int k') := rfl
    exact Option.some.inj (he3.symm.trans h1)
  have hname' : c.name = Ident.mk "array_var_int_element" :=
    ident_eq_of_name hname
  have h1 : fullInterp (Ident.mk "array_var_int_element")
      [vx, .array vs, v3] := by
    rw [← hargsv, ← hname']
    exact hinterp
  rw [fullInterp_of_extracted_elem "array_var_int_element"
    (Or.inr (Or.inl rfl))] at h1
  subst hv3
  cases vx with
  | int i =>
      have h2 : (match [Value.int i, .array vs, Value.int k'] with
        | [.int i, .array ys, .int e] => valuesGet1 ys i = some (.int e)
        | _ => False) := h1
      exact ⟨i, vs, hsx, hvs, by simpa using h2⟩
  | bool b => exact h1.elim
  | setOfInt s => exact h1.elim
  | array ys => exact h1.elim

/-! ## The pieces' successful-compile inversions -/

/-- The `constElemValL` piece (the all-literal table with the pinned
    aux value) compiles to the `arrayIntElementSlot` over the table's
    literal values and the two slot positions. -/
theorem compileConstraint_constElemValL_inv {env : Store} {names : List String}
    {x aux : Ident} {xs : List Int} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "array_int_element"
        , args := [Expr.basic (.ident x), Expr.array (litTab xs),
            Expr.basic (.ident aux)]
        , anns := [] } = .ok dc) :
    ∃ i kAux, nameIndex names x.name = some i ∧
      nameIndex names aux.name = some kAux ∧
      dc = .arrayIntElementSlot xs i kAux := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hres
    cases hx : nameIndex names x.name with
    | none =>
        have hred : extractConstraint names
            { name := Ident.mk "array_int_element"
            , args := [Expr.basic (.ident x), Expr.array (litTab xs),
                Expr.basic (.ident aux)]
            , anns := [] } = none := by
          simp only [extractConstraint, intLits_litTab, hx]
        rw [hred] at hres
        exact absurd hres (by simp)
    | some i =>
        cases ha : nameIndex names aux.name with
        | none =>
            have hred : extractConstraint names
                { name := Ident.mk "array_int_element"
                , args := [Expr.basic (.ident x), Expr.array (litTab xs),
                    Expr.basic (.ident aux)]
                , anns := [] } = none := by
              simp only [extractConstraint, intLits_litTab, hx, ha]
            rw [hred] at hres
            exact absurd hres (by simp)
        | some kAux =>
            have hred : extractConstraint names
                { name := Ident.mk "array_int_element"
                , args := [Expr.basic (.ident x), Expr.array (litTab xs),
                    Expr.basic (.ident aux)]
                , anns := [] } = some (.arrayIntElementSlot xs i kAux) := by
              simp only [extractConstraint, intLits_litTab, hx, ha]
            rw [hred] at hres
            exact ⟨i, kAux, rfl, rfl,
              (Except.ok.inj hcc).symm.trans (Option.some.inj hres).symm⟩
  · rw [if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "int_plus") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "int_le") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "int_lt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "int_gt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "int_ge") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "bool_not") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "bool_and") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_int_element" : String) = "bool_or") (by decide))]
      at hcc
    exact absurd hcc (by simp)

/-- The `varElemTabLit`/`varElemTabValLit` pieces (the mixed table with
    the pinned aux at the literal's position and any value operand)
    compile to the `arrayVarIntElementSlot` over the position list. -/
theorem compileConstraint_varElem_inv {env : Store} {names : List String}
    {x v : Ident} {pre post : List Ident} {aux : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "array_var_int_element"
        , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
            Expr.basic (.ident v)]
        , anns := [] } = .ok dc) :
    ∃ is i k, linIndices names (auxTab pre aux post) = some is ∧
      nameIndex names x.name = some i ∧
      nameIndex names v.name = some k ∧
      dc = .arrayVarIntElementSlot is i k := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hres
    cases hl : linIndices names (auxTab pre aux post) with
    | none =>
        have hred : extractConstraint names
            { name := Ident.mk "array_var_int_element"
            , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                Expr.basic (.ident v)]
            , anns := [] } = none := by
          simp only [extractConstraint, hl]
        rw [hred] at hres
        exact absurd hres (by simp)
    | some is =>
        cases hx : nameIndex names x.name with
        | none =>
            have hred : extractConstraint names
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                    Expr.basic (.ident v)]
                , anns := [] } = none := by
              simp only [extractConstraint, hl, hx]
            rw [hred] at hres
            exact absurd hres (by simp)
        | some i =>
            cases hv : nameIndex names v.name with
            | none =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_int_element"
                    , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                        Expr.basic (.ident v)]
                    , anns := [] } = none := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact absurd hres (by simp)
            | some k =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_int_element"
                    , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                        Expr.basic (.ident v)]
                    , anns := [] }
                    = some (.arrayVarIntElementSlot is i k) := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact ⟨is, i, k, rfl, rfl, rfl,
                  (Except.ok.inj hcc).symm.trans (Option.some.inj hres).symm⟩
  · rw [if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_plus") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_le") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_lt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_gt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_ge") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_not") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_and") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_or") (by decide))]
      at hcc
    exact absurd hcc (by simp)

/-- Inversion of `Holds` for the value-literal `array_var_int_element`
    over an ARBITRARY mixed table (the k-literal generalization): the
    index slot reads an integer, the table evaluates, and the table's
    element at the index is the literal value. -/
theorem holds_arrayVarElement_litVal_gen {store : Store} {c : ConstraintItem}
    {x : Ident} {tab : ArrayLiteral} {k' : Int}
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.int k'))])
    (h : c.Holds fullInterp store) :
    ∃ (i : Int) (vs : List Value), store x = some (.int i) ∧
      tab.mapM (BasicExpr.eval store) = some vs ∧
      valuesGet1 vs i = some (.int k') := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨vx, vs, v3, hsx, hvs, he3, hargsv⟩ :=
    eval_ident_arr_inv (store := store) hmap
  have hv3 : v3 = Value.int k' := by
    have h1 : Expr.eval store (Expr.basic (.lit (.int k'))) = some (.int k') := rfl
    exact Option.some.inj (he3.symm.trans h1)
  have hname' : c.name = Ident.mk "array_var_int_element" :=
    ident_eq_of_name hname
  have h1 : fullInterp (Ident.mk "array_var_int_element")
      [vx, .array vs, v3] := by
    rw [← hargsv, ← hname']
    exact hinterp
  rw [fullInterp_of_extracted_elem "array_var_int_element"
    (Or.inr (Or.inl rfl))] at h1
  subst hv3
  cases vx with
  | int i =>
      have h2 : (match [Value.int i, .array vs, Value.int k'] with
        | [.int i, .array ys, .int e] => valuesGet1 ys i = some (.int e)
        | _ => False) := h1
      exact ⟨i, vs, hsx, hvs, by simpa using h2⟩
  | bool b => exact h1.elim
  | setOfInt s => exact h1.elim
  | array ys => exact h1.elim

/-- The generalized `array_var_int_element` piece (an arbitrary table
    with a slot value) compiles to the `arrayVarIntElementSlot` over
    the table's position list. -/
theorem compileConstraint_varElemTab_inv {env : Store} {names : List String}
    {x v : Ident} {tab : ArrayLiteral} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "array_var_int_element"
        , args := [Expr.basic (.ident x), Expr.array tab,
            Expr.basic (.ident v)]
        , anns := [] } = .ok dc) :
    ∃ is i k, linIndices names tab = some is ∧
      nameIndex names x.name = some i ∧
      nameIndex names v.name = some k ∧
      dc = .arrayVarIntElementSlot is i k := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hres
    cases hl : linIndices names tab with
    | none =>
        have hred : extractConstraint names
            { name := Ident.mk "array_var_int_element"
            , args := [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident v)]
            , anns := [] } = none := by
          simp only [extractConstraint, hl]
        rw [hred] at hres
        exact absurd hres (by simp)
    | some is =>
        cases hx : nameIndex names x.name with
        | none =>
            have hred : extractConstraint names
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x), Expr.array tab,
                    Expr.basic (.ident v)]
                , anns := [] } = none := by
              simp only [extractConstraint, hl, hx]
            rw [hred] at hres
            exact absurd hres (by simp)
        | some i =>
            cases hv : nameIndex names v.name with
            | none =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_int_element"
                    , args := [Expr.basic (.ident x), Expr.array tab,
                        Expr.basic (.ident v)]
                    , anns := [] } = none := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact absurd hres (by simp)
            | some k =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_int_element"
                    , args := [Expr.basic (.ident x), Expr.array tab,
                        Expr.basic (.ident v)]
                    , anns := [] }
                    = some (.arrayVarIntElementSlot is i k) := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact ⟨is, i, k, rfl, rfl, rfl,
                  (Except.ok.inj hcc).symm.trans (Option.some.inj hres).symm⟩
  · rw [if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_plus") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_le") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_lt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_gt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "int_ge") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_not") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_and") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_int_element" : String) = "bool_or") (by decide))]
      at hcc
    exact absurd hcc (by simp)

/-- The bool-literal element tables' literal discipline: every entry
    is a slot identifier or a Boolean literal. -/
def mixedOkB : ArrayLiteral → Prop
  | [] => True
  | .ident _ :: rest => mixedOkB rest
  | .lit (.bool _) :: rest => mixedOkB rest
  | _ => False

/-- The bool classifier's entry predicate, through `List.all`. -/
theorem mixedOkB_of_all {tab : ArrayLiteral}
    (h : tab.all (fun b => match b with
      | .ident _ => true
      | .lit (.bool _) => true
      | _ => false) = true) : mixedOkB tab := by
  induction tab with
  | nil => trivial
  | cons b rest ih =>
      cases b with
      | ident x =>
          rw [List.all_cons] at h
          exact ih (Bool.and_eq_true_iff.mp h).2
      | lit l =>
          cases l with
          | bool b2 =>
              rw [List.all_cons] at h
              exact ih (Bool.and_eq_true_iff.mp h).2
          | int k =>
              rw [List.all_cons] at h
              exact absurd (Bool.and_eq_true_iff.mp h).1 (by simp)
          | set s2 =>
              rw [List.all_cons] at h
              exact absurd (Bool.and_eq_true_iff.mp h).1 (by simp)

/-- An all-slot table obeys the integer discipline. -/
theorem mixedOk_of_allIdents {tab : ArrayLiteral} {l : List Ident}
    (h : allIdents tab = some l) : mixedOk tab := by
  induction tab generalizing l with
  | nil => trivial
  | cons b rest ih =>
      cases b with
      | ident x =>
          cases hr : allIdents rest with
          | none => simp [allIdents, hr] at h
          | some l' => exact ih hr
      | lit l2 =>
          cases l2 <;> simp [allIdents] at h

/-- The bool-literal slot-value classifier implies the discipline. -/
theorem mixedOkB_of_boolLitTabOkB {tab : ArrayLiteral}
    (h : boolLitTabOkB tab = true) : mixedOkB tab :=
  mixedOkB_of_all (Bool.and_eq_true_iff.mp h).1

/-- The bool literal-value classifier implies the discipline. -/
theorem mixedOkB_of_boolTabOkB {tab : ArrayLiteral}
    (h : boolTabOkB tab = true) : mixedOkB tab :=
  mixedOkB_of_all h

/-- The identifier image of `mixSubstB` (the aux list must match the
    table's literal count, the classifier's invariant). -/
theorem mixSubstB_eq_map_mixIdentsB (tab : ArrayLiteral) (auxes : List Ident)
    (hmix : mixedOkB tab) (hlen : auxes.length = (tabBoolVals tab).length) :
    mixSubstB tab auxes = (mixIdentsB tab auxes).map (fun x => BasicExpr.ident x) := by
  induction tab generalizing auxes with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | ident x =>
          cases auxes <;>
            simp only [mixSubstB, mixIdentsB, List.map_cons] <;>
            rw [ih _ hmix (by simpa [tabBoolVals] using hlen)]
      | lit l =>
          cases l with
          | bool b2 =>
              cases auxes with
              | nil =>
                  exact absurd hlen (by simp [tabBoolVals])
              | cons a auxes' =>
                  simp only [mixSubstB, mixIdentsB, List.map_cons]
                  rw [ih _ hmix (by simpa [tabBoolVals] using hlen)]
          | int k => exact absurd hmix (by simp [mixedOkB])
          | set s2 => exact absurd hmix (by simp [mixedOkB])

/-- The aux-substituted bool table evaluated at the EXTENDED store is
    the source bool table evaluated at the source store (each
    Boolean-literal entry reads its pinned aux value, every other entry
    reads the same value). -/
theorem mapM_eval_mixSubstB_congr {s s' : Store} {tab : ArrayLiteral}
    {auxes : List Ident}
    (hlen : auxes.length = (tabBoolVals tab).length)
    (haux : ∀ j, j < auxes.length →
      s' auxes[j]! = some (.bool (tabBoolVals tab)[j]!))
    (hid : ∀ x, (.ident x : BasicExpr) ∈ tab → s' x = s x) :
    (mixSubstB tab auxes).mapM (BasicExpr.eval s')
      = tab.mapM (BasicExpr.eval s) := by
  induction tab generalizing auxes with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | ident x =>
          have hb : BasicExpr.eval s' (BasicExpr.ident x)
              = BasicExpr.eval s (BasicExpr.ident x) :=
            hid x List.mem_cons_self
          simp only [mixSubstB, List.mapM_cons]
          rw [hb]
          rw [ih (auxes := auxes) (by simpa [tabBoolVals] using hlen)
            (fun j hj => by simpa [tabBoolVals] using haux j hj)
            (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
      | lit l =>
          cases l with
          | bool b2 =>
              cases auxes with
              | nil =>
                  exact absurd hlen (by simp [tabBoolVals])
              | cons a auxes' =>
                  have hb0 : s' a = some (.bool b2) := by
                    have h := haux 0 (by simp)
                    simpa [tabBoolVals] using h
                  have hlen' : auxes'.length = (tabBoolVals rest).length := by
                    simpa [tabBoolVals] using hlen
                  simp only [mixSubstB, List.mapM_cons]
                  rw [show BasicExpr.eval s' (BasicExpr.ident a) = s' a
                    from rfl, hb0]
                  rw [ih (auxes := auxes') hlen'
                    (fun j hj => by
                      have h := haux (j + 1) (by simp; omega)
                      simpa [tabBoolVals, Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using h)
                    (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
                  rfl
          | int k =>
              simp only [mixSubstB, List.mapM_cons]
              rw [ih (auxes := auxes) (by simpa [tabBoolVals] using hlen)
                (fun j hj => by simpa [tabBoolVals] using haux j hj)
                (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
              rfl
          | set s2 =>
              simp only [mixSubstB, List.mapM_cons]
              rw [ih (auxes := auxes) (by simpa [tabBoolVals] using hlen)
                (fun j hj => by simpa [tabBoolVals] using haux j hj)
                (fun y hy => hid y (List.mem_cons_of_mem _ hy))]
              rfl

/-- The single-store form: the mixed bool table's evaluation with its
    literal entries read from their pinned aux slots is the source
    table's evaluation. -/
theorem mapM_eval_mixSubstB {store : Store} {tab : ArrayLiteral}
    {auxes : List Ident}
    (hlen : auxes.length = (tabBoolVals tab).length)
    (haux : ∀ j, j < auxes.length →
      store auxes[j]! = some (.bool (tabBoolVals tab)[j]!)) :
    (mixSubstB tab auxes).mapM (BasicExpr.eval store)
      = tab.mapM (BasicExpr.eval store) :=
  mapM_eval_mixSubstB_congr hlen haux (fun _ _ => rfl)

/-- The element classifier's value: a `varBoolTabLits` result encodes
    the name, the mixed bool table and the slot value outright. -/
theorem elemAuxShapeOf_varBoolTabLits_inv {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral}
    (h : elemAuxShapeOf c = some (AuxShape.varBoolTabLits x y tab)) :
    c.name.name = "array_var_bool_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.ident y)] ∧
      boolLitTabOkB tab = true := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the array_int_element arm never returns varBoolTabLits
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    -- the array_var_int_element arms never return varBoolTabLits
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        all_goals (first
          | (exfalso; injection h with h1; cases h1)
          | (exfalso; cases h))
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        all_goals (first
          | (exfalso; injection h with h1; cases h1)
          | (exfalso; cases h))
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next hok =>
        injection h with h1
        injection h1 with h3 h4 h5
        subst h3 h4 h5
        exact ⟨heqm, heqa, hok⟩
      next => exfalso; cases h
    next x2 elems b2 heqa =>
      split at h
      next hok => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next => exfalso; cases h

/-- The element classifier's value: a `varBoolTabValLit` result encodes
    the name, the mixed bool table and the literal value outright. -/
theorem elemAuxShapeOf_varBoolTabValLit_inv {c : ConstraintItem} {x : Ident}
    {tab : ArrayLiteral} {b' : Bool}
    (h : elemAuxShapeOf c = some (AuxShape.varBoolTabValLit x tab b')) :
    c.name.name = "array_var_bool_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.bool b'))] ∧
      boolTabOkB tab = true := by
  unfold elemAuxShapeOf at h
  split at h
  next heqm =>
    -- the array_int_element arm never returns varBoolTabValLit
    split at h
    next heqa =>
      split at h
      next heql => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next => exfalso; cases h
  next heqm =>
    -- the array_var_int_element arms never return varBoolTabValLit
    split at h
    next x2 elems y2 heqa =>
      split at h
      next pre2 k2 post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        all_goals (first
          | (exfalso; injection h with h1; cases h1)
          | (exfalso; cases h))
    next x2 elems k2 heqa =>
      split at h
      next pre2 k2' post2 hs => exfalso; injection h with h1; cases h1
      next =>
        split at h
        all_goals (first
          | (exfalso; injection h with h1; cases h1)
          | (exfalso; cases h))
    next => exfalso; cases h
  next heqm =>
    split at h
    next x2 elems y2 heqa =>
      split at h
      next hok => exfalso; injection h with h1; cases h1
      next => exfalso; cases h
    next x2 elems b2 heqa =>
      split at h
      next hok =>
        injection h with h1
        injection h1 with h3 h4 h5
        subst h3 h4 h5
        exact ⟨heqm, heqa, hok⟩
      next => exfalso; cases h
    next => exfalso; cases h
  next => exfalso; cases h

/-- The `varBoolTabLits` shape's name and argument inversion. -/
theorem auxShapeOf_varBoolTabLits_inv {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral}
    (h : auxShapeOf c = some (AuxShape.varBoolTabLits x y tab)) :
    c.name.name = "array_var_bool_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.ident y)] ∧
      boolLitTabOkB tab = true := by
  have h' : elemAuxShapeOf c = some (AuxShape.varBoolTabLits x y tab) := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varBoolTabLits_inv h'

/-- The `varBoolTabValLit` shape's name and argument inversion. -/
theorem auxShapeOf_varBoolTabValLit_inv {c : ConstraintItem} {x : Ident}
    {tab : ArrayLiteral} {b' : Bool}
    (h : auxShapeOf c = some (AuxShape.varBoolTabValLit x tab b')) :
    c.name.name = "array_var_bool_element" ∧
      c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.bool b'))] ∧
      boolTabOkB tab = true := by
  have h' : elemAuxShapeOf c = some (AuxShape.varBoolTabValLit x tab b') := by
    rw [auxShapeOf] at h
    split at h
    all_goals (try split at h)
    all_goals
      first
        | (exact h)
        | (exact absurd h (by simp))
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  exact elemAuxShapeOf_varBoolTabValLit_inv h'

/-- Inversion of `Holds` for the value-literal `array_var_bool_element`
    over an arbitrary mixed table: the index slot reads an integer, the
    table evaluates, and the table's element at the index is the
    Boolean literal value. -/
theorem holds_arrayVarBoolElement_litVal_gen {store : Store}
    {c : ConstraintItem} {x : Ident} {tab : ArrayLiteral} {b' : Bool}
    (hname : c.name.name = "array_var_bool_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array tab,
        Expr.basic (.lit (.bool b'))])
    (h : c.Holds fullInterp store) :
    ∃ (i : Int) (vs : List Value), store x = some (.int i) ∧
      tab.mapM (BasicExpr.eval store) = some vs ∧
      valuesGet1 vs i = some (.bool b') := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨vx, vs, v3, hsx, hvs, he3, hargsv⟩ :=
    eval_ident_arr_inv (store := store) hmap
  have hv3 : v3 = Value.bool b' := by
    have h1 : Expr.eval store (Expr.basic (.lit (.bool b'))) = some (.bool b') := rfl
    exact Option.some.inj (he3.symm.trans h1)
  have hname' : c.name = Ident.mk "array_var_bool_element" :=
    ident_eq_of_name hname
  have h1 : fullInterp (Ident.mk "array_var_bool_element")
      [vx, .array vs, v3] := by
    rw [← hargsv, ← hname']
    exact hinterp
  rw [fullInterp_of_extracted_elem "array_var_bool_element"
    (Or.inr (Or.inr rfl))] at h1
  subst hv3
  cases vx with
  | int i =>
      have h2 : (match [Value.int i, .array vs, Value.bool b'] with
        | [.int i, .array ys, .bool e] => valuesGet1 ys i = some (.bool e)
        | _ => False) := h1
      exact ⟨i, vs, hsx, hvs, by simpa using h2⟩
  | bool b2 => exact h1.elim
  | setOfInt s => exact h1.elim
  | array ys => exact h1.elim

/-- The generalized `array_var_bool_element` piece (an arbitrary table
    with a slot value) compiles to the `arrayVarBoolElementSlot` over
    the table's position list. -/
theorem compileConstraint_varBoolTab_inv {env : Store} {names : List String}
    {x v : Ident} {tab : ArrayLiteral} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "array_var_bool_element"
        , args := [Expr.basic (.ident x), Expr.array tab,
            Expr.basic (.ident v)]
        , anns := [] } = .ok dc) :
    ∃ is i k, linIndices names tab = some is ∧
      nameIndex names x.name = some i ∧
      nameIndex names v.name = some k ∧
      dc = .arrayVarBoolElementSlot is i k := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hres
    cases hl : linIndices names tab with
    | none =>
        have hred : extractConstraint names
            { name := Ident.mk "array_var_bool_element"
            , args := [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident v)]
            , anns := [] } = none := by
          simp only [extractConstraint, hl]
        rw [hred] at hres
        exact absurd hres (by simp)
    | some is =>
        cases hx : nameIndex names x.name with
        | none =>
            have hred : extractConstraint names
                { name := Ident.mk "array_var_bool_element"
                , args := [Expr.basic (.ident x), Expr.array tab,
                    Expr.basic (.ident v)]
                , anns := [] } = none := by
              simp only [extractConstraint, hl, hx]
            rw [hred] at hres
            exact absurd hres (by simp)
        | some i =>
            cases hv : nameIndex names v.name with
            | none =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_bool_element"
                    , args := [Expr.basic (.ident x), Expr.array tab,
                        Expr.basic (.ident v)]
                    , anns := [] } = none := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact absurd hres (by simp)
            | some k =>
                have hred : extractConstraint names
                    { name := Ident.mk "array_var_bool_element"
                    , args := [Expr.basic (.ident x), Expr.array tab,
                        Expr.basic (.ident v)]
                    , anns := [] }
                    = some (.arrayVarBoolElementSlot is i k) := by
                  simp only [extractConstraint, hl, hx, hv]
                rw [hred] at hres
                exact ⟨is, i, k, rfl, rfl, rfl,
                  (Except.ok.inj hcc).symm.trans (Option.some.inj hres).symm⟩
  · rw [if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "int_plus") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "int_le") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "int_lt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "int_gt") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "int_ge") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "bool_not") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "bool_and") (by decide)),
      if_neg (fun hc =>
          absurd (hc.1 : ("array_var_bool_element" : String) = "bool_or") (by decide))]
      at hcc
    exact absurd hcc (by simp)

end LeanFzn.Compiler

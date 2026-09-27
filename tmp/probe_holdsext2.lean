import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The identifiers appearing in a basic expression. -/
def BasicExpr.idents : BasicExpr → List Ident
  | .ident x => [x]
  | _ => []

/-- The identifiers appearing in an expression. -/
def Expr.idents : Expr → List Ident
  | .basic b => BasicExpr.idents b
  | .array es => es.flatMap BasicExpr.idents

/-- flatMap membership, cons form. -/
theorem flatMap_cons_mem {b : BasicExpr} {rest : List BasicExpr}
    {x : Ident} (hx : x ∈ BasicExpr.idents b) :
    x ∈ (b :: rest).flatMap BasicExpr.idents := by
  rw [List.flatMap_cons]
  exact List.mem_append_left _ hx

theorem flatMap_cons_mem' {b : BasicExpr} {rest : List BasicExpr}
    {x : Ident} (hx : x ∈ rest.flatMap BasicExpr.idents) :
    x ∈ (b :: rest).flatMap BasicExpr.idents := by
  rw [List.flatMap_cons]
  exact List.mem_append_right _ hx

/-- `Holds` transfers between stores agreeing on the identifiers
    appearing in the constraint's arguments. -/
theorem Holds_ext_args {store1 store2 : Store} {c : ConstraintItem}
    (h : ∀ x, x ∈ (c.args.flatMap Expr.idents) → store1 x = store2 x)
    (hh : c.Holds fullInterp store1) :
    c.Holds fullInterp store2 := by
  obtain ⟨args, hmap, hinterp⟩ := hh
  refine ⟨args, ?_, hinterp⟩
  -- per-element agreement, by induction over basic-expression lists
  have hbelist : ∀ (es : List BasicExpr),
      (∀ x, x ∈ es.flatMap BasicExpr.idents → store1 x = store2 x) →
      es.mapM (BasicExpr.eval store1) = es.mapM (BasicExpr.eval store2) := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons b rest ih =>
        intro hall
        have hb : BasicExpr.eval store1 b = BasicExpr.eval store2 b := by
          cases b with
          | lit l => rfl
          | ident x =>
              show store1 x = store2 x
              exact hall x (flatMap_cons_mem (b := .ident x) (rest := rest)
                List.mem_cons_self)
        rw [List.mapM_cons, List.mapM_cons, hb,
          ih (fun x hx => hall x (flatMap_cons_mem' (b := b) (rest := rest) hx))]
  -- per-expression agreement
  have haeval : ∀ (e : Expr), (∀ x, x ∈ Expr.idents e →
      store1 x = store2 x) →
      Expr.eval store1 e = Expr.eval store2 e := by
    intro e hid
    cases e with
    | basic b =>
        cases b with
        | lit l => rfl
        | ident x =>
            show store1 x = store2 x
            exact hid x (by
              show x ∈ BasicExpr.idents (.ident x)
              exact List.mem_cons_self)
    | array es =>
        show (es.mapM (BasicExpr.eval store1)).map Value.array =
          (es.mapM (BasicExpr.eval store2)).map Value.array
        rw [hbelist es (fun x hx => hid x hx)]
  -- the args' mapM agreement, by induction over the args (the
  -- hypothesis is generalized: the tail's identifiers are a subset)
  have hmain : ∀ (l : List Expr) (hl : ∀ x,
      x ∈ l.flatMap Expr.idents → store1 x = store2 x),
      l.mapM (Expr.eval store1) = l.mapM (Expr.eval store2) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e rest ih =>
        intro hl
        rw [List.mapM_cons, List.mapM_cons]
        rw [haeval e (fun x hx => hl x (by
          rw [List.flatMap_cons]
          exact List.mem_append_left _ hx))]
        rw [ih (fun x hx => hl x (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ hx))]
  rw [hmain c.args h] at hmap
  exact hmap

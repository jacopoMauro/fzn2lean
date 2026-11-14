/-
Purpose: Correctness and equivalence theorems for the check checker.
Dependencies: Checker.Runtime.Check and correctness of earlier checker layers.
DAG: Runtime.Check -> Proofs.Check -> public Checker.Check import.
-/
import LeanFzn.Checker.Runtime.Check
import LeanFzn.Checker.Proofs.Globals

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Checker.Solution
open Internal
open LeanFzn.Checker.Globals

/-- Inserting a different key leaves membership unchanged. -/
private theorem insert_contains_ne (s : Std.HashSet String) (x y : String) (h : x ≠ y) :
    (s.insert x).contains y = s.contains y := by
  by_cases hc : (s.insert x).contains y = true
  · by_cases hd : s.contains y = true
    · rw [hc, hd]
    · exfalso
      have hmem : y ∈ s.insert x := by simpa using hc
      rcases Std.HashSet.mem_insert.mp hmem with h1 | h2
      · exact h (by simpa using h1)
      · exact absurd (by simpa using h2) hd
  · by_cases hd : s.contains y = true
    · exfalso
      have hmem : y ∈ s := by simpa using hd
      have hmem2 : y ∈ s.insert x := Std.HashSet.mem_insert.mpr (Or.inr hmem)
      exact absurd (by simpa using hmem2) hc
    · cases hs1 : (s.insert x).contains y <;>
        cases hs2 : s.contains y <;> simp_all

/-- The seen-set loop decides the declarative condition: no name of
    the list is in `seen`, and the list has no duplicates. -/
private theorem nodupNamesFast_iff (l : List String) :
    ∀ (seen : Std.HashSet String),
      nodupNamesFast l seen = true ↔
        (∀ x ∈ l, seen.contains x = false) ∧ l.Nodup := by
  induction l with
  | nil => intro seen; simp [nodupNamesFast, List.nodup_nil]
  | cons x xs ih =>
      intro seen
      simp only [nodupNamesFast, Bool.and_eq_true, Bool.not_eq_true']
      rw [ih (seen.insert x)]
      constructor
      · rintro ⟨hx, hall⟩
        refine ⟨?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hx
          · have hcy := hall.1 y (by simp [hy'])
            by_cases hxy : x = y
            · subst hxy
              have hself : (seen.insert x).contains x = true := by simp
              rw [hself] at hcy
              exact absurd hcy (by simp)
            · rw [insert_contains_ne _ x y hxy] at hcy
              exact hcy
        · rw [List.nodup_cons]
          refine ⟨?_, hall.2⟩
          intro hmem
          have hself : (seen.insert x).contains x = true := by simp
          have hxin := hall.1 x hmem
          rw [hself] at hxin
          exact Bool.noConfusion hxin
      · intro ⟨hall, hnd⟩
        have hnx : x ∉ xs := (List.nodup_cons.mp hnd).1
        have hnx' : ∀ y ∈ xs, x ≠ y := by
          intro y hy hxy
          exact hnx (hxy ▸ hy)
        refine ⟨hall x (by simp), ⟨?_, ?_⟩⟩
        · intro y hy
          rw [insert_contains_ne _ x y (hnx' y hy)]
          exact hall y (List.mem_cons_of_mem _ hy)
        · exact (List.nodup_cons.mp hnd).2

/-- The empty set contains nothing. -/
private theorem HashSet.empty_contains_false (x : String) :
    ((∅ : Std.HashSet String)).contains x = false := by simp

/-- Duplicate-freedom is preserved and reflected by the injective
    `Ident.name` map. -/
private theorem ident_nodup_map_iff (l : List Ident) :
    (l.map (·.name)).Nodup ↔ l.Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.nodup_cons, ih]
      constructor
      · rintro ⟨hn, hnd⟩
        exact ⟨fun hmem => hn (List.mem_map_of_mem hmem), hnd⟩
      · rintro ⟨hn, hnd⟩
        refine ⟨fun hmem => ?_, hnd⟩
        obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hmem
        have hab : a = b := by
          cases a
          cases b
          simp only [Ident.mk.injEq]
          exact hbeq.symm
        subst hab
        exact hn hb

/-- `nodupIdentsFast` decides `List.Nodup`. -/
theorem nodupIdentsFast_iff (l : List Ident) :
    nodupIdentsFast l = true ↔ l.Nodup := by
  have h := nodupNamesFast_iff (l.map (·.name)) ∅
  rw [nodupIdentsFast, h]
  constructor
  · exact fun hall => (ident_nodup_map_iff l).mp hall.2
  · intro hnd
    exact ⟨fun x _ => HashSet.empty_contains_false x, (ident_nodup_map_iff l).mpr hnd⟩

/-- A first-match hit is a member of the list. -/
private theorem lookupPair_mem {β : Type} {x : String} :
    ∀ (l : List (String × β)) (w : β),
      lookupPair x l = some w → (x, w) ∈ l := by
  intro l
  induction l with
  | nil => intro w h; simp [lookupPair] at h
  | cons kv rest ih =>
      intro w h
      simp only [lookupPair] at h
      by_cases hk : kv.1 = x
      · rw [if_pos hk] at h
        have hw : kv.2 = w := Option.some.inj h
        subst hw
        rw [← hk]
        exact List.mem_cons_self
      · rw [if_neg hk] at h
        exact List.mem_cons_of_mem _ (ih w h)

/-- Under name-uniqueness, the head's name does not hit again in the
    tail. -/
private theorem lookupPair_none_of_nodup {β : Type} {x : String} {kv : String × β}
    {rest : List (String × β)}
    (hl : ((kv :: rest).map Prod.fst).Nodup) (hx : kv.1 = x) : lookupPair x rest = none := by
  match hcl : lookupPair x rest with
  | none => rfl
  | some w =>
      have hmem : (x, w) ∈ rest := lookupPair_mem rest w hcl
      have hmem' : x ∈ rest.map Prod.fst := List.mem_map_of_mem hmem
      rw [← hx] at hmem'
      exact absurd hmem' (List.nodup_cons.mp hl).1

/-- Folding `insert` over a (name, value) list agrees with first-match
    lookup when the names are unique. -/
private theorem insertFold_get?_eq {β : Type}
    (l : List (String × β)) (hl : (l.map Prod.fst).Nodup)
    (acc : Std.HashMap String β) (x : String) :
    (l.foldl (fun m kv => m.insert kv.1 kv.2) acc).get? x =
      (lookupPair x l).elim (acc.get? x) some := by
  induction l generalizing acc with
  | nil => simp [lookupPair]
  | cons kv rest ih =>
      have hnodup_rest : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hl).2
      have ih' := ih hnodup_rest
      simp only [List.foldl_cons, lookupPair]
      by_cases hx : kv.1 = x
      · rw [ih']
        have hins : (acc.insert kv.1 kv.2).get? x = some kv.2 := by
          have h1 := Std.HashMap.getElem?_insert (m := acc) (k := kv.1) (v := kv.2) (a := x)
          rw [show (acc.insert kv.1 kv.2).get? x = (acc.insert kv.1 kv.2)[x]? from rfl]
          rw [h1]
          simp [hx]
        rw [hins, if_pos hx, lookupPair_none_of_nodup hl hx]
        rfl
      · rw [ih']
        have hne : (acc.insert kv.1 kv.2).get? x = acc.get? x := by
          have h1 := Std.HashMap.getElem?_insert (m := acc) (k := kv.1) (v := kv.2) (a := x)
          rw [show (acc.insert kv.1 kv.2).get? x = (acc.insert kv.1 kv.2)[x]? from rfl]
          rw [h1]
          simp [hx]
        rw [hne, if_neg hx]

/-- `lookupIdent` on identifier-keyed pairs is `lookupPair` on the
    name-keyed projection. -/
private theorem lookupIdent_eq_lookupPair {β : Type} (x : Ident) (l : List (Ident × β)) :
    lookupIdent x l = lookupPair x.name (l.map (fun p => (p.1.name, p.2))) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.map_cons, lookupIdent, lookupPair]
      by_cases h : p.1.name = x.name
      · rw [if_pos h]
        rw [if_pos (by rw [h])]
      · rw [if_neg (fun hc => h (by rw [← hc])), if_neg h, ih]

/-- `Model.staticEnv` agrees with the fast environment when the
    parameter and variable names are unique.  Both layers are folded
    `insert`s over the name-keyed pair lists; each agrees with
    first-match lookup (`insertFold_get?_eq`), and the parameters-
    second insertion order realizes `staticEnv`'s parameters-first
    preference. -/
theorem staticEnvFast_eq (m : Model)
    (hpar : (m.parameters.map (·.name.name)).Nodup)
    (hvar : (m.variables.map (·.name.name)).Nodup)
    (x : Ident) :
    (staticEnvFast m).get? x.name = m.staticEnv x := by
  -- the variable fold is the pair-list fold over the mapped list
  have hvarfold : insertVarDecls m.variables {} =
      (m.variables.map (fun d => (d.name.name, (d.type, true)))).foldl
        (fun mm (kv : String × (FznType × Bool)) => mm.insert kv.1 kv.2) {} := by
    have gen : ∀ (acc : Std.HashMap String (FznType × Bool)) (l : List VarDeclItem),
        insertVarDecls l acc =
          List.foldl (fun mm kv => mm.insert kv.1 kv.2) acc
            (List.map (fun d => (d.name.name, (d.type, true))) l) := by
      intro acc l
      induction l generalizing acc with
      | nil => rfl
      | cons d rest ih =>
          simp only [insertVarDecls, List.map_cons, List.foldl_cons]
          exact ih _
    exact gen _ _
  have hparfold : ∀ (acc : Std.HashMap String (FznType × Bool)),
      insertParDecls m.parameters acc =
      (m.parameters.map (fun d => (d.name.name, (d.type, false)))).foldl
        (fun mm (kv : String × (FznType × Bool)) => mm.insert kv.1 kv.2) acc := by
    intro acc
    have gen : ∀ (l : List ParDeclItem) (acc : Std.HashMap String (FznType × Bool)),
        insertParDecls l acc =
          List.foldl (fun mm kv => mm.insert kv.1 kv.2) acc
            (List.map (fun d => (d.name.name, (d.type, false))) l) := by
      intro l acc
      induction l generalizing acc with
      | nil => rfl
      | cons d rest ih =>
          simp only [insertParDecls, List.map_cons, List.foldl_cons]
          exact ih _
    exact gen _ _
  have hinner : ∀ x', (insertVarDecls m.variables {}).get? x' =
      (lookupPair x' (m.variables.map (fun d => (d.name.name, (d.type, true))))).elim
        ((∅ : Std.HashMap String (FznType × Bool)).get? x') some := by
    intro x'
    rw [hvarfold]
    have hmap : ((m.variables.map (fun d => (d.name.name, (d.type, true)))).map Prod.fst) =
        m.variables.map (·.name.name) := by
      simp [List.map_map]
    exact insertFold_get?_eq _ (hmap ▸ hvar) _ x'
  have houter : ∀ x', (insertParDecls m.parameters (insertVarDecls m.variables {})).get? x' =
      (lookupPair x' (m.parameters.map (fun d => (d.name.name, (d.type, false))))).elim
        ((insertVarDecls m.variables {}).get? x') some := by
    intro x'
    rw [hparfold]
    have hmap : ((m.parameters.map (fun d => (d.name.name, (d.type, false)))).map Prod.fst) =
        m.parameters.map (·.name.name) := by
      simp [List.map_map]
    exact insertFold_get?_eq _ (hmap ▸ hpar) _ x'
  unfold staticEnvFast
  rw [houter x.name, hinner x.name]
  have hempty : ((∅ : Std.HashMap String (FznType × Bool)).get? x.name) = none := by simp
  rw [hempty]
  have hstatic : m.staticEnv x =
      (lookupPair x.name (m.parameters.map (fun d => (d.name.name, (d.type, false))))).elim
        (lookupPair x.name (m.variables.map (fun d => (d.name.name, (d.type, true))))) some := by
    unfold Model.staticEnv
    rw [lookupIdent_eq_lookupPair, lookupIdent_eq_lookupPair]
    have hcomppar : (m.parameters.map (fun d => (d.name, (d.type, false)))).map
        (fun p => (p.1.name, p.2)) =
        m.parameters.map (fun d => (d.name.name, (d.type, false))) := by
      simp [List.map_map]
    have hcompvar : (m.variables.map (fun d => (d.name, (d.type, true)))).map
        (fun p => (p.1.name, p.2)) =
        m.variables.map (fun d => (d.name.name, (d.type, true))) := by
      simp [List.map_map]
    rw [hcomppar, hcompvar]
    cases lookupPair x.name
        (m.parameters.map (fun d => (d.name.name, (d.type, false)))) with
    | none => rfl
    | some info => rfl
  rw [hstatic]
  have helim : ∀ (o : Option (FznType × Bool)), o.elim none some = o := by
    intro o
    cases o with
    | none => rfl
    | some w => rfl
  cases lookupPair x.name
      (m.parameters.map (fun d => (d.name.name, (d.type, false)))) with
  | none => rw [helim]
  | some info => rfl

/-- The seen-set loop decides: every entry is declared and fresh
    w.r.t. the seen-set, and the assigned names are pairwise
    distinct. -/
private theorem entriesOkAux_iff (declared : Std.HashSet String) :
    ∀ (es : List Entry) (seen : Std.HashSet String),
      entriesOkAux declared seen es = true ↔
        (∀ e ∈ es, declared.contains e.name = true ∧ seen.contains e.name = false) ∧
          (es.map Entry.name).Nodup := by
  intro es
  induction es with
  | nil => intro seen; simp [entriesOkAux, List.nodup_nil]
  | cons e rest ih =>
      intro seen
      simp only [entriesOkAux, Bool.and_eq_true, Bool.not_eq_true', List.map_cons,
        List.nodup_cons]
      rw [ih (seen.insert e.name)]
      constructor
      · rintro ⟨⟨hdecl, hfresh⟩, hall⟩
        refine ⟨?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨hdecl, hfresh⟩
          · obtain ⟨hd2, hs2⟩ := hall.1 y (by simp [hy'])
            refine ⟨hd2, ?_⟩
            by_cases heq : e.name = y.name
            · exfalso
              have hins : (seen.insert e.name).contains y.name = true := by
                rw [← heq]
                simp
              rw [hins] at hs2
              exact Bool.noConfusion hs2
            · rw [insert_contains_ne _ e.name y.name (fun hc => heq (by simpa using hc))] at hs2
              exact hs2
        · refine ⟨?_, hall.2⟩
          intro hmem
          obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
          have hins : (seen.insert e.name).contains y.name = true := by
            rw [hyeq]
            simp
          have hs2 := (hall.1 y (by simp [hy])).2
          rw [hins] at hs2
          exact Bool.noConfusion hs2
      · intro ⟨hall, hnd⟩
        have hfresh : seen.contains e.name = false := (hall e List.mem_cons_self).2
        refine ⟨⟨(hall e List.mem_cons_self).1, hfresh⟩, ⟨?_, hnd.2⟩⟩
        intro y hy
        obtain ⟨hd2, hs2⟩ := hall y (List.mem_cons_of_mem _ (by simp [hy]))
        refine ⟨hd2, ?_⟩
        by_cases heq : e.name = y.name
        · exfalso
          have hmem : e.name ∈ List.map Entry.name rest := by
            exact heq ▸ List.mem_map_of_mem (f := Entry.name) hy
          exact absurd hmem hnd.1
        · rw [insert_contains_ne _ e.name y.name (fun hc => heq (by simpa using hc))]
          exact hs2

/-- `entriesOkB` decides: every entry names a declared variable, and
    the assigned names are pairwise distinct. -/
theorem entriesOkB_iff (m : Model) (es : List Entry) :
    entriesOkB m es = true ↔
      (∀ e ∈ es, ∃ d ∈ m.variables, d.name.name = e.name) ∧
        (es.map (·.name)).Nodup := by
  have hdeclared : ∀ (n : String),
      (Std.HashSet.ofList (m.variables.map (fun d => d.name.name))).contains n = true ↔
        ∃ d ∈ m.variables, d.name.name = n := by
    intro n
    constructor
    · intro hmem
      have hin : n ∈ Std.HashSet.ofList (m.variables.map (fun d => d.name.name)) := by
        simpa using hmem
      rw [Std.HashSet.mem_ofList] at hin
      have hlmem : n ∈ m.variables.map (fun d => d.name.name) :=
        List.contains_iff_mem.mp hin
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hlmem
      exact ⟨d, hd, hdeq⟩
    · rintro ⟨d, hd, hdeq⟩
      have hmem : d.name.name ∈ m.variables.map (fun d => d.name.name) :=
        List.mem_map_of_mem hd
      have hin : d.name.name ∈ Std.HashSet.ofList
          (m.variables.map (fun d => d.name.name)) :=
        Std.HashSet.mem_ofList.mpr (List.contains_iff_mem.mpr hmem)
      have hres : (Std.HashSet.ofList (m.variables.map (fun d => d.name.name))).contains
          d.name.name = true := by simpa using hin
      have hconv : (Std.HashSet.ofList (m.variables.map (fun d => d.name.name))).contains
          n = true := hdeq ▸ hres
      exact hconv
  rw [entriesOkB, entriesOkAux_iff _ es {}]
  constructor
  · rintro ⟨hall, hnd⟩
    refine ⟨?_, hnd⟩
    intro e he
    have h1 := hall e he
    exact (hdeclared e.name).mp h1.1
  · intro ⟨hall, hnd⟩
    refine ⟨?_, hnd⟩
    intro e he
    have h2 := (hdeclared e.name).mpr (hall e he)
    have hempty : ((∅ : Std.HashSet String)).contains e.name = false := by simp
    exact ⟨h2, hempty⟩

/-- The boxed environment is the fast environment (definitionally:
    zeta-reducing the `let` gives exactly `staticEnvFastAsEnv`). -/
theorem staticEnvBox_f (m : Model) : (staticEnvBox m).f = staticEnvFastAsEnv m :=
  rfl

/-- The environment-dependent sub-checks agree under pointwise
    environment agreement (`funext` + `List.all` congruence). -/
private theorem all_ext {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.all_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Duplicate-freedom is preserved by injective maps. -/
private theorem nodup_map_inj {α β : Type} (f : α → β) (hinj : ∀ a b, f a = f b → a = b)
    (l : List α) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hmem
        have hab : a = b := hinj a b hbeq.symm
        subst hab
        exact absurd hb h.1
      · exact ih h.2

/-- `Ident.name` is injective. -/
private theorem Ident_name_inj (a b : Ident) (h : a.name = b.name) : a = b := by
  cases a
  cases b
  simpa using h

/-- If the fast value-namespace check fails, so does the slow one. -/
private theorem slow_nodup_of_fast (m : Model) (hvals : nodupNamesFast
    (m.parameters.map (·.name.name) ++ m.variables.map (·.name.name)) {} = false) :
    nodupIdentB (m.parameters.map (·.name) ++ m.variables.map (·.name)) = false := by
  cases hb : nodupIdentB (m.parameters.map (·.name) ++ m.variables.map (·.name)) with
  | false => rfl
  | true =>
      exfalso
      have hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup :=
        nodupIdentB_iff.mp hb
      have hnd2 : (m.parameters.map (·.name) ++ m.variables.map (·.name)).map (·.name)
          |>.Nodup := nodup_map_inj (·.name) (fun a b h => Ident_name_inj a b h) _ hnd
      have hmap : (m.parameters.map (·.name) ++ m.variables.map (·.name)).map (·.name)
          = m.parameters.map (·.name.name) ++ m.variables.map (·.name.name) := by
        rw [List.map_append, List.map_map, List.map_map]
        rfl
      rw [hmap] at hnd2
      have hfast : nodupNamesFast
          (m.parameters.map (·.name.name) ++ m.variables.map (·.name.name)) {} = true :=
        (nodupNamesFast_iff _ _).mpr ⟨fun _ _ => by simp, hnd2⟩
      rw [hfast] at hvals
      exact Bool.noConfusion hvals

/-- Under name-uniqueness of the model's declarations, the fast
    environment *is* the declarative one. -/
private theorem staticEnvFastAsEnv_eq (m : Model)
    (hpar : (m.parameters.map (·.name.name)).Nodup)
    (hvar : (m.variables.map (·.name.name)).Nodup) :
    staticEnvFastAsEnv m = m.staticEnv := by
  unfold staticEnvFastAsEnv
  exact funext (fun x => staticEnvFast_eq m hpar hvar x)

/-- **The fast twin agrees with `WellFormed`.** -/
theorem wellFormedFastB_iff (m : Model) :
    wellFormedFastB m = true ↔ WellFormed fullSig m := by
  rw [← wellFormedB_iff]
  -- case split on whether the value-namespace is duplicate-free: the
  -- environment agreement is only needed in the duplicate-free case
  cases hvals : nodupNamesFast
      (m.parameters.map (·.name.name) ++ m.variables.map (·.name.name)) {} with
  | false =>
      -- both checkers are false: the second conjunct of each fails
      have hf : wellFormedFastB m = false := by
        simp only [wellFormedFastB, hvals]
        simp
      have hs : wellFormedB fullSig m = false := by
        have hslow : nodupIdentB (m.parameters.map (·.name)
          ++ m.variables.map (·.name)) = false := slow_nodup_of_fast m hvals
        simp only [wellFormedB, hslow]
        simp
      constructor
      · intro habsurd
        rw [hf] at habsurd
        exact Bool.noConfusion habsurd
      · intro habsurd
        rw [hs] at habsurd
        exact Bool.noConfusion habsurd
  | true =>
      -- extract the uniqueness this gives us
      have hnd : (m.parameters.map (·.name.name) ++ m.variables.map (·.name.name)).Nodup :=
        (nodupNamesFast_iff _ _).mp hvals |>.2
      have hpar : (m.parameters.map (·.name.name)).Nodup :=
        List.Nodup.sublist (List.sublist_append_left _ _) hnd
      have hvar : (m.variables.map (·.name.name)).Nodup :=
        List.Nodup.sublist (List.sublist_append_right _ _) hnd
      have henv : staticEnvFastAsEnv m = m.staticEnv :=
        staticEnvFastAsEnv_eq m hpar hvar
      -- rewrite the fast checker into the slow one, componentwise
      have h1 : nodupIdentsFast (m.predicates.map (·.name)) = true ↔
          nodupIdentB (m.predicates.map (·.name)) = true := by
        rw [nodupIdentsFast_iff, nodupIdentB_iff]
      have h2 : ∀ p ∈ m.predicates,
          (nodupIdentsFast (p.params.map (·.name)) = true ↔
            nodupIdentB (p.params.map (·.name)) = true) := by
        intro p _
        rw [nodupIdentsFast_iff, nodupIdentB_iff]
      -- h1 as an equation (not an iff) so it rewrites the head operand
      have h1eq : nodupIdentsFast (m.predicates.map (·.name))
          = nodupIdentB (m.predicates.map (·.name)) := by
        cases ha : nodupIdentsFast (m.predicates.map (·.name)) with
        | true =>
            have hb : nodupIdentB (m.predicates.map (·.name)) = true := h1.mp ha
            rw [hb]
        | false =>
            cases hb : nodupIdentB (m.predicates.map (·.name)) with
            | true =>
                have hcontra := h1.mpr hb
                rw [hcontra] at ha
                exact Bool.noConfusion ha
            | false => rfl
      simp only [wellFormedFastB, wellFormedB, wellFormedEnvFastB, h1eq, henv,
        staticEnvBox_f]
      have hcongr : m.predicates.all (fun p => nodupIdentsFast (p.params.map (·.name)))
          = m.predicates.all (fun p => nodupIdentB (p.params.map (·.name))) :=
        all_ext _ _ _ (fun p hp => by
          have hiff := h2 p hp
          cases ha : nodupIdentsFast (p.params.map (·.name)) with
          | true =>
              have hb : nodupIdentB (p.params.map (·.name)) = true := hiff.mp ha
              rw [hb]
          | false =>
              cases hb : nodupIdentB (p.params.map (·.name)) with
              | true =>
                  have hcontra : nodupIdentsFast (p.params.map (·.name)) = true :=
                    hiff.mpr hb
                  rw [hcontra] at ha
                  exact Bool.noConfusion ha
              | false => rfl)
      rw [hcongr]
      -- the slow checker's second conjunct from the fast one's Nodup
      have hslownd : nodupIdentB (m.parameters.map (·.name)
          ++ m.variables.map (·.name)) = true := by
        rw [nodupIdentB_iff]
        -- ident-list nodup from the name-list nodup: since `Ident`
        -- equality is name equality, the ident lists are nodup iff
        -- their name projections are
        have hpar' : (m.parameters.map (·.name)).Nodup :=
          (ident_nodup_map_iff _).mp (by
            have hmap : (m.parameters.map (·.name)).map (·.name)
                = m.parameters.map (·.name.name) := by
              simp [List.map_map]
            rw [hmap]
            exact hpar)
        have hvar' : (m.variables.map (·.name)).Nodup :=
          (ident_nodup_map_iff _).mp (by
            have hmap : (m.variables.map (·.name)).map (·.name)
                = m.variables.map (·.name.name) := by
              simp [List.map_map]
            rw [hmap]
            exact hvar)
        -- and no parameter name equals a variable name (both map into hnd)
        have hno : ∀ p ∈ m.parameters.map (·.name), ∀ v ∈ m.variables.map (·.name),
            p.name ≠ v.name := by
          intro p hp v hv heq
          have hp' : p.name ∈ m.parameters.map (·.name.name) := by
            obtain ⟨d, hd, hdname⟩ := List.mem_map.mp hp
            exact hdname ▸ List.mem_map_of_mem hd
          have hv' : v.name ∈ m.variables.map (·.name.name) := by
            obtain ⟨d, hd, hdname⟩ := List.mem_map.mp hv
            exact hdname ▸ List.mem_map_of_mem hd
          rw [heq] at hp'
          exact (List.nodup_append.mp hnd).2.2 v.name hp' v.name hv' rfl
        exact List.nodup_append.mpr ⟨hpar', hvar',
          fun p hp v hv heq => hno p hp v hv (congrArg (·.name) heq)⟩
      simp only [hvals, hslownd, Bool.and_assoc]

/-- `List.find? p l = none` exactly when `p` fails on every element. -/
private theorem find?_none_iff {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.find? p = none ↔ ∀ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
      cases h : p a with
      | false =>
          rw [List.find?_cons, h, ih]
          constructor
          · intro hall x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact h
            · exact hall x hx'
          · intro hall x hx
            exact hall x (List.mem_cons_of_mem _ hx)
      | true =>
          rw [List.find?_cons, h]
          constructor
          · intro hcontra _
            exact absurd hcontra (by simp)
          · intro hall
            have hx : p a = false := hall a List.mem_cons_self
            rw [hx] at h
            exact Bool.noConfusion h

/-- `firstUnsupported m = none` exactly when every constraint name is
    checkable. -/
theorem firstUnsupported_none_iff (m : Model) :
    firstUnsupported m = none ↔
      ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames := by
  unfold firstUnsupported
  cases hfind : m.constraints.find? (fun c =>
    !(decide (c.name.name ∈ fullCheckableNames))) with
  | none =>
      have hall : ∀ x ∈ m.constraints,
          (!(decide (x.name.name ∈ fullCheckableNames))) = false :=
        (find?_none_iff _ _).mp hfind

      simp only [Option.map_none]
      constructor
      · intro _ c hc
        have hfail := hall c hc
        cases hchk : decide (c.name.name ∈ fullCheckableNames) with
        | true => exact of_decide_eq_true hchk
        | false =>
            exfalso
            have hfound : (!(decide (c.name.name ∈ fullCheckableNames))) = true := by
              simp only [Bool.not_eq_true', hchk]
            rw [hfound] at hfail
            exact Bool.noConfusion hfail
      · intro _
        trivial
  | some c =>
      have hfound : (!(decide (c.name.name ∈ fullCheckableNames))) = true := by
        have hsome := List.find?_some hfind
        simpa only [Bool.not_eq_true'] using hsome
      simp only [Option.map_some]
      constructor
      · intro habsurd
        exact absurd habsurd (by simp)
      · intro hall
        exfalso
        have hchk : decide (c.name.name ∈ fullCheckableNames) = true :=
          decide_eq_true (hall c (List.mem_of_find?_eq_some hfind))
        rw [hchk] at hfound
        exact Bool.noConfusion hfound

/-- Membership along a list preserves the failing element's position:
    the first list element on which one predicate fails is the first
    on which an agreeing predicate fails. -/
private theorem find?_eq_of_forall {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.find?_cons]
      cases hp : p a with
      | true =>
          have hq : q a = true := by rw [← h a List.mem_cons_self]; exact hp
          simp only [hq]
      | false =>
          have hq : q a = false := by
              rw [h a List.mem_cons_self] at hp
              exact hp
          simp only [hq]
          exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The fast name gate returns exactly the slow gate's answer. -/
theorem firstUnsupportedFast_eq (m : Model) :
    firstUnsupportedFast m = firstUnsupported m := by
  unfold firstUnsupportedFast firstUnsupported
  rw [find?_eq_of_forall
    (fun c => !(decide (c.name.name ∈ fullCheckableNames)))
    (fun c => !(dispatchMap[c.name.name]?).isSome)
    m.constraints
    (fun c _ => by
      have h1 : (dispatchMap[c.name.name]?).isSome = true ↔
          c.name.name ∈ fullCheckableNames := dispatchMap_isSome_iff_mem
      by_cases hm : c.name.name ∈ fullCheckableNames
      · have hmap : (dispatchMap[c.name.name]?).isSome = true := h1.mpr hm
        rw [hmap, decide_eq_true hm]
      · have hns : ¬((dispatchMap[c.name.name]?).isSome = true) := by
          intro hcontra
          exact hm (h1.mp hcontra)
        rw [Bool.eq_false_iff.mpr hns, decide_eq_false_iff_not.mpr hm])]

/-- **Correctness of the front door.**  `checkModelSolution m sol =
    .accepted` if and only if the model is statically well formed
    under `fullSig`, every constraint name belongs to
    `fullCheckableNames`, and the solution string parses to entries
    that are well formed (declared variables only, no duplicates)
    and whose completed store satisfies `Satisfies fullSig
    fullInterp`. -/
theorem checkModelSolution_correct_parse (m : Model) (sol : String) :
    checkModelSolution m sol = .accepted ↔
      WellFormed fullSig m ∧
      (∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) ∧
      ∃ es, parseSolution (stripSeparators sol) = .ok es ∧
        entriesOkB m es ∧
        Satisfies fullSig fullInterp m (completedStore m es) := by
  unfold checkModelSolution
  cases huns : firstUnsupported m with
  | some n =>
      constructor
      · intro habsurd
        exact Outcome.noConfusion habsurd
      · rintro ⟨_, hnames, _⟩
        have hnone : firstUnsupported m = none :=
          (firstUnsupported_none_iff m).mpr hnames
        rw [hnone] at huns
        exact absurd huns (by simp)
  | none =>
      by_cases hwf : wellFormedFastB m = true
      · rw [if_pos hwf]
        cases hparse : parseSolution (stripSeparators sol) with
        | error e =>
            constructor
            · intro habsurd
              exact Outcome.noConfusion habsurd
            · rintro ⟨_, _, es', hes, _, _⟩
              exact absurd hes (by simp)
        | ok es =>
            by_cases hentries : entriesOkB m es = true
            · show (if entriesOkB m es = true then
                  (if checkSolutionFull m sol = true then Outcome.accepted
                   else Outcome.unsatisfied)
                else Outcome.malformedSolution
                  "assigns a parameter, an unknown name, or a name twice") = Outcome.accepted ↔ _
              simp only [hentries, if_true]
              by_cases hcheck : checkSolutionFull m sol = true
              · simp only [hcheck, if_true]
                constructor
                · intro _
                  obtain ⟨es', hparse', hsat⟩ :=
                    (checkSolutionFull_correct_parse m sol
                      ((firstUnsupported_none_iff m).mp huns)).mp hcheck
                  have heq : es' = es := Except.ok.inj (hparse'.symm.trans hparse)
                  subst heq
                  exact ⟨(wellFormedFastB_iff m).mp hwf,
                    (firstUnsupported_none_iff m).mp huns, es', rfl, hentries,
                      (wellFormedFastB_iff m).mp hwf, hsat⟩
                · rintro ⟨_, _, _, _, _, _⟩
                  trivial
              · simp only [hcheck]
                constructor
                · intro habsurd
                  exact Outcome.noConfusion habsurd
                · rintro ⟨_, _, es', hparse', hentries', hsat⟩
                  have hfull := (checkSolutionFull_correct_parse m sol
                    ((firstUnsupported_none_iff m).mp huns)).mpr
                    ⟨es', hparse.trans hparse', hsat.2⟩
                  rw [hfull] at hcheck
                  exact (hcheck rfl).elim
            · simp only [hentries]
              constructor
              · intro habsurd
                exact Outcome.noConfusion habsurd
              · rintro ⟨_, _, es2, hparse2, hes, _⟩
                have heq : es2 = es := Except.ok.inj hparse2.symm
                rw [heq] at hes
                exact absurd hes hentries
      · rw [if_neg (by simp [hwf])]
        constructor
        · intro habsurd
          exact Outcome.noConfusion habsurd
        · rintro ⟨hwf', _⟩
          have hfast : wellFormedFastB m = true := (wellFormedFastB_iff m).mpr hwf'
          rw [hfast] at hwf
          exact (hwf rfl).elim

/-- The front door is sound and complete against the independent,
    value-sensitive solution grammar, within the supported model signature.
    In particular, valid assignment syntax is not defined using the parser. -/
theorem checkModelSolution_correct (m : Model) (sol : String) :
    checkModelSolution m sol = .accepted ↔
      WellFormed fullSig m ∧
      (∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) ∧
      ∃ es, SolutionGrammar (stripSeparators sol) es ∧
        entriesOkB m es ∧
        Satisfies fullSig fullInterp m (completedStore m es) := by
  rw [checkModelSolution_correct_parse]
  constructor
  · rintro ⟨hw, hn, es, hp, he, hs⟩
    exact ⟨hw, hn, es, parseSolution_eq_ok_iff_grammar.mp hp, he, hs⟩
  · rintro ⟨hw, hn, es, hg, he, hs⟩
    exact ⟨hw, hn, es, parseSolution_eq_ok_iff_grammar.mpr hg, he, hs⟩

/-- **What an accepted solution means.**  The store that
    `checkModelSolution_correct` speaks about is tied to the solution
    string and the model: it maps every assigned name to the value
    written in the solution, gives every parameter its declared value,
    and satisfies the model. -/
theorem checkModelSolution_accepted {m : Model} {sol : String}
    (h : checkModelSolution m sol = .accepted) :
    ∃ es, parseSolution (stripSeparators sol) = .ok es ∧
      (∀ e ∈ es, completedStore m es ⟨e.name⟩ = some e.value.toValue) ∧
      ParamHonest m (completedStore m es) ∧
      Satisfies fullSig fullInterp m (completedStore m es) := by
  obtain ⟨hwf, _, es, hparse, hok, hsat⟩ := (checkModelSolution_correct_parse m sol).mp h
  obtain ⟨hdecl, hnd⟩ := (entriesOkB_iff m es).mp hok
  have hvu := hwf.valueNamesUnique
  rw [List.nodup_append] at hvu
  obtain ⟨hpn, _, hdisj⟩ := hvu
  refine ⟨es, hparse, fun e he => completedStore_entry hnd he, ?_, hsat⟩
  apply completedStore_paramHonest
  · have hmap : (m.parameters.map fun d => d.name.name) =
        (m.parameters.map (·.name)).map Ident.name := by
      simp [List.map_map, Function.comp_def]
    rw [hmap]
    exact List.Pairwise.map Ident.name (fun _ _ hab heq => hab (Ident.eq_of_name_eq heq)) hpn
  · intro e he d hd heq
    obtain ⟨dv, hdv, hname⟩ := hdecl e he
    exact hdisj d.name (List.mem_map_of_mem hd) dv.name (List.mem_map_of_mem hdv)
      (Ident.eq_of_name_eq (by rw [hname, heq]))

/-- The fast front door returns exactly the verified front door's
    outcome on every model and solution, so `checkModelSolution_correct`
    and `checkModelSolution_accepted` describe its verdicts too. -/
theorem checkModelSolutionFast_eq (m : Model) (sol : String) :
    checkModelSolutionFast m sol = checkModelSolution m sol := by
  unfold checkModelSolutionFast checkModelSolution
  rw [firstUnsupportedFast_eq]
  cases hu : firstUnsupported m with
  | some n => rfl
  | none =>
    simp only
    rw [checkSolutionFullFast_eq m sol ((firstUnsupported_none_iff m).mp hu)]

/-- A declaration without an initializer is a fixed point of one
    completion step: `initValue` returns `none` on it, so the step
    returns the map unchanged. -/
private theorem completePass_step_none {d : VarDeclItem}
    (hd : isInitVar d = false) (known : Std.HashMap String Value) :
    completePass [d] known = known := by
  cases d with
  | basic ty n anns opt =>
      cases opt with
      | none =>
          simp only [completePass, List.foldl_cons, List.foldl_nil, initValue]
          split <;> rfl
      | some v => simp [isInitVar] at hd
  | array ty n anns es => simp [isInitVar] at hd

/-- The completion pass over the filtered plan is the pass over all
    declarations: the skipped declarations (no initializer) are fixed
    points of their step. -/
private theorem completePass_filter_eq (vars : List VarDeclItem)
    (known : Std.HashMap String Value) :
    completePass (vars.filter isInitVar) known = completePass vars known := by
  induction vars generalizing known with
  | nil => rfl
  | cons d rest ih =>
      cases hd : isInitVar d with
      | true =>
          simp only [completePass, List.filter_cons_of_pos hd, List.foldl_cons]
          exact ih _
      | false =>
          have hnf : ¬ isInitVar d = true := by rw [hd]; simp
          rw [List.filter_cons_of_neg hnf, ih known,
            show completePass (d :: rest) known = completePass rest (completePass [d] known)
              from rfl, completePass_step_none hd known]

/-- The plan lemma: completing along the filtered plan computes the
    same map as completing over every declaration, for every fuel and
    starting map. -/
private theorem completeFix_filter_eq (vars : List VarDeclItem) :
    ∀ (fuel : Nat) (known : Std.HashMap String Value),
      completeFix (vars.filter isInitVar) fuel known
        = completeFix vars fuel known := by
  intro fuel
  induction fuel with
  | zero => intro known; rfl
  | succ n ih =>
      intro known
      simp only [completeFix]
      rw [completePass_filter_eq]
      cases (completePass vars known).size == known.size with
      | true => rfl
      | false => exact ih _

/-- The prepared box *is* the reference box on a freshly prepared
    model (definitionally: `completedBoxPrepared` unfolds to
    `completedBox p.model es` and `prepareModel`'s field is `m`). -/
theorem completedBoxPrepared_eq (m : Model) (es : List Entry) :
    completedBoxPrepared (prepareModel m) es = completedBox m es := rfl

/-- The incremental twin computes the reference construction: the
    entry inserts into the prepared parameter base are the reference's
    inserts into `paramMap`, and the completion along the filtered plan
    is the completion over all declarations (the plan lemma).  This is
    the proof backing the `implemented_by` seam of
    `completedBoxPrepared`. -/
private theorem completedBoxPreparedI_eq (m : Model) (es : List Entry) :
    completedBoxPreparedI (prepareModel m) es = completedBox m es := by
  show (⟨mapStore (completeFix (m.variables.filter isInitVar) m.variables.length
    (es.foldl (fun acc e => acc.insert e.name e.value.toValue)
      (paramMap m)))⟩ : StoreBox) = _
  rw [completeFix_filter_eq]
  rfl

/-- The prepared constraint list preserves the constraint items in
    order. -/
theorem prepareConstraints_map_item (cs : List ConstraintItem) :
    (prepareConstraints cs).map PreparedConstraint.item = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [prepareConstraints, ih]

/-- A freshly prepared constraint decides the same as the fast
    dynamic checker's per-constraint test on checkable names: the
    stored twin is the map lookup `preparedInterpB` applies. -/
private theorem preparedConstraintHoldsB_eq (store : Store)
    (c : ConstraintItem)
    (hname : c.name.name ∈ fullCheckableNames) :
    preparedConstraintHoldsB store { item := c, twin := dispatchMap[c.name.name]? } =
      (match c.args.mapM (Expr.eval store) with
       | some args => preparedInterpB c.name args
       | none => false) := by
  set_option maxRecDepth 4000 in
  obtain ⟨fn, hfn⟩ := dispatchMap_get?_some_of_mem hname
  unfold preparedConstraintHoldsB preparedInterpB
  rw [hfn]
  cases hargs : c.args.mapM (Expr.eval store) with
  | none => rfl
  | some args =>
      show (match some fn with
        | none => false
        | some fn =>
            fn c.name args) = fn c.name args
      rfl

/-- The pre-dispatched constraint list decides the same as the fast
    dynamic checker's constraint test, whenever every constraint name
    is checkable (the scope the name gate establishes). -/
private theorem prepared_all_eq (store : Store) (cs : List ConstraintItem)
    (hnames : ∀ c ∈ cs, c.name.name ∈ fullCheckableNames) :
    (prepareConstraints cs).all (fun pc => preparedConstraintHoldsB store pc) =
      cs.all (fun c =>
        match c.args.mapM (Expr.eval store) with
        | some args => preparedInterpB c.name args
        | none => false) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      have h1 := preparedConstraintHoldsB_eq store c (hnames c List.mem_cons_self)
      have h2 := ih (fun x hx => hnames x (List.mem_cons_of_mem _ hx))
      simp only [prepareConstraints, List.all_cons]
      rw [h1, h2]

/-- The prepared dynamic part agrees with the fast dynamic checker on
    models whose constraints are all checkable. -/
private theorem checkPreparedDyn_eq (m : Model) (sol : String)
    (hnames : ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) :
    checkPreparedDyn (prepareModel m) sol = checkSolutionFullFast m sol := by
  unfold checkPreparedDyn prepareModel checkSolutionFullFast
  cases LeanFzn.Checker.Solution.parseSolution
      (LeanFzn.Checker.Solution.stripSeparators sol) with
  | error _ => rfl
  | ok es =>
      show (LeanFzn.Checker.Solution.allAssignedB
          (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          LeanFzn.Checker.Solution.varDeclsOkB
            (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          (prepareConstraints m.constraints).all (fun pc =>
            preparedConstraintHoldsB (LeanFzn.Checker.Solution.completedBox m es).f pc)) =
        (LeanFzn.Checker.Solution.allAssignedB
          (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          LeanFzn.Checker.Solution.varDeclsOkB
            (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          m.constraints.all (fun c =>
            match c.args.mapM (Expr.eval (LeanFzn.Checker.Solution.completedBox m es).f) with
            | some args => preparedInterpB c.name args
            | none => false))
      rw [prepared_all_eq _ _ hnames]

end LeanFzn.Checker

/-
File: LeanFzn/Solver/Propagation/Proofs/Singleton.lean

Purpose:
  PLAN Step 2.E execution order, item 1 — the singleton
  characterization. When the engine's domains are all singletons and
  the leaf assignment is the `singletonAssignment` value, every fitting
  assignment IS that value: the state represents exactly one
  assignment, so semantics at the leaf reduce to evaluation at `a`.

  Pure list/assignment lemma, no constraint semantics: everything
  reduces to the length law and the pointwise law of the singleton
  `mapM` plus the `Fits` membership characterization.

Dependencies:
  - LeanFzn.Solver.Reference.Engine: `State`, `allSingleton`, `singletonAssignment`.
  - LeanFzn.Solver.Propagation.Encoding: assignment/domain vocabulary.

DAG:
  LeanFzn.Solver.UIP.Engine -> LeanFzn.Solver.UIP.Proofs.Singleton -> LeanFzn.Solver.UIP.Proofs.Search
    (leaf-shape consumption, Step 2.E item 2)
-/

import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Encoding
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Singleton domain characterization -/

/-- A state whose domains pass `allSingleton` has every domain enumeration
    a singleton list: `(st.domains[s]).enum = [v_s]` for in-range `s`. -/
theorem dom_of_allSingleton {st : State} (hsingle : allSingleton st = true)
    {s : Nat} (hs : s < st.domains.length) :
    ∃ v : Value, (st.domains[s]).enum = [v] := by
  have hall : st.domains.all (fun d => d.length == 1) = true := hsingle
  rw [List.all_eq_true] at hall
  have hmem := hall (st.domains[s]) (List.getElem_mem hs)
  have hlen1 : st.domains[s].length = 1 := by simpa using hmem
  have hlen : (st.domains[s]).enum.length = 1 := by
    rw [← Dom.length_eq_enum]
    exact hlen1
  exact List.length_eq_one_iff.mp hlen

/-- Under all-singleton domains, `singletonAssignment st` maps each slot
    to the domain's value: on the list level first. -/
private theorem mapM_singleton_eq {doms : List (List Value)}
    (hall : ∀ i (h : i < doms.length), ∃ v, doms[i] = [v]) :
    ∃ a : Assignment, doms.mapM (fun d => match d with
      | [v] => some v | _ => none) = some a := by
  induction doms with
  | nil => exact ⟨[], rfl⟩
  | cons d rest ih =>
      -- d is the head domain (slot 0), so d = [v] for some v
      obtain ⟨v0, hv0⟩ := hall 0 (Nat.zero_lt_succ _)
      have hlenc : (d :: rest).length = rest.length + 1 := rfl
      -- from (d :: rest)[0] = [v0]: d = [v0]
      have hd : d = [v0] := by
        have : (d :: rest)[0] = d := rfl
        rw [this] at hv0
        exact hv0
      -- the recursive call: rest's slots are 1-shifted
      have ihall : ∀ (i : Nat) (h : i < rest.length),
          ∃ w, rest[i] = [w] := by
        intro i hi
        obtain ⟨w, hw⟩ := hall (i + 1) (by omega)
        have hstep : (d :: rest)[i + 1] = rest[i] := rfl
        exact ⟨w, hstep ▸ hw⟩
      obtain ⟨a, ha⟩ := ih ihall
      refine ⟨v0 :: a, ?_⟩
      show ((List.mapM (fun d => match d with
        | [v] => some v | _ => none) (d :: rest))) = some (v0 :: a)
      rw [List.mapM_cons]
      simp only [hd]
      rw [ha]
      rfl

/-- The singleton-map `mapM` computes the pointwise singleton values with
    the same length as the domain list. -/
private theorem mapM_singleton_length {doms : List (List Value)}
    {a : Assignment}
    (h : doms.mapM (fun d => match d with
      | [v] => some v | _ => none) = some a) :
    a.length = doms.length := by
  induction doms generalizing a with
  | nil =>
      cases h
      rfl
  | cons d rest ih =>
      -- d.length must be 1 (else the mapM fails): case on d directly
      match hdm : d with
      | [v0] =>
          have hdgoal : d = [v0] := hdm
          subst hdgoal
          -- h : mapM f ([v0] :: rest) = some a
          rw [List.mapM_cons] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          match hm : List.mapM (fun d => match d with
              | [v] => some v | _ => none) rest with
          | none => rw [hm] at h; simp at h
          | some a2 =>
              rw [hm] at h
              simp only [Option.bind_some, pure] at h
              have hexact : a = v0 :: a2 := Option.some.inj h.symm
              have hln := ih hm
              show a.length = ([v0] :: rest).length
              rw [hexact]
              show (v0 :: a2).length = ([v0] :: rest).length
              simp only [List.length_cons]
              rw [hln]
      | [] =>
          have this : d = [] := hdm
          subst this
          cases h
      | v1 :: v2 :: r2 =>
          have this : d = v1 :: v2 :: r2 := hdm
          subst this
          cases h

/-- Pointwise characterization of the singleton mapM: at every in-range
    position `n`, the result's value equals the singleton domain's
    value. -/
private theorem mapM_singleton_get {doms : List (List Value)}
    {a : Assignment}
    (h : doms.mapM (fun d => match d with
      | [v] => some v | _ => none) = some a)
    {n : Nat} (hn : n < doms.length) :
    a[n]? = doms[n].head? := by
  induction doms generalizing a n with
  | nil => cases hn
  | cons d rest ih =>
      match hdm : d with
      | [v0] =>
          have hdgoal : d = [v0] := hdm
          subst hdgoal
          rw [List.mapM_cons] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          match hm : List.mapM (fun d => match d with
              | [v] => some v | _ => none) rest with
          | none => rw [hm] at h; simp at h
          | some a2 =>
              rw [hm] at h
              simp only [Option.bind_some, pure] at h
              have hexact : a = v0 :: a2 := Option.some.inj h.symm
              subst hexact
              cases n with
              | zero => simp
              | succ n' =>
                  have hshift : ([v0] :: rest).length = rest.length + 1 := rfl
                  have hn' : n' < rest.length := by omega
                  have hstep : (v0 :: a2)[n' + 1]? = a2[n']? := by simp
                  have hstep2 : ([v0] :: rest)[n' + 1].head?
                      = rest[n'].head? := by
                    simp [List.getElem_cons_succ]
                  rw [hstep, hstep2]
                  exact ih hm hn'
      | [] =>
          have this : d = [] := hdm
          subst this
          cases h
      | v1 :: v2 :: r2 =>
          have this : d = v1 :: v2 :: r2 := hdm
          subst this
          cases h

/-! ### The state-level characterization -/

/-- THE SINGLETON CHARACTERIZATION (PLAN step 2.E.1): under
    all-singleton domains, every fitting assignment equals the
    singleton assignment. -/
theorem fits_allSingleton_eq {st : State} {a b : Assignment}
    (hsingle : allSingleton st = true)
    (hfit : b.Fits st.domains)
    (ha : singletonAssignment st = some a) :
    b = a := by
  -- obtain the singleton-domain shape characterization on enumerations
  have hall : ∀ i (h : i < st.domains.length),
      ∃ v, (st.domains[i]).enum = [v] :=
    fun i h => dom_of_allSingleton hsingle h
  have hall' : ∀ i (h : i < (st.domains.map Dom.enum).length),
      ∃ v, (st.domains.map Dom.enum)[i] = [v] := by
    intro i hi
    rw [List.length_map] at hi
    obtain ⟨v, hv⟩ := hall i hi
    exact ⟨v, by rw [List.getElem_map]; exact hv⟩
  -- the singleton assignment is the singleton `mapM` of the enumerations
  have hmap : (st.domains.map Dom.enum).mapM
        (fun d => match d with
          | [v] => some v | _ => none) =
      st.domains.mapM (fun d => match Dom.enum d with
          | [v] => some v | _ => none) :=
    List.mapM_map (f := Dom.enum)
      (g := fun l => match l with | [v] => some v | _ => none) (l := st.domains)
  have hmapM : ∃ c, (st.domains.map Dom.enum).mapM (fun d => match d with
      | [v] => some v | _ => none) = some c :=
    mapM_singleton_eq hall'
  obtain ⟨c, hc⟩ := hmapM
  -- a = c (both bind the same mapM result)
  rw [show singletonAssignment st = (st.domains.map Dom.enum).mapM
      (fun d => match d with
        | [v] => some v | _ => none) from by
      unfold singletonAssignment
      exact hmap.symm] at ha
  -- hc and ha bind the same value
  have hca : a = c := by
    rw [hc] at ha
    exact Option.some.inj ha.symm
  subst c
  -- Now c is a; hc : mapM ... = some a.
  show b = a
  -- per-slot equality between two fitting assignments of the same
  -- all-singleton domain list: use data-level list equality via
  -- List.ext_get.
  refine List.ext_get ?_ ?_
  · -- length agreement
    have hlen := mapM_singleton_length hc
    have hmapLen : (st.domains.map Dom.enum).length = st.domains.length :=
      List.length_map ..
    rw [hfit.1, ← hmapLen]
    exact hlen.symm
  · intro n hn hn2
    -- a[n] = the singleton domain's value (pointwise mapM law), and
    -- b[n] = the same singleton value (fit membership).
    have hndom : n < st.domains.length := by
      have := hfit.1
      omega
    obtain ⟨v, hv⟩ := hall n hndom
    have hval : (st.domains[n]).enum.head? = some v := by
      rw [hv]; simp
    have hlenmap : n < (st.domains.map Dom.enum).length := by
      rwa [List.length_map]
    have ha_n := mapM_singleton_get hc hlenmap
    rw [List.getElem_map, hval] at ha_n
    -- b[n] = v via singleton membership (b[n] ∈ [v] from the fit)
    have hblen : n < b.length := by
      have := hfit.1
      omega
    have hget : b[n]? = some (b[n]) := List.getElem?_eq_some_iff.mpr
      ⟨hblen, rfl⟩
    have hmem := hfit.2 n (b[n]) hget
    have hgetD : st.domains.getD n Dom.empty = st.domains[n] := by
      show (st.domains[n]?.getD Dom.empty) = st.domains[n]
      rw [List.getElem?_eq_some_iff.mpr ⟨hndom, rfl⟩]
      rfl
    rw [domEmpty_eq] at hmem
    rw [hgetD] at hmem
    have hmemEnum : b[n] ∈ (st.domains[n]).enum := by
      rw [← domElems_eq_enum, ← DomainLike.mem_iff]
      exact hmem
    rw [hv] at hmemEnum
    have hmemv : b[n] = v := by simpa using hmemEnum
    -- getElem agreement from b[n]? = some v and a[n]? = some v:
    have hbeq : b.get ⟨n, hn⟩ = v := by
      have hget2 : b.get ⟨n, hn⟩ = b[n] := rfl
      rw [hget2, hmemv]
    have haeq : a.get ⟨n, hn2⟩ = v := by
      have hget2 : a.get ⟨n, hn2⟩ = a[n] := rfl
      obtain ⟨hgt, hgv⟩ := List.getElem?_eq_some_iff.mp ha_n
      rw [hget2, hgv]
    rw [hbeq, haeq]

end LeanFzn.Solver.Propagation

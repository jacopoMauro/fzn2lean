/-
Purpose: Kernel value presentations, permutation proofs and certified annotated search adapters.
Dependencies: Config.Annotations, Config.Kernel, kernel heuristic search.
DAG: Common annotation tables -> kernel presentation -> public solve/optimization.
-/
import LeanFzn.Legacy.Integration.Kernel.Heur
import LeanFzn.Integration.Config.Annotations
import LeanFzn.Legacy.Integration.SearchConfig

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgEmissionTyped LeanFzn.Solver.UIP.LcgMixedCompiledKit
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedPhaseTerminal
open LeanFzn.Solver.UIP.LcgSeedClauses

/-- The rank of `v` in the activity-ordered enumeration of `d`, if the
    domain is small enough to enumerate and `v` occurs.  This is the phase
    rank consumed by `AnnValOrder.atRank`. -/
def phaseRank? (d : Domain) (v : Value) : Option Nat :=
  if LcgHeur.enumSmallB d then
    let vs := Dom.enum d
    if vs.contains v then some (vs.idxOf v) else none
  else none

/-- F3 solution-guided value orders: for every slot, rotate the previous
    round's incumbent value to the front of its activity-ordered domain.
    Without a previous solution (the first round) there are no orders, so the
    presentation is the unchanged activity order.  Slots whose incumbent value
    is absent (or whose domain is too wide to enumerate) keep `none`. -/
def phaseOrders (p : CompiledProblem DomConstraint)
    (prev : Option (List Value)) : List AnnValOrder :=
  match prev with
  | none => []
  | some a =>
      (LcgHeur.heurDomains p).zipIdx.map fun (d, s) =>
        match a[s]? with
        | some v =>
            match phaseRank? d v with
            | some r => .atRank r
            | none => .none
        | none => .none

/-- F3 per-slot orders for the static value strategies and the phase-saving
    strategy; `--val=annot` keeps the F2 annotation table. -/
def configOrders (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) : List AnnValOrder :=
  match o.val with
  | .annot => annotOrders p.source p.names
  | .min => List.replicate p.domains.length .min
  | .max => List.replicate p.domains.length .max
  | .median => List.replicate p.domains.length .median
  | .incumbent => phaseOrders p prev
  | .act => []

/-! ## §3 Value presentations -/

/-- A total order key for the compiled (int/bool) values. -/
def annotValueKey : Value → Int
  | .int i => i
  | .bool false => 0
  | .bool true => 1
  | _ => 0

/-- Ascending value order (stable). -/
def ascValues (vs : List Value) : List Value :=
  vs.mergeSort fun a b => decide (annotValueKey a ≤ annotValueKey b)

/-- Descending value order. -/
def descValues (vs : List Value) : List Value :=
  (ascValues vs).reverse

/-- Median-first alternating keys: distance from the middle of the ascending
    list, ties by ascending rank (lower rank first). -/
def medianKeyAux (n : Nat) : Nat → List Value → List (Nat × Nat × Value)
  | _, [] => []
  | i, v :: rest =>
      (Int.natAbs ((2 * (i : Int)) - (((n - 1 : Nat) : Int))), i, v) ::
        medianKeyAux n (i + 1) rest

/-- The values of `vs` (already ascending) in median-first alternating order. -/
def medianValues (vs : List Value) : List Value :=
  ((medianKeyAux vs.length 0 vs).mergeSort
      fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2

/-- One domain in the requested annotation value order.  Domains wider than
    the activity presentation's enumeration guard are returned unchanged. -/
def sortDomAnnot (ord : AnnValOrder) (d : Domain) : Domain :=
  if LcgHeur.enumSmallB d then
    match ord with
    | .min => Dom.ofList (ascValues (Dom.enum d))
    | .max => Dom.ofList (descValues (Dom.enum d))
    | .median => Dom.ofList (medianValues (ascValues (Dom.enum d)))
    | .split => Dom.ofList (ascValues (Dom.enum d))
    | .reverseSplit => Dom.ofList (descValues (Dom.enum d))
    | .atRank r =>
        let vs := Dom.enum d
        if h : r < vs.length then
          let v := vs[r]
          Dom.ofList (v :: vs.erase v)
        else d
    | .none => d
  else d

/-! ## §4 Permutation facts -/

theorem ascValues_perm (vs : List Value) : (ascValues vs).Perm vs :=
  List.mergeSort_perm _ _

theorem descValues_perm (vs : List Value) : (descValues vs).Perm vs :=
  (List.reverse_perm (ascValues vs)).trans (ascValues_perm vs)

theorem medianKeyAux_map (n i : Nat) (vs : List Value) :
    (medianKeyAux n i vs).map (fun p => p.2.2) = vs := by
  induction vs generalizing i with
  | nil => rfl
  | cons v rest ih =>
      simp only [medianKeyAux, List.map_cons]
      rw [ih]

theorem medianValues_perm (vs : List Value) : (medianValues vs).Perm vs := by
  unfold medianValues
  have h := (List.mergeSort_perm (medianKeyAux vs.length 0 vs)
    (fun p q => decide (p.1 ≤ q.1))).map (fun p => p.2.2)
  rwa [medianKeyAux_map] at h

/-- The annotation value order of one slot is a permutation of the domain. -/
theorem dom_ofList_perm {vs : List Value} {d : Domain}
    (h : vs.Perm (Dom.enum d)) : (Dom.ofList vs).Perm d := by
  show (Dom.enum (Dom.ofList vs)).Perm (Dom.enum d)
  rw [Dom.enum_ofList]
  exact h

/-- The annotation value order of one slot is a permutation of the domain. -/
theorem sortDomAnnot_perm (ord : AnnValOrder) (d : Domain) :
    (sortDomAnnot ord d).Perm d := by
  cases ord with
  | min =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using
          dom_ofList_perm (ascValues_perm (Dom.enum d))
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | max =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using
          dom_ofList_perm (descValues_perm (Dom.enum d))
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | median =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using
          dom_ofList_perm ((medianValues_perm (ascValues (Dom.enum d))).trans
            (ascValues_perm (Dom.enum d)))
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | split =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using
          dom_ofList_perm (ascValues_perm (Dom.enum d))
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | reverseSplit =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using
          dom_ofList_perm (descValues_perm (Dom.enum d))
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | atRank r =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · by_cases hr : r < (Dom.enum d).length
        · simpa [sortDomAnnot, hsmall, hr] using
            dom_ofList_perm
              (List.perm_cons_erase (List.getElem_mem hr)).symm
        · simpa [sortDomAnnot, hsmall, hr] using Dom.Perm.refl d
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
  | none =>
      by_cases hsmall : LcgHeur.enumSmallB d = true
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d
      · simpa [sortDomAnnot, hsmall] using Dom.Perm.refl d

/-- The annotation value order keeps the empty domain empty. -/
theorem sortDomAnnot_nil (ord : AnnValOrder) :
    sortDomAnnot ord Dom.empty = Dom.empty := by
  cases ord <;> simp [sortDomAnnot, ascValues, descValues, medianValues,
    medianKeyAux, LcgHeur.enumSmallB, Dom.empty]

/-! ## §5 The presentation and its transfer -/

/-- The per-slot presentation induced by the annotation table. -/
def annotOrder (orders : List AnnValOrder) : Nat → Domain → Domain :=
  fun s d => sortDomAnnot (orders.getD s .none) d

/-- The annotation presentation of the activity-ordered box. -/
def annotDomains (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) : List Domain :=
  LcgHeur.reorderAuxWith (annotOrder orders) 0 (LcgHeur.heurDomains p)

/-- The annotation presentation is a per-slot permutation of the activity
    presentation. -/
theorem annotDomains_perm (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (s : Nat) (d : Domain) :
    (annotOrder orders s d).Perm d :=
  sortDomAnnot_perm _ _

theorem annotDomains_nil (orders : List AnnValOrder) (s : Nat) :
    annotOrder orders s Dom.empty = Dom.empty :=
  sortDomAnnot_nil _

theorem annotDomains_length (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) :
    (annotDomains p orders).length = p.domains.length := by
  unfold annotDomains
  rw [LcgHeur.reorderAuxWith_length, LcgHeur.heurDomains_eq,
    LcgHeur.reorderAux_length]

theorem annotDomains_getElem? (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (i : Nat) :
    (annotDomains p orders)[i]? =
      (LcgHeur.heurDomains p)[i]?.map (annotOrder orders i) := by
  unfold annotDomains
  simpa using
    LcgHeur.reorderAuxWith_getElem? (annotOrder orders) 0
      (LcgHeur.heurDomains p) i

theorem mem_annotDomains_perm (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) {d' : Domain}
    (h : d' ∈ annotDomains p orders) :
    ∃ d ∈ LcgHeur.heurDomains p, d'.Perm d :=
  LcgHeur.mem_reorderAuxWith_perm (annotDomains_perm p orders) 0
    (LcgHeur.heurDomains p) h

theorem getD_annotDomains (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (i : Nat) :
    (annotDomains p orders).getD i Dom.empty =
      annotOrder orders i ((LcgHeur.heurDomains p).getD i Dom.empty) := by
  unfold annotDomains
  simpa using LcgHeur.reorderAuxWith_getD (annotDomains_perm p orders)
    (annotDomains_nil orders) 0 (LcgHeur.heurDomains p) i

/-- `fitsB` at the annotation box is the compiled problem's `fitsB`. -/
theorem fitsB_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (a : Assignment) :
    fitsB { lcgProblem p with domains := annotDomains p orders } a
      = fitsB (lcgProblem p) a := by
  unfold annotDomains
  change fitsB { LcgHeur.heurProblem p with
      domains := LcgHeur.reorderAuxWith (annotOrder orders) 0
        (LcgHeur.heurProblem p).domains } a = fitsB (lcgProblem p) a
  rw [LcgHeur.fitsB_reorderAuxWith (annotDomains_perm p orders)
    (annotDomains_nil orders) 0 (LcgHeur.heurProblem p) a]
  exact LcgHeur.fitsB_heur p a

/-- `Fits` (the Prop-level box membership) is invariant under the annotation
    presentation. -/
theorem Fits_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (a : Assignment) :
    a.Fits (annotDomains p orders) ↔ a.Fits p.domains := by
  unfold annotDomains
  rw [LcgHeur.Fits_reorderAuxWith (annotDomains_perm p orders)
    (annotDomains_nil orders) 0 (LcgHeur.heurDomains p) a]
  exact LcgHeur.Fits_reorderAux 0 p.domains a

/-- `SlotOK` transfers along the annotation presentation. -/
theorem SlotOK_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (i : Nat)
    (h : SlotOK (LcgHeur.heurDomains p) i) :
    SlotOK (annotDomains p orders) i :=
  LcgHeur.SlotOK_reorderAuxWith (annotDomains_perm p orders) 0
    (LcgHeur.heurDomains p) i h

/-- The executable source gate transfers along the annotation presentation. -/
theorem gateOk_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (h : gateOk (LcgHeur.heurProblem p) = true) :
    gateOk { lcgProblem p with domains := annotDomains p orders } = true := by
  unfold annotDomains
  change gateOk { LcgHeur.heurProblem p with
      domains := LcgHeur.reorderAuxWith (annotOrder orders) 0
        (LcgHeur.heurProblem p).domains } = true
  exact LcgHeur.gateOk_reorderAuxWith (annotDomains_perm p orders) 0 h

/-- The pruning kit gate transfers along the annotation presentation. -/
theorem domPruningOkB_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (h : domPruningOkB (LcgHeur.heurProblem p) = true) :
    domPruningOkB { lcgProblem p with domains := annotDomains p orders }
      = true := by
  unfold annotDomains
  change domPruningOkB { LcgHeur.heurProblem p with
      domains := LcgHeur.reorderAuxWith (annotOrder orders) 0
        (LcgHeur.heurProblem p).domains } = true
  exact LcgHeur.domPruningOkB_reorderAuxWith (annotDomains_perm p orders) 0 h

/-- The mixed kit gate transfers along the annotation presentation. -/
theorem mixedKitGateB_annot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (h : mixedKitGateB (LcgHeur.heurProblem p) = true) :
    mixedKitGateB { lcgProblem p with domains := annotDomains p orders }
      = true := by
  unfold annotDomains
  change mixedKitGateB { LcgHeur.heurProblem p with
      domains := LcgHeur.reorderAuxWith (annotOrder orders) 0
        (LcgHeur.heurProblem p).domains } = true
  exact LcgHeur.mixedKitGateB_reorderAuxWith (annotDomains_perm p orders) 0 h

/-! ## §6 The annotated route and its certified transfer

The route mirrors the activity-ordered route of `LcgHeur` §4 exactly, with
`annotDomains p orders` in place of `heurDomains p` and `annotProps` in
place of `heurProps`.  Every obligation is discharged by the §5 transfer
lemmas, so the public SAT/UNSAT/totality statements are stated at the
compiled problem AS GIVEN. -/

/-- The clamped propagator list at the annotation-ordered box. -/
def annotProps (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) : List Propagator :=
  clampProps (annotDomains p orders) (p.constraints.filterMap propagatorOfProved)

/-- `fitsB` at the annotation-ordered problem is the compiled problem's
`fitsB`. -/
theorem fitsB_annotProblem (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) (a : Assignment) :
    fitsB { lcgProblem p with domains := annotDomains p orders } a
      = fitsB (lcgProblem p) a :=
  fitsB_annot p orders a

/-- The compiled leaf is unchanged by the annotation presentation. -/
theorem annotLeaf_eq (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder) :
    lcgLeaf p = chronologicalLeaf
      { lcgProblem p with domains := annotDomains p orders }
      DomConstraint.satisfiedB := by
  funext a
  simp only [lcgLeaf, chronologicalLeaf]
  rw [fitsB_annot p orders a]

/-- The source gate at the activity-ordered problem, from the compiled
gate. -/
theorem gateOk_heur {p : CompiledProblem DomConstraint}
    (h : gateOk (lcgProblem p) = true) :
    gateOk (LcgHeur.heurProblem p) = true :=
  LcgHeur.gateOk_reorderAux 0 (problem := lcgProblem p) h

/-- The pruning gate at the activity-ordered problem, from the compiled
gate. -/
theorem domPruningOkB_heur {p : CompiledProblem DomConstraint}
    (h : domPruningOkB (lcgProblem p) = true) :
    domPruningOkB (LcgHeur.heurProblem p) = true :=
  LcgHeur.domPruningOkB_reorderAux 0 (problem := lcgProblem p) h

/-- The slot gate at the activity-ordered problem, from the compiled
gate. -/
theorem SlotOK_heur {p : CompiledProblem DomConstraint} (s : Nat)
    (h : SlotOK (lcgProblem p).domains s) :
    SlotOK (LcgHeur.heurDomains p) s :=
  LcgHeur.SlotOK_reorderAux 0 (lcgProblem p).domains s h

/-- The mixed kit gate at the activity-ordered problem, from the compiled
gate. -/
theorem mixedKitGateB_heur {p : CompiledProblem DomConstraint}
    (h : mixedKitGateB (lcgProblem p) = true) :
    mixedKitGateB (LcgHeur.heurProblem p) = true :=
  LcgHeur.mixedKitGateB_reorderAux 0 (problem := lcgProblem p) h

/-- The compiled input gate transfers to the annotation-ordered box. -/
theorem annotCompiledInput {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder}
    (h : lcgRouteGateMixed p = true) :
    CompiledInput (lcgLeaf p)
      { lcgProblem p with domains := annotDomains p orders } := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true] at h
  exact ⟨annotLeaf_eq p orders,
    gateOk_annot p orders (gateOk_heur h.1.1),
    domPruningOkB_annot p orders (domPruningOkB_heur h.1.2)⟩

/-- The mixed kit gate transfers to the annotation-ordered box. -/
theorem annotGate {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder}
    (h : lcgRouteGateMixed p = true) :
    mixedKitGateB { lcgProblem p with domains := annotDomains p orders }
      = true := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq] at h
  exact mixedKitGateB_annot p orders (mixedKitGateB_heur h.2)

/-- The seed database stays pool-aligned at the annotation-ordered box. -/
theorem annotAligned {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder}
    (h : lcgRouteGateMixed p = true) :
    DatabaseAligned (annotDomains p orders) (seedClauses p.constraints) := by
  have hslot := slots_of_mixedGate (lcgInputMixed h)
    (by simp only [lcgRouteGateMixed, Bool.and_eq_true,
      LcgMixedCompiledKit.mixedKitGateFastB_eq] at h; exact h.2)
  refine seedClauses_aligned_of_slotOK fun dc hdc s hs => ?_
  exact SlotOK_annot p orders s (SlotOK_heur s (hslot dc hdc s hs))

/-- **THE ANNOTATION-ORDERED MIXED KIT**: every kit obligation at the
annotation-ordered box is derived from the same gates. -/
theorem annotKit {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder}
    (h : lcgRouteGateMixed p = true) :
    MixedLcgKit (lcgLeaf p) (annotDomains p orders)
      (seedClauses p.constraints) p.constraints
      (p.constraints.filterMap propagatorOfProved) (annotProps p orders) :=
  kit_of_compiled_mixed (annotCompiledInput h) (annotGate h)
    (lcgSeedCanonical p) (annotAligned h)

/-- The route gate supplies the sparse frame gate at the annotation-ordered
box. -/
theorem annotFrameGate {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder}
    (h : lcgRouteGateMixed p = true) :
    ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg := by
  intro cfg hreach
  exact LeanFzn.Solver.UIP.FrameLive.frameNonempty_of_gateOk
    (problem := { lcgProblem p with domains := annotDomains p orders })
    (annotCompiledInput h).gate (by rfl) hreach

/-- **THE ANNOTATION-ORDERED SCHEDULED RUN**: the certified scheduled LCG
entry on the annotation-ordered presentation of the compiled problem. -/
def lcgRunAnnot (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) :=
  solve_sched (annotDomains p orders) (seedClauses p.constraints)
    (annotProps p orders) (lcgSeedEntailed p)
    (PropScheduler.init (annotProps p orders))
    (clampProps_local (annotDomains p orders) p.constraints)
    (PropSchedulerOK.init (annotProps p orders)) hgate prio actBump

/-- The annotation-ordered run is the certified kernel at the
annotation-ordered box. -/
theorem lcgRunAnnot_eq_solve (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    lcgRunAnnot p orders hgate prio actBump =
      LcgPhaseKernel.solve (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) (lcgSeedEntailed p) hgate prio actBump :=
  solve_sched_eq _ _ _ _ _ _ _ hgate prio actBump

/-- **SAT SOUNDNESS AT THE ORIGINAL BOX**: the annotation-ordered run reports
a witness that is a genuine solution of the compiled problem as given. -/
theorem lcgRunAnnot_sat {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true) {a : List Value}
    (hrun : lcgRunAnnot p orders (annotFrameGate h) prio actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  have hr := hrun
  rw [lcgRunAnnot_eq_solve p orders (annotFrameGate h) prio actBump] at hr
  have hs := solve_sat_solution_of_kit_mixed (annotKit h) (lcgSeedEntailed p)
    (annotFrameGate h) hr
  have hl := hs.1
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at hl
  refine ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns ?_, hl.2.1⟩
  exact (Fits_annot p orders a).mp hs.2

/-- **UNSAT COMPLETENESS AT THE ORIGINAL BOX**: the annotation-ordered run's
refutation excludes every solution of the compiled problem as given. -/
theorem lcgRunAnnot_unsat {p : CompiledProblem DomConstraint}
    {orders : List AnnValOrder} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true)
    (hrun : lcgRunAnnot p orders (annotFrameGate h) prio actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  have hex : ∀ b, b ∈ allAssigns p.domains → accepts p b = true → False := by
    intro b hb ha
    have hr := hrun
    rw [lcgRunAnnot_eq_solve p orders (annotFrameGate h) prio actBump] at hr
    have hn := solve_unsat_excludes_of_kit_mixed (annotKit h) (lcgSeedEntailed p)
      (annotFrameGate h) hr
    apply hn b
    have hf : Assignment.Fits p.domains b :=
      LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb
    refine ⟨?_, (Fits_annot p orders b).mpr hf⟩
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true]
    exact ⟨fitsB_iff.mpr hf, ha,
      List.all_eq_true.mpr fun c hc =>
        seedClauses_any_satisfiedB (fun dc hdc => List.all_eq_true.mp ha dc hdc) c hc⟩
  intro b hb
  cases ha : accepts p b with
  | false => rfl
  | true => exact False.elim (hex b hb ha)

/-- **TOTALITY**: the annotation-ordered run always reports a verdict. -/
theorem lcgRunAnnot_verdict (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (∃ a, lcgRunAnnot p orders hgate prio actBump = .sat a) ∨
      lcgRunAnnot p orders hgate prio actBump = .unsat := by
  cases h : lcgRunAnnot p orders hgate prio actBump with
  | sat a => exact Or.inl ⟨a, rfl⟩
  | unsat => exact Or.inr rfl

/-! ## §7 The annotated public entry and the configuration dispatch -/

/-- **THE ANNOTATION-ORDERED COMPILED ENTRY**: the same route as
`solveCompiledLcgHeur`, with the LCG branch running on the annotation-ordered
presentation (`lcgRunAnnot`). -/
def solveCompiledAnnot (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (orders : List AnnValOrder := [])
    (actBump : Bool := false) : SearchResult :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunAnnot p orders (annotFrameGate hg) prio actBump with
    | .sat a => .sat a
    | .unsat => .unsat
  else
    LeanFzn.Solver.Chronological.solve (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The annotation-ordered entry reports source solutions. -/
theorem solveCompiledAnnot_sat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {orders : List AnnValOrder} {actBump : Bool}
    {a : List Value} (h : solveCompiledAnnot p prio orders actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledAnnot at h
  split at h
  · rename_i hg
    split at h
    · rename_i hr
      cases h
      exact lcgRunAnnot_sat hg hr
    · cases h
  · have hs := LeanFzn.Solver.Chronological.solve_sat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a) h
    exact ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns hs.1,
      List.all_eq_true.mpr (fun c hc =>
        (DomConstraint.satisfiedB_iff c a).mpr (hs.2 c hc))⟩

/-- The annotation-ordered entry's refutation excludes every source
solution. -/
theorem solveCompiledAnnot_unsat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {orders : List AnnValOrder} {actBump : Bool}
    (h : solveCompiledAnnot p prio orders actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiledAnnot at h
  split at h
  · rename_i hg
    split at h
    · cases h
    · rename_i hr
      exact lcgRunAnnot_unsat hg hr
  · have hn := LeanFzn.Solver.Chronological.solve_pruned_unsat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a)
      (fun c hc _ hsol => seedClauses_satisfiedBy
        (fun dc hdc => hsol.2 dc hdc) c hc) h
    intro b hb
    cases ha : accepts p b with
    | false => rfl
    | true =>
        refine absurd ?_ hn
        exact ⟨b, LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb,
          fun c hc => (DomConstraint.satisfiedB_iff c b).mp
            (List.all_eq_true.mp ha c hc)⟩

/-- The annotation-ordered entry is total: it never reports `unknown`. -/
theorem solveCompiledAnnot_verdict (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (orders : List AnnValOrder := [])
    (actBump : Bool := false) :
    solveCompiledAnnot p prio orders actBump ≠ .unknown := by
  unfold solveCompiledAnnot
  split
  · rename_i hg
    cases lcgRunAnnot p orders (annotFrameGate hg) prio actBump <;> simp
  · exact LeanFzn.Solver.Chronological.solve_total _ _ _ _

/-- The annotation priority vector with the legacy objective-first boost
merged in.  `OBJ_SCORE` is below every annotation group band, so the boost
only orders unannotated slots and never disturbs the `seq_search` group
order. -/
def annotPrioOpts (p : CompiledProblem DomConstraint) (o : SearchConfig) :
    List Nat :=
  let base := annotPrio p.source p.names
  if o.objPrio then
    match LcgHeur.biasSlot? p.constraints with
    | some (s, _) => base.set s (max (base.getD s 0) LcgHeur.OBJ_SCORE)
    | none => base
  else base

/-- **THE CONFIGURATION DISPATCH WITH PHASE**: run the presentation-ordered
route whenever the configuration asks for annotation variables, a value
strategy other than the static activity order, or an annotation value order.
`--val=incumbent` uses `prev` (the last incumbent) for its per-slot phase
orders; every other value strategy ignores it.  The unchanged optioned route
is used exactly when `var != annot` and `val == act`, so the default and the
F2 `--var=annot --val=act` behaviour are preserved. -/
def solveSearchConfigWith (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) : SearchResult :=
  if o.var == .annot || o.val != .act then
    solveCompiledAnnot p
      (if o.var == .annot then annotPrioOpts p o
       else LcgHeur.heurPrio o.toHeurOpts p)
      (configOrders p o prev)
      (o.actBump && o.var != .annot)
  else
    LcgHeur.solveCompiledLcgHeurOpts o.toHeurOpts p

/-- **THE CONFIGURATION DISPATCH**: the satisfaction route has no previous
solution, so phase saving selects its unchanged first-round presentation. -/
def solveSearchConfig (p : CompiledProblem DomConstraint)
    (o : SearchConfig) : SearchResult :=
  solveSearchConfigWith p o none

/-- The default configuration is the unchanged public route. -/
theorem solveSearchConfig_default (p : CompiledProblem DomConstraint) :
    solveSearchConfig p (default : SearchConfig) =
      LcgHeur.solveCompiledLcgHeurOpts (default : LcgHeur.HeurOpts) p := rfl

/-- The phase-aware dispatched entry reports source solutions for every
configuration and every previous incumbent. -/
theorem solveSearchConfigWith_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {a : List Value}
    (h : solveSearchConfigWith p o prev = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveSearchConfigWith at h
  by_cases hc : o.var == .annot || o.val != .act
  · rw [if_pos hc] at h
    exact solveCompiledAnnot_sat h
  · rw [if_neg hc] at h
    exact LcgHeur.solveCompiledLcgHeurOpts_sat h

/-- The phase-aware dispatched entry's refutation excludes every source
solution for every configuration and every previous incumbent. -/
theorem solveSearchConfigWith_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)}
    (h : solveSearchConfigWith p o prev = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveSearchConfigWith at h
  by_cases hc : o.var == .annot || o.val != .act
  · rw [if_pos hc] at h
    exact solveCompiledAnnot_unsat h
  · rw [if_neg hc] at h
    exact LcgHeur.solveCompiledLcgHeurOpts_unsat h

/-- The phase-aware dispatched entry is total for every configuration and
every previous incumbent. -/
theorem solveSearchConfigWith_verdict (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) :
    solveSearchConfigWith p o prev ≠ .unknown := by
  unfold solveSearchConfigWith
  by_cases hc : o.var == .annot || o.val != .act
  · rw [if_pos hc]
    exact solveCompiledAnnot_verdict p _ _ _
  · rw [if_neg hc]
    exact LcgHeur.solveCompiledLcgHeurOpts_verdict o.toHeurOpts p

/-- The dispatched entry reports source solutions for every configuration. -/
theorem solveSearchConfig_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {a : List Value}
    (h : solveSearchConfig p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveSearchConfig at h
  exact solveSearchConfigWith_sat h

/-- The dispatched entry's refutation excludes every source solution for
every configuration. -/
theorem solveSearchConfig_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} (h : solveSearchConfig p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveSearchConfig at h
  exact solveSearchConfigWith_unsat h

/-- The dispatched entry is total for every configuration. -/
theorem solveSearchConfig_verdict (p : CompiledProblem DomConstraint)
    (o : SearchConfig) : solveSearchConfig p o ≠ .unknown := by
  unfold solveSearchConfig
  exact solveSearchConfigWith_verdict p o none

/-! ## §8 Return-beside stats twins (K0)

The `--stats` engine counters. The wrappers return the certified verdict with
the terminal `SearchStats` of the identical run; their first component is
proved equal to the corresponding certified entry (`solveSearchConfigStats_fst`
below is what the IO driver uses), so every printed claim keeps its theorem.
Counters are observations only. -/

/-- Stats twin of `lcgRunAnnot`. -/
def lcgRunAnnotStats (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) × SearchStats :=
  solve_schedStats (annotDomains p orders) (seedClauses p.constraints)
    (annotProps p orders) (lcgSeedEntailed p)
    (PropScheduler.init (annotProps p orders))
    (clampProps_local (annotDomains p orders) p.constraints)
    (PropSchedulerOK.init (annotProps p orders)) hgate prio actBump

/-- The instrumented annotation-ordered run decides exactly `lcgRunAnnot`. -/
theorem lcgRunAnnotStats_fst (p : CompiledProblem DomConstraint)
    (orders : List AnnValOrder)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (annotDomains p orders) (seedClauses p.constraints)
        (annotProps p orders) cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (lcgRunAnnotStats p orders hgate prio actBump).1
      = lcgRunAnnot p orders hgate prio actBump :=
  solve_schedStats_fst _ _ _ _ _ _ _ hgate prio actBump

/-- Stats twin of `solveCompiledAnnot` (gate branch + chronological
fallback). -/
def solveCompiledAnnotStats (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (orders : List AnnValOrder := [])
    (actBump : Bool := false) : SearchResult × SearchStats :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunAnnotStats p orders (annotFrameGate hg) prio actBump with
    | (.sat a, st) => (.sat a, st)
    | (.unsat, st) => (.unsat, st)
  else
    LeanFzn.Solver.Chronological.solveWithStats (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The instrumented annotation-ordered entry decides exactly
`solveCompiledAnnot`. -/
theorem solveCompiledAnnotStats_fst (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (orders : List AnnValOrder := [])
    (actBump : Bool := false) :
    (solveCompiledAnnotStats p prio orders actBump).1
      = solveCompiledAnnot p prio orders actBump := by
  unfold solveCompiledAnnotStats solveCompiledAnnot
  by_cases hg : lcgRouteGateMixed p = true
  · rw [dif_pos hg, dif_pos hg]
    cases h : lcgRunAnnot p orders (annotFrameGate hg) prio actBump with
    | sat a =>
        have hs := lcgRunAnnotStats_fst p orders (annotFrameGate hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunAnnotStats p orders (annotFrameGate hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
    | unsat =>
        have hs := lcgRunAnnotStats_fst p orders (annotFrameGate hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunAnnotStats p orders (annotFrameGate hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
  · rw [dif_neg hg, dif_neg hg]
    rfl

/-- Stats twin of `solveSearchConfigWith`. -/
def solveSearchConfigWithStats (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) : SearchResult × SearchStats :=
  if o.var == .annot || o.val != .act then
    solveCompiledAnnotStats p
      (if o.var == .annot then annotPrioOpts p o
       else LcgHeur.heurPrio o.toHeurOpts p)
      (configOrders p o prev)
      (o.actBump && o.var != .annot)
  else
    LcgHeur.solveCompiledLcgHeurOptsStats o.toHeurOpts p

/-- The instrumented phase-aware dispatch decides exactly
`solveSearchConfigWith` for every configuration and previous incumbent. -/
theorem solveSearchConfigWithStats_fst (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) :
    (solveSearchConfigWithStats p o prev).1 = solveSearchConfigWith p o prev := by
  unfold solveSearchConfigWithStats solveSearchConfigWith
  split
  · rw [solveCompiledAnnotStats_fst p
      (if o.var == .annot then annotPrioOpts p o
       else LcgHeur.heurPrio o.toHeurOpts p)
      (configOrders p o prev) (o.actBump && o.var != .annot)]
  · rw [LcgHeur.solveCompiledLcgHeurOptsStats_fst]

/-- Stats twin of `solveSearchConfig`. -/
def solveSearchConfigStats (p : CompiledProblem DomConstraint)
    (o : SearchConfig) : SearchResult × SearchStats :=
  solveSearchConfigWithStats p o none

/-- The instrumented dispatch decides exactly `solveSearchConfig`. -/
theorem solveSearchConfigStats_fst (p : CompiledProblem DomConstraint)
    (o : SearchConfig) :
    (solveSearchConfigStats p o).1 = solveSearchConfig p o :=
  solveSearchConfigWithStats_fst p o none

end LeanFzn.Integration

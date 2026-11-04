/-
Purpose: finite-domain propagation closure and lazy explanation-clause generation.

  Two representations (M2/M3):
  * the sparse scheduled `BranchFrame` (shared names: `frameState`,
    `frameViewedB`, `frameLiveB`, `productive`, `scanDatabase`,
    `scanPropagators`, `nextPruningEvent`, `propagationClosure`,
    `PropagationContract`; all slot-direct through the sparse
    `filterFrame`);
  * the positional `PrefixFrame` the chronological/reference cone keeps
    (`prefix*` twins, filtered through `prefixFilterFrame`).

Dependencies: FrameFilter narrows branches; ClausePropagation interprets clauses;
PruningTypes provides certified refinement contracts and search statistics.
DAG: frame/clauses -> Pruning -> certified kits -> public solve entry.
-/
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Solver.Propagation.CompactDomain
import LeanFzn.Legacy.Solver.Propagation.CompactDomainBridges
import LeanFzn.Legacy.Solver.Propagation.ClausePropagation
import LeanFzn.Legacy.Solver.Propagation.PruningTypes
import LeanFzn.Solver.Propagation.Propagate
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Sparse event selection (scheduled cone) -/

/-- Domain-only observation: registered family propagators read the current box. -/
def frameState (f : BranchFrame) : State :=
  { domains := Frame.domains f, trail := [], decisionLevel := 0,
    clauses := [], learned := [], queue := [], conflict := none }

def frameViewedB (f : BranchFrame) : Bool :=
  (Frame.domains f).all (fun d => (Dom.enum d).all (fun v => v.intView != none))

/-- Structural twin of `frameViewedB`: the per-domain integer-view test is
    the constructor-tag test `Dom.intViewableB`, which reads no values. -/
def frameViewedBFast (f : BranchFrame) : Bool :=
  (Frame.domains f).all Dom.intViewableB

/-- The structural test equals the enumerating one. -/
theorem frameViewedBFast_eq (f : BranchFrame) :
    frameViewedBFast f = frameViewedB f := by
  unfold frameViewedBFast frameViewedB
  apply List.all_congr rfl
  intro d
  rw [Bool.eq_iff_iff, List.all_eq_true, Dom.intViewableB_iff]
  simp only [Dom.valueIntView_eq_value_intView, bne_iff_ne]

attribute [implemented_by frameViewedBFast] frameViewedB

/-- FRAME LIVENESS (P1 S1′): every remaining domain is nonempty —
equivalently (P1's `exists_frameCovers_iff`) the frame covers some
assignment. Coverless frames admit no leaf solution inside them, so no
PROPAGATION EVENT may be selected there: the deduction path's semantic
obligations (contract `chronology`, `WellFormed` reason chronology) are
only well-posed at live frames. -/
def frameLiveB (f : BranchFrame) : Bool :=
  f.doms.all (fun d => !d.isEmpty)

/-- Only a genuine domain reduction triggers another propagation round. -/
def productive (l : Literal) (f : BranchFrame) : Bool :=
  match filterFrame l f with
  | none => true
  | some g => decide (Frame.mass g < Frame.mass f)

/-! ## Fused productivity test -/

/-- Writing one slot changes the box mass exactly by the written domain's
length change. -/
private theorem mass_set_add_eq {ds : List Domain} {k : Nat} {x : Domain}
    {d : Domain} (hd : ds[k]? = some d) :
    ((ds.set k x).map Dom.length).sum + d.length =
      (ds.map Dom.length).sum + x.length := by
  induction ds generalizing k with
  | nil => simp at hd
  | cons e rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at hd
      have h := ih hd
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- Strict mass decrease of the sparse filter frame is exactly strict
length decrease of the filtered slot's domain. -/
private theorem mass_filterFrame_lt_iff (l : Literal) {f : BranchFrame} {d : Domain}
    (hd : f.doms[l.atom.slot]? = some d) :
    Frame.mass { f with doms := f.doms.set l.atom.slot (d.filter l.valueHolds) } <
        Frame.mass f ↔
      (d.filter l.valueHolds).length < d.length := by
  show ((f.doms.set l.atom.slot (d.filter l.valueHolds)).map Dom.length).sum <
      (f.doms.map Dom.length).sum ↔ _
  have h := mass_set_add_eq (ds := f.doms) (k := l.atom.slot)
    (x := d.filter l.valueHolds) hd
  omega

/-- The enumerating productivity check: slot-direct `filterLit` plus one
length/emptiness test. This is the reference body of `productiveFast`. -/
private def productiveCheckD (l : Literal) (d : Dom) : Bool :=
  let d' := Dom.filterLit l d
  if d'.isEmpty then true else decide (d'.length < d.length)

/-- Dropping a value strictly shortens a list. -/
private theorem length_filter_lt_of_mem_false {α : Type} {p : α → Bool} {l : List α}
    {a : α} (ha : a ∈ l) (hp : p a = false) :
    (l.filter p).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      rw [List.filter_cons]
      split
      · rename_i hpb
        simp only [List.length_cons]
        cases ha with
        | head => rw [hp] at hpb; cases hpb
        | tail _ hb =>
            have := ih hb
            omega
      · rename_i hpb
        simp only [List.length_cons]
        have := List.length_filter_le p bs
        omega

/-- The offset value is enumerated by a canonical `.small false` domain. -/
private theorem int_off_mem_enum_smallFalse {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    Value.int off ∈ Dom.enum (⟨.small false off bits⟩ : Dom) := by
  show Value.int off ∈ (Dom.smallInts off bits).map Value.int
  rw [List.mem_map]
  refine ⟨off, ?_, rfl⟩
  have h := (Dom.mem_smallInts_iff (off := off) (bits := bits) (k := 0)
    (by decide)).mpr (by simpa using h0)
  simpa using h

/-- `filterSmall?` returns `none` on a canonical `.small false` domain only
when the structural filter drops the offset value, so the enumerating
filter is strictly shorter. -/
private theorem filterSmall?_none_filter_lt {off : Int} {bits : UInt64}
    {atom : Atom} {positive : Bool}
    (h0 : bits.toNat.testBit 0 = true)
    (h : Dom.filterSmall? false off bits atom positive = none) :
    (Dom.filter (Literal.valueHolds ⟨atom, positive⟩)
      (⟨.small false off bits⟩ : Dom)).length <
      (⟨.small false off bits⟩ : Dom).length := by
  have hmem := int_off_mem_enum_smallFalse (bits := bits) (off := off) h0
  have hfalse : Literal.valueHolds ⟨atom, positive⟩ (.int off) = false := by
    unfold Dom.filterSmall? at h
    dsimp only at h
    cases atom with
    | boolEq s b =>
        cases positive <;> simp at h
    | intNe s x =>
        cases positive with
        | true =>
            dsimp only at h
            by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
            · rw [if_pos hout] at h
              simp at h
            · rw [if_neg hout] at h
              by_cases hbit : bits.toNat.testBit (x - off).toNat = true
              · rw [if_pos hbit] at h
                by_cases hk0 : (x - off).toNat = 0
                · rw [if_pos hk0] at h
                  have hx : x = off := by
                    have hle : x - off ≤ 0 := Int.toNat_eq_zero.mp hk0
                    have hout' : ¬(x < off ∨ off + 64 ≤ x) := by simpa using hout
                    omega
                  subst hx
                  rw [Dom.valueHolds_intNe_pos]
                  simp
                · rw [if_neg hk0] at h
                  simp at h
              · rw [if_neg hbit] at h
                simp at h
        | false =>
            dsimp only at h
            by_cases hout : decide (x < off ∨ off + 64 ≤ x) = true
            · rw [if_pos hout] at h
              simp at h
            · rw [if_neg hout] at h
              split at h <;> simp at h
    | intLe s u =>
        cases positive with
        | true =>
            dsimp only at h
            by_cases htop : off + 63 ≤ u
            · rw [if_pos htop] at h
              simp at h
            · rw [if_neg htop] at h
              by_cases hbot : u < off
              · rw [if_pos hbot] at h
                simp at h
              · rw [if_neg hbot] at h
                split at h
                · simp at h
                · rename_i hb0
                  split at h
                  · simp at h
                  · rename_i hb0f
                    exfalso
                    have hb0t : (bits &&& Dom.lowBitsMask ((u - off).toNat + 1)).toNat.testBit 0 = true := by
                      have hle : 0 ≤ u - off := by omega
                      have hlt : u - off < 63 := by omega
                      have hnat : (u - off).toNat + 1 ≤ 64 := by
                        have h1 : ((u - off).toNat : Int) = u - off := Int.toNat_of_nonneg hle
                        omega
                      rw [UInt64.toNat_and, Nat.testBit_and, Dom.lowBitsMask_testBit hnat (by decide)]
                      simp [h0]
                    rw [hb0t] at hb0f
                    exact hb0f rfl
        | false =>
            dsimp only at h
            by_cases hbot : u < off
            · rw [if_pos hbot] at h
              simp at h
            · rw [if_neg hbot] at h
              by_cases htop : off + 63 ≤ u
              · rw [if_pos htop] at h
                simp at h
              · rw [if_neg htop] at h
                rw [Dom.valueHolds_intLe_neg]
                apply decide_eq_false
                omega
  have hflt := length_filter_lt_of_mem_false
    (p := Literal.valueHolds ⟨atom, positive⟩) hmem hfalse
  rw [Dom.length_eq_enum (Dom.filter _ _), Dom.enum_filter,
    Dom.length_eq_enum]
  exact hflt

/-- The enumerating check is the certified `productive` on every frame. -/
private theorem productiveCheck_eq (l : Literal) (f : BranchFrame) :
    (match f.doms[l.atom.slot]? with
      | none => false
      | some d => productiveCheckD l d) = productive l f := by
  unfold productive
  rw [← filterFrameFast_eq l f]
  unfold filterFrameFast
  dsimp only
  cases hd : f.doms[l.atom.slot]? with
  | none => simp
  | some d =>
      dsimp only
      unfold productiveCheckD
      dsimp only
      have hlen : Dom.length (Dom.filterLit l d) =
          Dom.length (Dom.filterLitKeep l d) := by
        rw [Dom.length_filterLitKeep_eq, Dom.length_eq_enum, Dom.length_eq_enum,
          Dom.enum_filterLit, Dom.enum_filter]
      have hem : (Dom.filterLit l d).isEmpty =
          (Dom.filterLitKeep l d).isEmpty := by
        apply Bool.eq_iff_iff.mpr
        rw [Dom.isEmpty_eq_true_iff, Dom.isEmpty_eq_true_iff, Dom.enum_filterLit,
          Dom.enum_filterLitKeep]
      rw [hem]
      by_cases he : (Dom.filterLitKeep l d).isEmpty = true
      · rw [if_pos he, if_pos he]
      · rw [if_neg he, if_neg he]
        dsimp only
        rw [decide_eq_decide, hlen]
        have h := mass_set_add_eq (ds := f.doms) (k := l.atom.slot)
          (x := Dom.filterLitKeep l d) (d := d) hd
        show (Dom.filterLitKeep l d).length < d.length ↔
          ((f.doms.set l.atom.slot (Dom.filterLitKeep l d)).map Dom.length).sum <
            (f.doms.map Dom.length).sum
        omega

/-- On a canonical `.small false` domain the structural filter decides the
enumerating check without materialising the filtered list. -/
private theorem productiveProbe_eq_check (l : Literal) {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    (match Dom.filterSmall? false off bits l.atom l.positive with
      | some e => e.isEmpty ||
          decide (e.length < (⟨.small false off bits⟩ : Dom).length)
      | none => true) = productiveCheckD l ⟨.small false off bits⟩ := by
  unfold productiveCheckD
  cases hf : Dom.filterSmall? false off bits l.atom l.positive with
  | some e =>
      have hfl : Dom.filterLit l (⟨.small false off bits⟩ : Dom) = e := by
        unfold Dom.filterLit
        simp only [hf, Option.getD_some]
      rw [hfl]
      by_cases he : e.isEmpty <;> simp [he]
  | none =>
      have hlt := filterSmall?_none_filter_lt h0 hf
      have hfl : Dom.filterLit l (⟨.small false off bits⟩ : Dom) =
          Dom.filter l.valueHolds ⟨.small false off bits⟩ := by
        unfold Dom.filterLit
        simp only [hf, Option.getD_none]
      rw [hfl]
      by_cases he : (Dom.filter l.valueHolds
          (⟨.small false off bits⟩ : Dom)).isEmpty = true
      · rw [if_pos he]
      · rw [if_neg he]
        dsimp only
        exact (decide_eq_true_eq.mpr hlt).symm

/-- Fused twin of `productive`: same result, but instead of building
`filterFrame` and comparing two full `Frame.mass` traversals it checks the
single domain `filterFrame` can change. Slot-direct (M3): out of range is a
no-op (no mass change); an emptied slot is a local exclusion (productive);
otherwise the mass decreases exactly when the filtered domain is shorter.
Canonical `.small false` domains take the structural `filterSmall?` path;
other representations fall back to the enumerating check. -/
def productiveFast (l : Literal) (f : BranchFrame) : Bool :=
  match f.doms[l.atom.slot]? with
  | none => false
  | some d =>
      match d.rep with
      | .small false off bits =>
          if bits.toNat.testBit 0 then
            match Dom.filterSmall? false off bits l.atom l.positive with
            | some e => e.isEmpty || decide (e.length < d.length)
            | none => true
          else productiveCheckD l d
      | _ => productiveCheckD l d

/-- **EQUIVALENCE (productivity)**: the fused test is the certified
`productive` on every literal and frame. -/
theorem productiveFast_eq (l : Literal) (f : BranchFrame) :
    productiveFast l f = productive l f := by
  rw [← productiveCheck_eq l f]
  unfold productiveFast
  cases hd : f.doms[l.atom.slot]? with
  | none => rfl
  | some d =>
      simp only [hd]
      cases d with
      | mk rep =>
          cases rep with
          | small isBool off bits =>
              cases isBool with
              | true => rfl
              | false =>
                  dsimp only
                  by_cases h0 : bits.toNat.testBit 0 = true
                  · rw [if_pos h0]
                    exact productiveProbe_eq_check l h0
                  · rw [if_neg h0]
          | holes lo hi hs => rfl
          | general vs => rfl

attribute [implemented_by productiveFast] productive

inductive PruningEvent where
  | stable
  | conflict (clauses : List Clause)
  | implied (literal : Literal) (clause : Clause) (learnReason fromLearned : Bool)

/-- Clauses are unit relative to the finite domains, not merely syntactic trail pins.
A database clause with no remaining literal is reported as a conflict ON THAT
CLAUSE (R1c conflict routing): the scheduler analyses it instead of excluding
the branch locally. -/
def scanDatabase (original : List Clause) (f : BranchFrame) : List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match clauseRemaining f c with
    | [] => .conflict [c]
    | [l] => if productive l f then .implied l c false (!(original.contains c))
             else scanDatabase original f rest
    | _ => scanDatabase original f rest

/-- Skip repeated deductions that do not remove a value; they cannot loop.

P2b (2026-10-24): a propagator deduction does NOT carry its reason clause into
the global learned database (`learnReason = false`). The reason remains the
trail entry's explanation; the clause is entailed but re-derivable by the
propagator, and storing one fresh clause per propagation step made the
nonogram learned-DB scan the dominant cost. -/
def scanPropagators (f : BranchFrame) : List Propagator → PruningEvent
  | [] => .stable
  | p :: rest =>
    match p.run (frameState f) with
    | .stable => scanPropagators f rest
    | .conflict c => .conflict (if c.isEmpty then [] else [c])
    | .implied l r => if productive l f then .implied l r.clause false false
                      else scanPropagators f rest

/-- P2b policy, deduction form: every propagated implied event asks for no
global learning. The reason clause is still the trail entry's explanation. -/
theorem scanPropagators_implied_learn_false {f : BranchFrame} {props : List Propagator}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : scanPropagators f props = .implied l c lr fl) : lr = false := by
  induction props with
  | nil => simp [scanPropagators] at h
  | cons p rest ih =>
      rw [scanPropagators] at h
      split at h
      · exact ih h
      · simp at h
      · rename_i l₀ r₀
        split at h
        · injection h with _ _ h3 _
          exact h3.symm
        · exact ih h

/-- The next pruning event. IMPLIED events are LIVENESS-GATED (P1 S1′): at
a coverless frame the extended event is `.stable`, because a coverless
frame holds no leaf solution and its semantic deduction obligations are
not well-posed (the `ClosureContract`'s implied-antecedent fields would be
refuted there — kernel witness in the P1 audit). Conflicts are NOT gated
(their obligations are branch-relative/vacuous at coverless frames, and
the conflict route stays the sound dead-branch handler). -/
def nextPruningEvent (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : PruningEvent :=
  match scanDatabase original f db with
  | .stable => if frameViewedB f then scanPropagators f props else .stable
  | .conflict cs => .conflict cs
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then .implied l c learnReason fromLearned else .stable

/-- Saturate a branch. Every recursive call removes a finite-domain value.
Explanations are generated only when needed and shared with later branches.
No timeout or iteration allowance is used. -/
def propagationClosure (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : SparseRefinement :=
  match nextPruningEvent original props f db with
  | .stable => { frame := some f }
  | .conflict cs =>
    let learned := cs.filter (fun c => !(db.contains c))
    { frame := none, learned, stats := { conflicts := 1, learnedClauses := learned.length } }
  | .implied l c learnReason fromLearned =>
    let fresh := learnReason && !(db.contains c)
    let learned := if fresh then [c] else []
    let stats : SearchStats :=
      { propagations := 1
        learnedClauses := if fresh then 1 else 0
        learnedPrunes := if fromLearned then 1 else 0 }
    match filterFrame l f with
    | none => { frame := none, learned, stats := stats.add { conflicts := 1 } }
    | some g =>
      if h : Frame.mass g < Frame.mass f then
        let r := propagationClosure original props g (learned ++ db)
        { frame := r.frame, learned := learned ++ r.learned, stats := stats.add r.stats }
      else { frame := some f, learned, stats }
termination_by Frame.mass f

/-- The semantic interface to registered propagators; no trail chronology is assumed. -/
structure PropagationContract (leaf : Assignment → Bool) (props : List Propagator) : Prop where
  implied : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r →
    ∀ a, leaf a = true → FrameCovers f a → l.eval a = some true
  conflict : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (frameState f) = .conflict c →
    ∀ a, leaf a = true → FrameCovers f a → False
  reason : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r →
    ∀ a, leaf a = true → r.clause.SatisfiedBy a

  /-- A non-empty propagator conflict clause is true at every leaf solution
      that is FAITHFUL to the frame the propagator read (it reads, at every
      slot, an int-viewed value of the sort of the slot's current domain
      values). The premise is what the explained `neSlot`/`allDiff` clauses
      need (a mixed-sort raw/view collision is the only way the raw
      disequality can hold while the clause's view-literals are false); every
      consumer discharges it from `frameFaithful_of_domSub` at a frame that is
      a sub-box of a shape-typed int-viewed box all leaf solutions fit. -/
  conflictReason : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (frameState f) = .conflict c → c ≠ [] →
    ∀ a, leaf a = true → FrameFaithful (Frame.domains f) a → c.SatisfiedBy a

/-! ## Positional event selection (chronological/reference cone) -/

/-- Positional variant of `frameState`. -/
def prefixFrameState (f : PrefixFrame) : State :=
  { domains := PrefixFrame.domains f, trail := [], decisionLevel := 0,
    clauses := [], learned := [], queue := [], conflict := none }

def prefixFrameViewedB (f : PrefixFrame) : Bool :=
  (PrefixFrame.domains f).all (fun d => (Dom.enum d).all (fun v => v.intView != none))

/-- Positional variant of `frameLiveB`: every remaining domain is nonempty. -/
def prefixFrameLiveB (f : PrefixFrame) : Bool :=
  f.1.all (fun d => !d.isEmpty)

/-- Positional variant of `productive`. -/
def prefixProductive (l : Literal) (f : PrefixFrame) : Bool :=
  match prefixFilterFrame l f with
  | none => true
  | some g => decide (PrefixFrame.mass g < PrefixFrame.mass f)

/-- Positional variant of `scanDatabase`. -/
def prefixScanDatabase (original : List Clause) (f : PrefixFrame) :
    List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match prefixClauseRemaining f c with
    | [] => .conflict [c]
    | [l] => if prefixProductive l f then .implied l c false (!(original.contains c))
             else prefixScanDatabase original f rest
    | _ => prefixScanDatabase original f rest

/-- Positional variant of `scanPropagators` (same P2b learning policy). -/
def prefixScanPropagators (f : PrefixFrame) : List Propagator → PruningEvent
  | [] => .stable
  | p :: rest =>
    match p.run (prefixFrameState f) with
    | .stable => prefixScanPropagators f rest
    | .conflict c => .conflict (if c.isEmpty then [] else [c])
    | .implied l r => if prefixProductive l f then .implied l r.clause false false
                      else prefixScanPropagators f rest

/-- Positional P2b policy, deduction form. -/
theorem prefixScanPropagators_implied_learn_false {f : PrefixFrame}
    {props : List Propagator} {l : Literal} {c : Clause} {lr fl : Bool}
    (h : prefixScanPropagators f props = .implied l c lr fl) : lr = false := by
  induction props with
  | nil => simp [prefixScanPropagators] at h
  | cons p rest ih =>
      rw [prefixScanPropagators] at h
      split at h
      · exact ih h
      · simp at h
      · rename_i l₀ r₀
        split at h
        · injection h with _ _ h3 _
          exact h3.symm
        · exact ih h

/-- Positional variant of `nextPruningEvent`. -/
def prefixNextPruningEvent (original : List Clause) (props : List Propagator)
    (f : PrefixFrame) (db : List Clause) : PruningEvent :=
  match prefixScanDatabase original f db with
  | .stable => if prefixFrameViewedB f then prefixScanPropagators f props else .stable
  | .conflict cs => .conflict cs
  | .implied l c learnReason fromLearned =>
      if prefixFrameLiveB f then .implied l c learnReason fromLearned else .stable

/-- Positional variant of `propagationClosure`. -/
def prefixPropagationClosure (original : List Clause) (props : List Propagator)
    (f : PrefixFrame) (db : List Clause) : Refinement :=
  match prefixNextPruningEvent original props f db with
  | .stable => { frame := some f }
  | .conflict cs =>
    let learned := cs.filter (fun c => !(db.contains c))
    { frame := none, learned, stats := { conflicts := 1, learnedClauses := learned.length } }
  | .implied l c learnReason fromLearned =>
    let fresh := learnReason && !(db.contains c)
    let learned := if fresh then [c] else []
    let stats : SearchStats :=
      { propagations := 1
        learnedClauses := if fresh then 1 else 0
        learnedPrunes := if fromLearned then 1 else 0 }
    match prefixFilterFrame l f with
    | none => { frame := none, learned, stats := stats.add { conflicts := 1 } }
    | some g =>
      if h : PrefixFrame.mass g < PrefixFrame.mass f then
        let r := prefixPropagationClosure original props g (learned ++ db)
        { frame := r.frame, learned := learned ++ r.learned, stats := stats.add r.stats }
      else { frame := some f, learned, stats }
termination_by PrefixFrame.mass f

/-- Positional variant of `PropagationContract`. -/
structure PrefixPropagationContract (leaf : Assignment → Bool)
    (props : List Propagator) : Prop where
  implied : ∀ f, prefixFrameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (prefixFrameState f) = .implied l r →
    ∀ a, leaf a = true → PrefixCovers f a → l.eval a = some true
  conflict : ∀ f, prefixFrameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (prefixFrameState f) = .conflict c →
    ∀ a, leaf a = true → PrefixCovers f a → False
  reason : ∀ f, prefixFrameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (prefixFrameState f) = .implied l r →
    ∀ a, leaf a = true → r.clause.SatisfiedBy a
  conflictReason : ∀ f, prefixFrameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (prefixFrameState f) = .conflict c → c ≠ [] →
    ∀ a, leaf a = true → FrameFaithful (PrefixFrame.domains f) a → c.SatisfiedBy a

end LeanFzn.Solver.Propagation

/-
File: LeanFzn/Solver/UIP/Proofs/ExtendedPoolRank.lean
and novelty consumers; owner C1)

Purpose: port the remaining `litPool`-keyed C1 consumers to the extended
pool `litPoolWith extra orig` (the unit route instantiates
`extra := constraintAtomPool dcs`, i.e. `litPoolExt orig dcs`):

  * §1 the sorted-pool extension `sortedLitPoolWith` / `canonicalSortedWith`
    / `sortedClausePoolWith` and their membership/normalization facts (the
    `Proofs/SchedulerVocabulary` sorted-pool algebra re-keyed);
  * §2 the order-insensitive CLAUSE-pool extension `clausePoolWith` and the
    `AnalysisPoolAligned` port (`LearningNovelty` §4) —
    `AnalysisPoolAlignedWith` / `hpoolWith_of_alignedWith`;
  * §3 the sorted-shape NOVELTY and RANK consumers (`Proofs/SchedulerJumpProgress`
    §4–§5 re-keyed): `SortedNoveltyWith`, `PhaseRankSortedWith`, the
    canonical-equality falsification transfer, the novelty provider from
    `DatabaseUnfalsified` and the jump's component-1 strict decrease;
  * §4 the sorted-shape arm decreases (`Proofs/SchedulerJumpProgress` §5
    re-keyed) and the well-foundedness of the extended sorted rank.

Every theorem name carries the `With` marker so no rank/novelty consumer
silently remains on `litPool`; the `litPool`-keyed originals are untouched.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.ExtendedPoolRank` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.ExtendedPoolProducers
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerJumpProgress
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P3 (PhaseLt absentCountMap canonicalDBMap statusWeight)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P4 (canonicalDBSorted absentCountSorted PhaseRankSorted
  SortedNovelty)

/-! ## §1 The sorted-pool extension -/

/-- The sorted extended literal pool (`sortedLitPool` at `litPoolWith`). -/
def sortedLitPoolWith (extra : List Atom) (orig : List Domain) : List Literal :=
  (litPoolWith extra orig).mergeSort litSortLe

theorem sortedLitPoolWith_mem {extra : List Atom} {orig : List Domain}
    {l : Literal} :
    l ∈ sortedLitPoolWith extra orig ↔ l ∈ litPoolWith extra orig :=
  List.mem_mergeSort

/-- The landed sorted pool embeds into the extended one. -/
theorem sortedLitPool_mem_sortedLitPoolWith {extra : List Atom}
    {orig : List Domain} {l : Literal} (h : l ∈ sortedLitPool orig) :
    l ∈ sortedLitPoolWith extra orig :=
  sortedLitPoolWith_mem.mpr
    (litPool_mem_litPoolWith (sortedLitPool_mem.mp h))

/-- **THE ORDER-INSENSITIVE CANONICAL CLAUSE AT THE EXTENDED POOL**: the
filter of the sorted extended pool by the (normalized) literals of `c`. -/
def canonicalSortedWith (extra : List Atom) (orig : List Domain)
    (c : Clause) : Clause :=
  (sortedLitPoolWith extra orig).filter fun x => decide (x ∈ c.map Literal.norm)

theorem canonicalSortedWith_sublist (extra : List Atom) (orig : List Domain)
    (c : Clause) :
    (canonicalSortedWith extra orig c).Sublist (sortedLitPoolWith extra orig) :=
  List.filter_sublist

/-- The order-insensitive extended clause pool. -/
def sortedClausePoolWith (extra : List Atom) (orig : List Domain) : List Clause :=
  sublistsOf (sortedLitPoolWith extra orig)

theorem sortedClausePoolWith_mem_iff_sublist {extra : List Atom}
    {orig : List Domain} {c : Clause} :
    c ∈ sortedClausePoolWith extra orig ↔
      c.Sublist (sortedLitPoolWith extra orig) :=
  ⟨sublistsOf_sublist, sublistsOf_mem_of_sublist⟩

theorem canonicalSortedWith_mem_sortedClausePoolWith {extra : List Atom}
    (orig : List Domain) (c : Clause) :
    canonicalSortedWith extra orig c ∈ sortedClausePoolWith extra orig :=
  sublistsOf_mem_of_sublist (canonicalSortedWith_sublist extra orig c)

theorem canonicalSortedWith_congr {extra : List Atom} {orig : List Domain}
    {c d : Clause}
    (h : ∀ l : Literal, l ∈ c.map Literal.norm ↔ l ∈ d.map Literal.norm) :
    canonicalSortedWith extra orig c = canonicalSortedWith extra orig d := by
  apply List.filter_congr
  intro x _
  exact decide_eq_decide.mpr (h x)

theorem norm_mem_canonicalSortedWith {extra : List Atom} {orig : List Domain}
    {c : Clause} {l : Literal} (hc : l ∈ c)
    (hp : l.norm ∈ litPoolWith extra orig) :
    l.norm ∈ canonicalSortedWith extra orig c :=
  List.mem_filter.mpr
    ⟨sortedLitPoolWith_mem.mpr hp, by
      simp only [decide_eq_true_eq]
      exact List.mem_map_of_mem (f := Literal.norm) hc⟩

/-- The consumable backward direction at the extended pool: every
literal-normalized clause is in the extended order-insensitive pool. -/
theorem sortedClausePoolWith_mem_of_forall_norm_mem {extra : List Atom}
    {orig : List Domain} {c : Clause}
    (_h : ∀ l ∈ c, l.norm ∈ litPoolWith extra orig) :
    canonicalSortedWith extra orig c ∈ sortedClausePoolWith extra orig :=
  canonicalSortedWith_mem_sortedClausePoolWith orig c

/-- The landed sorted canonical form IS the extended one at
`extra := []`-shaped pools: the `litPool`-keyed and extended keys agree on
the ORIGINAL pool (definitional bridge used by the monotone consumers). -/
theorem canonicalSortedWith_nil_extras (orig : List Domain) (c : Clause) :
    canonicalSortedWith [] orig c = canonicalSorted orig c := by
  simp [canonicalSortedWith, canonicalSorted, sortedLitPoolWith, sortedLitPool,
    litPoolWith_nil]

/-! ## §2 The clause-pool extension and the `AnalysisPoolAligned` port -/

/-- The extended clause pool (`clausePool` at `litPoolWith`). -/
def clausePoolWith (extra : List Atom) (orig : List Domain) : List Clause :=
  sublistsOf (litPoolWith extra orig)

theorem clausePoolWith_length (extra : List Atom) (orig : List Domain) :
    (clausePoolWith extra orig).length = 2 ^ (litPoolWith extra orig).length :=
  sublistsOf_length _

theorem clausePoolWith_lits_mem {extra : List Atom} {orig : List Domain}
    {c : Clause} (h : c ∈ clausePoolWith extra orig) :
    ∀ l ∈ c, l ∈ litPoolWith extra orig :=
  sublistsOf_subset_mem h

/-- The extended pool-closure shape of P4's `hpool`: a canonical form that
is an order-preserving sublist of the extended pool is an extended
clause-pool member. -/
theorem canonicalClause_mem_clausePoolWith_of_sublist {extra : List Atom}
    {orig : List Domain} {c : Clause}
    (h : List.Sublist (Clause.canonicalClause c) (litPoolWith extra orig)) :
    Clause.canonicalClause c ∈ clausePoolWith extra orig :=
  sublistsOf_mem_of_sublist h

/-- `Sublist (litPool orig) (litPoolWith extra orig)` (the monotone bridge
behind every extended-pool embedding). -/
theorem litPool_sublist_litPoolWith {extra : List Atom} {orig : List Domain} :
    (litPool orig).Sublist (litPoolWith extra orig) := by
  rw [litPool, litPoolWith, atomPoolWith, atomExtras]
  repeat' apply List.Sublist.append
  all_goals
    apply List.Sublist.map
    exact List.sublist_append_left _ _

/-- The base clause pool embeds into the extended clause pool. -/
theorem clausePool_mem_clausePoolWith {extra : List Atom} {orig : List Domain}
    {c : Clause} (h : c ∈ clausePool orig) : c ∈ clausePoolWith extra orig :=
  sublistsOf_mem_of_sublist
    ((sublistsOf_sublist h).trans litPool_sublist_litPoolWith)

/-- **THE EXTENDED `AnalysisPoolAligned`** (`LearningNovelty` §4 re-keyed):
the canonical clause is an order-preserving sublist of the extended pool —
the exact `hpool` shape at `litPoolExt`. -/
def AnalysisPoolAlignedWith (extra : List Atom) (orig : List Domain)
    (an : ConflictAnalysis) : Prop :=
  List.Sublist (Clause.canonicalClause an.learned) (litPoolWith extra orig)

/-- The extended residual, when supplied, yields the extended `hpool`
premise verbatim. -/
theorem hpoolWith_of_alignedWith {extra : List Atom} {orig : List Domain}
    {an : ConflictAnalysis} (h : AnalysisPoolAlignedWith extra orig an) :
    Clause.canonicalClause an.learned ∈ clausePoolWith extra orig :=
  canonicalClause_mem_clausePoolWith_of_sublist h

/-- The landed `AnalysisPoolAligned` transports to every extended pool. -/
theorem analysisPoolAlignedWith_of_aligned {extra : List Atom}
    {orig : List Domain} {an : ConflictAnalysis}
    (h : AnalysisPoolAligned orig an) :
    AnalysisPoolAlignedWith extra orig an :=
  h.trans litPool_sublist_litPoolWith

/-- The landed `hpool_of_aligned` conclusion at the extended pool. -/
theorem hpoolWith_of_aligned {extra : List Atom} {orig : List Domain}
    {an : ConflictAnalysis} (h : AnalysisPoolAligned orig an) :
    Clause.canonicalClause an.learned ∈ clausePoolWith extra orig :=
  hpoolWith_of_alignedWith (analysisPoolAlignedWith_of_aligned h)

/-! ## §3 The sorted-shape novelty and rank consumers at the extended pool -/

/-- Sorted-shape canonical database at the extended pool. -/
def canonicalDBSortedWith (extra : List Atom) (orig : List Domain)
    (db : List Clause) : List Clause :=
  canonicalDBMap (canonicalSortedWith extra orig) db

/-- The extended sorted-shape pool countdown. -/
def absentCountSortedWith (extra : List Atom) (orig : List Domain)
    (db : List Clause) : Nat :=
  absentCountMap (canonicalSortedWith extra orig) db
    (sortedClausePoolWith extra orig)

/-- The extended sorted-shape rank tuple: component 1 is the extended
order-insensitive countdown; components 2–4 are P3's. -/
def PhaseRankSortedWith (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Nat × Nat × Nat × Nat :=
  (absentCountSortedWith extra orig cfg.branch.learned,
   frontierWeight cfg.frontier,
   Frame.mass cfg.branch.frame,
   statusWeight cfg.status)

/-- Extended sorted-shape novelty: the extended sorted canonical form of
the recorded learned clause is absent from the extended sorted canonical
database. -/
def SortedNoveltyWith (extra : List Atom) (orig : List Domain)
    (pre : List Clause) (an : ConflictAnalysis) : Prop :=
  canonicalSortedWith extra orig an.learned ∉ canonicalDBSortedWith extra orig pre

/-- THE EXTENDED RANK IS WELL-FOUNDED (an inverse image of `phaseLt_wf`). -/
theorem phaseRankSortedWith_wf {leaf : Assignment → Bool}
    (extra : List Atom) (orig : List Domain) :
    WellFounded (fun a b : SchedulerConfig leaf =>
      PhaseLt (PhaseRankSortedWith extra orig a) (PhaseRankSortedWith extra orig b)) :=
  InvImage.wf (PhaseRankSortedWith extra orig) P3.phaseLt_wf

theorem phaseRankSortedWith_analyzeConflictCounted_stutter
    (extra : List Atom) (orig : List Domain) (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    PhaseRankSortedWith extra orig (stepAnalyzeConflictCounted cfg c learned n)
      = PhaseRankSortedWith extra orig cfg := rfl

/-- **EXTENDED SORTED-CANONICAL EQUALITY TRANSFERS NORM FALSIFICATION**: the
`Proofs/SchedulerJumpProgress` §4 transfer with the extended key (the only
pool-dependent input is the extended alignment of the clause's literals). -/
theorem falsifiedByTrailNorm_of_canonicalSortedWith_eq
    {leaf : Assignment → Bool} {bs : BranchState leaf} {extra : List Atom}
    {orig : List Domain} {c d : Clause}
    (halign : ∀ q ∈ c, q.norm ∈ litPoolWith extra orig)
    (heq : canonicalSortedWith extra orig c = canonicalSortedWith extra orig d)
    (h : FalsifiedByTrailNorm bs d) : FalsifiedByTrailNorm bs c := by
  intro q hq
  have hmem : q.norm ∈ canonicalSortedWith extra orig c :=
    norm_mem_canonicalSortedWith hq (halign q hq)
  rw [heq] at hmem
  have hmem' : q.norm ∈ d.map Literal.norm := by
    simpa using (List.mem_filter.mp hmem).2
  obtain ⟨q', hq', hq'n⟩ := List.mem_map.mp hmem'
  obtain ⟨e, he, helit⟩ := h q' hq'
  refine ⟨e, he, ?_⟩
  rw [helit]
  calc (q'.negate).norm = ((q'.norm).negate).norm :=
        (norm_negate_norm_local q').symm
    _ = ((q.norm).negate).norm := by rw [hq'n]
    _ = (q.negate).norm := norm_negate_norm_local q

/-- **THE EXTENDED SORTED-NOVELTY PROVIDER**: on a branch whose learned
database is unfalsified and whose recorded analysis is trail-falsified, the
extended sorted key of the learned clause is absent from the extended
sorted canonical database — given the extended database-side alignment
(which `halignDB_litPoolExt_of_supportedRun` produces on the unit route). -/
theorem sortedNoveltyWith_of_unfalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {extra : List Atom} {orig : List Domain}
    {an : ConflictAnalysis}
    (halignDB : ∀ c ∈ bs.learned, ∀ q ∈ c, q.norm ∈ litPoolWith extra orig)
    (hdb : DatabaseUnfalsified bs)
    (hfals : FalsifiedByTrailNorm bs an.learned) :
    SortedNoveltyWith extra orig bs.learned an := by
  intro hmem
  obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
  exact hdb c hc
    (falsifiedByTrailNorm_of_canonicalSortedWith_eq (halignDB c hc) hceq hfals)

/-- **EXTENDED SORTED-SHAPE COMPONENT-1 DECREASE, NO POOL PREMISE**: the
extended pool membership is a theorem
(`canonicalSortedWith_mem_sortedClausePoolWith`); the only countdown premise
is extended sorted novelty. -/
theorem absentCountSortedWith_stepLearnBackjumpAssert_lt
    {leaf : Assignment → Bool} {extra : List Atom} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hnov : SortedNoveltyWith extra orig cfg.branch.learned an)
    (hperf : p.perform cfg.branch cfg.orig cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) :
    absentCountSortedWith extra orig
        (stepLearnBackjumpAssert cfg p ev restored).branch.learned
      < absentCountSortedWith extra orig cfg.branch.learned := by
  have hmem : an.learned ∈ restored.learned := by
    have h := perform_learned_mem_own hperf
    rwa [hm.1] at h
  have hmono : ∀ d ∈ cfg.branch.learned,
      d ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned :=
    fun c hc =>
      stepLearnBackjumpAssert_learned_mono
        (restorationKeepsLearned_of_perform_cfg hperf) c hc
  have hnew : canonicalSortedWith extra orig an.learned ∈
      canonicalDBSortedWith extra orig
        (stepLearnBackjumpAssert cfg p ev restored).branch.learned := by
    rw [stepLearnBackjumpAssert_learned_eq]
    exact List.mem_map_of_mem (f := canonicalSortedWith extra orig)
      (List.mem_append.mpr (Or.inr hmem))
  exact P3.absentCountMap_lt_of_mono_mem (f := canonicalSortedWith extra orig)
    hmono (canonicalSortedWith_mem_sortedClausePoolWith orig an.learned)
    hnew hnov

/-- **EXTENDED SORTED-SHAPE JUMP DECREASE** (`PhaseLt` by component 1). -/
theorem phaseLtSortedWith_stepLearnBackjumpAssert
    {leaf : Assignment → Bool} {extra : List Atom} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hnov : SortedNoveltyWith extra orig cfg.branch.learned an)
    (hperf : p.perform cfg.branch cfg.orig cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) :
    PhaseLt (PhaseRankSortedWith extra orig
        (stepLearnBackjumpAssert cfg p ev restored))
      (PhaseRankSortedWith extra orig cfg) :=
  Or.inl (absentCountSortedWith_stepLearnBackjumpAssert_lt hnov hperf hm)

/-! ## §4 The extended sorted-shape arm decreases -/

theorem absentCountSortedWith_propagate_le (extra : List Atom)
    (orig : List Domain) (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    absentCountSortedWith extra orig (stepPropagate cfg d).branch.learned ≤
      absentCountSortedWith extra orig cfg.branch.learned := by
  apply P3.absentCountMap_mono
  intro c hc
  rw [P3.stepPropagate_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

theorem absentCountSortedWith_localExclude_le (extra : List Atom)
    (orig : List Domain) (cfg : SchedulerConfig leaf) (learned : List Clause)
    (r : DeadRegion) :
    absentCountSortedWith extra orig
        (stepLocalExclude cfg learned r).branch.learned ≤
      absentCountSortedWith extra orig cfg.branch.learned := by
  apply P3.absentCountMap_mono
  intro c hc
  rw [P3.stepLocalExclude_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

/-- Extended sorted-shape PROPAGATE decrease (mirror of P4's). -/
theorem phaseRankSortedWith_lt_propagate (extra : List Atom)
    (orig : List Domain) (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    PhaseLt (PhaseRankSortedWith extra orig (stepPropagate cfg d))
      (PhaseRankSortedWith extra orig cfg) := by
  have hrem := absentCountSortedWith_propagate_le extra orig cfg d
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hcost : branchCost d.frame.1 ≤ branchCost cfg.branch.frame.1 :=
      filterFrame_cost_le d.filtered
    have e1 : (PhaseRankSortedWith extra orig (stepPropagate cfg d)).snd =
        (frontierWeight (d.frame :: cfg.pending), Frame.mass d.frame,
          statusWeight (stepPropagate cfg d).status) := by
      simp [PhaseRankSortedWith, SchedulerConfig.frontier, narrowState]
    rw [e1]
    rcases Nat.lt_or_eq_of_le hcost with hclt | hceq
    · exact Or.inl (C3a.frontierWeight_frame_lt hclt cfg.pending)
    · exact Or.inr ⟨C3a.frontierWeight_frame_congr hceq cfg.pending,
        Or.inl d.decreases⟩

/-- Extended sorted-shape CONSUME decrease. -/
theorem phaseRankSortedWith_lt_consume (extra : List Atom)
    (orig : List Domain) {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    PhaseLt (PhaseRankSortedWith extra orig next)
      (PhaseRankSortedWith extra orig cfg) := by
  have hlearn := P3.stepConsume_learned h
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCountSortedWith extra orig next.branch.learned =
      absentCountSortedWith extra orig cfg.branch.learned
    rw [hlearn]
  · obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
    show frontierWeight next.frontier < frontierWeight cfg.frontier
    rw [SchedulerConfig.frontier, SchedulerConfig.frontier, hframe, hpend, hp]
    exact frontierWeight_cons _ _

/-- Extended sorted-shape DECIDE decrease. -/
theorem phaseRankSortedWith_lt_decide (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) (vs : Domain)
    (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, Dom.enum e ≠ []) :
    PhaseLt (PhaseRankSortedWith extra orig (stepDecide cfg k v vs l))
      (PhaseRankSortedWith extra orig cfg) := by
  have hspec := C3a.splitData_frame_eq hsplit
  have hne : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsplit
  have hnew : (stepDecide cfg k v vs l).frontier
      = cfg.branch.frame.pin k v :: cfg.branch.frame.retire k vs :: cfg.pending := by
    simp only [SchedulerConfig.frontier, stepDecide_pending, stepDecide_frame]
  refine Or.inr ⟨rfl, Or.inl ?_⟩
  show frontierWeight (stepDecide cfg k v vs l).frontier < frontierWeight cfg.frontier
  rw [hnew]
  exact DecisionProto.frontierWeight_split_lt
    (DecisionProto.cost_pin_lt hspec hne hall)
    (DecisionProto.cost_retire_lt hspec hall)

/-- Extended sorted-shape DECIDE-SKIP decrease. -/
theorem phaseRankSortedWith_lt_decideSkip (extra : List Atom)
    (orig : List Domain) (cfg : SchedulerConfig leaf) (k : Nat) (v : Value)
    (vs : Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, Dom.enum e ≠ []) :
    PhaseLt (PhaseRankSortedWith extra orig (stepDecideSkip cfg k v))
      (PhaseRankSortedWith extra orig cfg) :=
  Or.inr ⟨rfl, Or.inl (P3.frontierWeight_stepDecideSkip_lt hsplit hall)⟩

/-- Extended sorted-shape FALLBACK-then-consume composite. -/
theorem fallback_then_consume_sortedWith (extra : List Atom)
    (orig : List Domain) {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRankSortedWith extra orig next)
      (PhaseRankSortedWith extra orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := P3.stepConsume_learned h
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepChronologicalFallback cfg r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepChronologicalFallback cfg r).branch.frame
          :: (stepChronologicalFallback cfg r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCountSortedWith extra orig next.branch.learned =
      absentCountSortedWith extra orig cfg.branch.learned
    rw [hlearn, P3.stepChronologicalFallback_learned_eq]
  · show frontierWeight next.frontier < frontierWeight cfg.frontier
    rwa [show frontierWeight (stepChronologicalFallback cfg r).frontier
        = frontierWeight cfg.frontier from rfl] at hwork

/-- Extended sorted-shape localExclude-then-consume composite. -/
theorem localExclude_then_consume_sortedWith (extra : List Atom)
    (orig : List Domain) {cfg next : SchedulerConfig leaf}
    {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRankSortedWith extra orig next)
      (PhaseRankSortedWith extra orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := P3.stepConsume_learned h
  have hrem1 := absentCountSortedWith_localExclude_le extra orig cfg learned r
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepLocalExclude cfg learned r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepLocalExclude cfg learned r).branch.frame
          :: (stepLocalExclude cfg learned r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  rcases Nat.lt_or_eq_of_le hrem1 with hlt | heq
  · refine Or.inl ?_
    show absentCountSortedWith extra orig next.branch.learned
      < absentCountSortedWith extra orig cfg.branch.learned
    rw [hlearn]
    exact hlt
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · show absentCountSortedWith extra orig next.branch.learned =
        absentCountSortedWith extra orig cfg.branch.learned
      rw [hlearn]
      exact heq
    · show frontierWeight next.frontier < frontierWeight cfg.frontier
      rwa [show frontierWeight (stepLocalExclude cfg learned r).frontier
          = frontierWeight cfg.frontier from rfl] at hwork

/-! ## §5 The consistency bridge to the landed keys -/

/-- At `litPoolWith [] orig = litPool orig` the extended sorted key IS the
landed one (so no consumer silently changes key). -/
theorem canonicalSortedWith_nil_eq_sortedLitPool (orig : List Domain) :
    sortedLitPoolWith [] orig = sortedLitPool orig := by
  simp [sortedLitPoolWith, sortedLitPool, litPoolWith_nil]

/-! ## §6 The non-sorted rank at the extended clause pool (P3 port)

P3's `PhaseRank` (`Proofs/SchedulerRank`) reads `clausePool orig` directly.
The extended twin `PhaseRankWith extra orig` reads `clausePoolWith extra
orig` (P3's `absentCount` is already pool-parametric), with the whole P3
§1–§6 decrease suite re-proved verbatim at the extended pool. The
`extra := []` instance is the landed rank (`phaseRankWith_nil_eq`). -/

/-- The extended non-sorted rank: component 1 counts missing
`clausePoolWith` clauses; components 2–4 are P3's. -/
def PhaseRankWith (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Nat × Nat × Nat × Nat :=
  (P3.absentCount cfg.branch.learned (clausePoolWith extra orig),
   frontierWeight cfg.frontier,
   Frame.mass cfg.branch.frame,
   statusWeight cfg.status)

/-- The extended rank is well-founded (an inverse image of `phaseLt_wf`). -/
theorem phaseRankWith_wf {leaf : Assignment → Bool}
    (extra : List Atom) (orig : List Domain) :
    WellFounded (fun a b : SchedulerConfig leaf =>
      PhaseLt (PhaseRankWith extra orig a) (PhaseRankWith extra orig b)) :=
  InvImage.wf (PhaseRankWith extra orig) P3.phaseLt_wf

/-- The extended rank's component 1 is bounded by the extended pool size
(P3's `absentCount_le_length`, pool-parametric). -/
theorem absentCountWith_le_length (extra : List Atom) (orig : List Domain)
    (db : List Clause) :
    P3.absentCount db (clausePoolWith extra orig) ≤
      (clausePoolWith extra orig).length :=
  P3.absentCount_le_length db _

theorem absent_propagate_le_with (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    P3.absentCount (stepPropagate cfg d).branch.learned
        (clausePoolWith extra orig) ≤
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig) := by
  apply P3.absentCount_mono
  intro c hc
  rw [P3.stepPropagate_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

theorem absent_localExclude_le_with (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (learned : List Clause) (r : DeadRegion) :
    P3.absentCount (stepLocalExclude cfg learned r).branch.learned
        (clausePoolWith extra orig) ≤
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig) := by
  apply P3.absentCount_mono
  intro c hc
  rw [P3.stepLocalExclude_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

theorem phaseRankWith_lt_propagate (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    PhaseLt (PhaseRankWith extra orig (stepPropagate cfg d))
      (PhaseRankWith extra orig cfg) := by
  have hrem := absent_propagate_le_with extra orig cfg d
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hcost : branchCost d.frame.1 ≤ branchCost cfg.branch.frame.1 :=
      filterFrame_cost_le d.filtered
    have e1 : (PhaseRankWith extra orig (stepPropagate cfg d)).snd =
        (frontierWeight (d.frame :: cfg.pending), Frame.mass d.frame,
          statusWeight (stepPropagate cfg d).status) := by
      simp [PhaseRankWith, SchedulerConfig.frontier, narrowState]
    rw [e1]
    rcases Nat.lt_or_eq_of_le hcost with hclt | hceq
    · exact Or.inl (C3a.frontierWeight_frame_lt hclt cfg.pending)
    · exact Or.inr ⟨C3a.frontierWeight_frame_congr hceq cfg.pending,
        Or.inl d.decreases⟩

theorem phaseRankWith_lt_decide (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) (vs : Domain)
    (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, Dom.enum e ≠ []) :
    PhaseLt (PhaseRankWith extra orig (stepDecide cfg k v vs l))
      (PhaseRankWith extra orig cfg) := by
  have hspec := C3a.splitData_frame_eq hsplit
  have hne : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsplit
  have hnew : (stepDecide cfg k v vs l).frontier
      = cfg.branch.frame.pin k v :: cfg.branch.frame.retire k vs :: cfg.pending := by
    simp only [SchedulerConfig.frontier, stepDecide_pending, stepDecide_frame]
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show P3.absentCount (stepDecide cfg k v vs l).branch.learned
        (clausePoolWith extra orig) =
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
    rw [stepDecide_learned]
  · show frontierWeight (stepDecide cfg k v vs l).frontier < frontierWeight cfg.frontier
    rw [hnew]
    exact DecisionProto.frontierWeight_split_lt
      (DecisionProto.cost_pin_lt hspec hne hall)
      (DecisionProto.cost_retire_lt hspec hall)

theorem phaseRankWith_lt_decideSkip (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) (vs : Domain)
    (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, Dom.enum e ≠ []) :
    PhaseLt (PhaseRankWith extra orig (stepDecideSkip cfg k v))
      (PhaseRankWith extra orig cfg) :=
  Or.inr ⟨rfl, Or.inl (P3.frontierWeight_stepDecideSkip_lt hsplit hall)⟩

theorem phaseRankWith_lt_consume (extra : List Atom) (orig : List Domain)
    {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    PhaseLt (PhaseRankWith extra orig next) (PhaseRankWith extra orig cfg) := by
  have hlearn := P3.stepConsume_learned h
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show P3.absentCount next.branch.learned (clausePoolWith extra orig) =
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
    rw [hlearn]
  · obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
    show frontierWeight next.frontier < frontierWeight cfg.frontier
    rw [SchedulerConfig.frontier, SchedulerConfig.frontier, hframe, hpend, hp]
    exact frontierWeight_cons _ _

theorem phaseRankWith_lt_localExclude (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (learned : List Clause) (r : DeadRegion)
    (hstatus : cfg.status = .active) :
    PhaseLt (PhaseRankWith extra orig (stepLocalExclude cfg learned r))
      (PhaseRankWith extra orig cfg) := by
  have hrem := absent_localExclude_le_with extra orig cfg learned r
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩⟩
    show statusWeight (stepLocalExclude cfg learned r).status <
      statusWeight cfg.status
    rw [P3.stepLocalExclude_status, hstatus]
    exact P3.statusWeight_dead_lt_active

theorem phaseRankWith_lt_fallback (extra : List Atom) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (r : DeadRegion) (hstatus : cfg.status = .active) :
    PhaseLt (PhaseRankWith extra orig (stepChronologicalFallback cfg r))
      (PhaseRankWith extra orig cfg) := by
  refine Or.inr ⟨?_, Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩⟩
  · show P3.absentCount (stepChronologicalFallback cfg r).branch.learned
        (clausePoolWith extra orig) =
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
    rw [P3.stepChronologicalFallback_learned_eq]
  · show statusWeight (stepChronologicalFallback cfg r).status <
      statusWeight cfg.status
    rw [P3.stepChronologicalFallback_status, hstatus]
    exact P3.statusWeight_dead_lt_active

theorem phaseRankWith_lt_fallback_then_consume (extra : List Atom)
    (orig : List Domain) {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (_hstatus : cfg.status = .active)
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRankWith extra orig next) (PhaseRankWith extra orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := P3.stepConsume_learned h
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepChronologicalFallback cfg r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepChronologicalFallback cfg r).branch.frame
          :: (stepChronologicalFallback cfg r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show P3.absentCount next.branch.learned (clausePoolWith extra orig) =
      P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
    rw [hlearn, P3.stepChronologicalFallback_learned_eq]
  · show frontierWeight next.frontier < frontierWeight cfg.frontier
    rwa [show frontierWeight (stepChronologicalFallback cfg r).frontier
        = frontierWeight cfg.frontier from rfl] at hwork

theorem phaseRankWith_lt_localExclude_then_consume (extra : List Atom)
    (orig : List Domain) {cfg next : SchedulerConfig leaf}
    {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (_hstatus : cfg.status = .active)
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRankWith extra orig next) (PhaseRankWith extra orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := P3.stepConsume_learned h
  have hrem1 := absent_localExclude_le_with extra orig cfg learned r
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepLocalExclude cfg learned r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepLocalExclude cfg learned r).branch.frame
          :: (stepLocalExclude cfg learned r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  rcases Nat.lt_or_eq_of_le hrem1 with hlt | heq
  · refine Or.inl ?_
    show P3.absentCount next.branch.learned (clausePoolWith extra orig)
      < P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
    rw [hlearn]
    exact hlt
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · show P3.absentCount next.branch.learned (clausePoolWith extra orig) =
        P3.absentCount cfg.branch.learned (clausePoolWith extra orig)
      rw [hlearn]
      exact heq
    · show frontierWeight next.frontier < frontierWeight cfg.frontier
      rwa [show frontierWeight (stepLocalExclude cfg learned r).frontier
          = frontierWeight cfg.frontier from rfl] at hwork

theorem phaseRankWith_analyzeConflictCounted_stutter (extra : List Atom)
    (orig : List Domain) (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (n : Nat) :
    PhaseRankWith extra orig (stepAnalyzeConflictCounted cfg c learned n)
      = PhaseRankWith extra orig cfg := rfl

/-- The `extra := []` instance IS P3's landed rank (the extended port does
not change the original key). -/
theorem phaseRankWith_nil_eq (orig : List Domain)
    (cfg : SchedulerConfig leaf) :
    PhaseRankWith [] orig cfg = P3.PhaseRank orig cfg := by
  simp only [PhaseRankWith, P3.PhaseRank, clausePoolWith, clausePool,
    litPoolWith_nil]

end LeanFzn.Solver.UIP

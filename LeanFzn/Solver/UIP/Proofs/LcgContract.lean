/-
File: LeanFzn/Solver/UIP/Proofs/LcgContract.lean
U0: the non-unit (LCG) interface contract, as compiled statements.

Replaces, for the LCG runtime (R1: analysis at 100% of conflict sites):
  * `PropagatorEvidence.recorded` (exact `DomReasonRecorded`) by the SEMANTIC
    antecedent contract: every non-pivot reason literal `q` is falsified by an
    EARLIER trail entry `e` (`impliesP orig e.literal q.negate.norm`) or at the
    root (`litFalseAtRoot orig q`);
  * the `UnitLearned`/`UnitDB` relativization by the run-relative bundle
    `LcgRunInv` (entailed DB, semantic reasons, pool alignment, falsified
    evidence);
  * `SupportedUnitKit`'s fragment by a generic `KitSpec` / `KitFits`.

## Verdict per existing assembly (from reading the files; "indep" = no
## restatement, "restate" = statement mentions the unit fragment)

| assembly | verdict | why |
|---|---|---|
| FreshCoverless / C2c `hsepF` (level separation) | indep in argument, restate in hypotheses | the argument is purely level-based (UIP entry at conflict level vs checkpoint entries <= target, `TrailLevelSeparated`); it uses no unit shape. Only its current discharge `unitKit_backjumpLevel_eq_zero` and the unit-case consume/level-0 sequence are unit-specific. Non-unit: asserting literal is `negate.norm` of a UIP, still a trail literal of the predecessor, so the same separation target `TrailLevelSeparated` is stated over `impliesP`-free normalized equality and stays valid; the proof along runs must use `LcgRunInv.reasons` (semantic) instead of the exact-recorded chain, and must handle LCG weakening (learned literal need not be a trail literal: only its negation is IMPLIED by an earlier entry). The `hfresh` shape `e.literal != asserting.norm` is unaffected. |
| HdeadCkpt `hpre`/checkpoint-region soundness | restate | 16 unit mentions, 12 `hsepF`: the unit gate is used to get the singleton learned shape; replace by `LcgRunInv.entailed` plus `hfresh`. |
| SupportedInstance (`SupportedUnitKit`, 101 unit mentions) | restate | every builder takes `hprops : props = dcs.filterMap propagatorOfProved` with `unitFamilyB`, `UnitKitGate`; fields themselves (hbr, hsnapF, hent, hdeadCkpt, hbc, hnew, hlog, hdeadEv, hconsumeInv, core) are kit-agnostic Props over `SupportedReach`. Generic restatement: `KitSpec`/`KitFits` below; only builders change. |
| restoration / log / consume (SupportedLog(Sites), ConsumeInvariant, ConsumeRun, PendingRun, CheckpointPrefix) | indep | zero unit mentions (ConsumeRun: 4, the unit-gate wrapper only). They speak of frames, trails, regions, `ExhaustionLog.Sound`; soundness of regions follows from coverage of leaf solutions and `LearnedEntailed`. Consume invariant needs `SchedulerInvariant`, whose DB part is `LearnedEntailed` only. |
| ExtendedPool (Rank, Producers) | indep for rank (0 unit mentions); restate for producers | `litPoolExt` is a function of the constraint list; per family the emitted constants must be added (bool/ne/allDiff/int-binary hallClause literals use current-domain bounds and values: bounds `intLe`/`intNe` over slots of the box -> in `litPool orig` modulo bound constants; not in general: hall bounds are domain values, hence in `litPool` of an int slot; add per-family lemma `emitted literal norm in litPoolExt`). `LcgRunInv.align` is the DB-side alignment premise. |
| TrailSlotRange (C2b) | indep | 0 unit mentions; "for ANY registered propagator list". |
| SyncVocabulary (R1d) | indep | 0 unit mentions; syncClause entailed/chron from `leafFits`. |
| `UnitKitGate.no_wipe` | NOT transferable | after R1c a wipe-out is a legitimate conflict source (`terminalResult`), so `wipeoutClause = none` is false for LCG. Replace by `WipeoutOk`: the produced clause is semantically falsified (checked: conflict check (d)) and entailed. |
| `halignDB` / `PoolAligned` (C1, SortedNovelty / ExtendedPool rank) | REFUTED for LCG | checker (f): learned literals such as `x>2` on box `-1..1` come from propagator-computed bounds, outside `litPool orig` and outside the constraint-atom extension. Every pool-ranked termination argument (P3/P4, ExtendedPoolRank) needs a new pool/measure (e.g. closure of bounds under the kit, or a lexicographic measure on domains). Rank files themselves have no unit mentions, only the pool premise is false. |
| `hnov` (SortedNovelty at recorded analysis) | stays a premise (U1e) | `DatabaseUnfalsified` is false at database-conflict sites (R1c); the contract provides `DbSemUnfalsifiedAtDecide` only at decide closure points. |

## Recommendations
U1a: prove `PropSemContract` (reasons AND conflict clauses) per family: unit
via `propagatorEvidence_unit` (exact recorded => semantic by
`semFalsified_of_trail_negate`), bool via `falsifier_pin`, ne/allDiff/int
binary from their explanations, bounds through `impliesP`. U1c: preservation of
`LcgRunInv` per scheduler arm; new arms to check are those that push entries
(propagate / decide / assert / resume): use `TrailSem.snoc`; backjump restore
uses `TrailSem.of_prefix` (checkpoint trail is a prefix). U1d/e: keep `hnov`;
replace `no_wipe` by `WipeoutOk`. C2c: state `hsepF` as `TrailLevelSeparated`
only (kit independent) and discharge along `SupportedReach` using
`LcgRunInv.reasons`.
-/
import LeanFzn.Solver.UIP.Proofs.UnitRunSupported
import LeanFzn.Solver.Propagation.LcgAnalyzer
import LeanFzn.Solver.Propagation.LiteralClamp
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.UIP.LcgContract

variable {leaf : Assignment → Bool}

/-! ## 1. Semantic antecedent contract -/

/-- `q` is semantically falsified by the entries `pre` or at the root. -/
def SemFalsifiedBefore (orig : List Domain) (pre : List TrailEntry) (q : Literal) : Prop :=
  litFalseAtRoot orig q = true ∨ ∃ e ∈ pre, impliesP orig e.literal q.negate.norm = true

/-- Every literal of `c` is semantically falsified by the trail (database /
conflict falsification, no root part). -/
def ClauseSemFalsified (orig : List Domain) (pre : List TrailEntry) (c : Clause) : Prop :=
  ∀ q ∈ c, ∃ e ∈ pre, impliesP orig e.literal q.negate.norm = true

/-- Every literal of `c` is semantically falsified (trail or root). -/
def ClauseSemFalsifiedR (orig : List Domain) (pre : List TrailEntry) (c : Clause) : Prop :=
  ∀ q ∈ c, SemFalsifiedBefore orig pre q

/-- Non-pivot literals of `c` (w.r.t. `l`) are semantically falsified by `pre`. -/
def SemReasonOK (orig : List Domain) (pre : List TrailEntry) (l : Literal)
    (c : Clause) : Prop :=
  l.norm ∈ c ∧ ∀ q ∈ c, litEqB q.norm l.norm = false → SemFalsifiedBefore orig pre q

/-- Per-entry reason contract at position `pre.length`. -/
def EntryReasonOK (orig : List Domain) (pre : List TrailEntry) (e : TrailEntry) : Prop :=
  ∀ r, e.reason = some r → SemReasonOK orig pre e.literal r.clause

/-- The trail satisfies the semantic reason contract (entry `i` justified by
entries `< i` or the root). -/
def TrailSem (orig : List Domain) (trail : List TrailEntry) : Prop :=
  ∀ i e, trail[i]? = some e → EntryReasonOK orig (trail.take i) e

/-- **Per-propagator contract at a branch state**: the implied literal's
reason is semantically justified by the CURRENT trail, and a reported
conflict clause is semantically falsified by it. -/
def PropSemContract (orig : List Domain) (p : Propagator) (bs : BranchState leaf) : Prop :=
  (∀ l r, p.run (frameState bs.frame) = .implied l r →
      SemReasonOK orig bs.trail l r.clause) ∧
  (∀ c, p.run (frameState bs.frame) = .conflict c → ClauseSemFalsifiedR orig bs.trail c)

/-- **Per-run contract**: the propagators satisfy `PropSemContract` at the
branch state of every configuration of the supported run (replaces the
all-`bs` quantified `PropagatorEvidence.recorded`). -/
def RunSemContract (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ∀ p ∈ props, PropSemContract orig p cfg.branch

theorem semFalsifiedBefore_mono {orig : List Domain} {pre post : List TrailEntry}
    {q : Literal} (hsub : ∀ e ∈ pre, e ∈ post) (h : SemFalsifiedBefore orig pre q) :
    SemFalsifiedBefore orig post q := by
  rcases h with h | ⟨e, he, hi⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hsub e he, hi⟩

theorem impliesP_refl (orig : List Domain) (l : Literal) : impliesP orig l l = true := by
  simp [impliesP, impliesBase, litEqB]

/-- The exact (`DomReasonRecorded`-shape, normalized) form implies the semantic one. -/
theorem semFalsified_of_trail_negate {orig : List Domain} {pre : List TrailEntry}
    {q : Literal} {e : TrailEntry} (he : e ∈ pre) (h : e.literal = q.negate.norm) :
    SemFalsifiedBefore orig pre q :=
  Or.inr ⟨e, he, by rw [h]; exact impliesP_refl _ _⟩

theorem semFalsified_of_root {orig : List Domain} {pre : List TrailEntry} {q : Literal}
    (h : litFalseAtRoot orig q = true) : SemFalsifiedBefore orig pre q := Or.inl h

theorem semReasonOK_mono {orig : List Domain} {pre post : List TrailEntry}
    {l : Literal} {c : Clause} (hsub : ∀ e ∈ pre, e ∈ post)
    (h : SemReasonOK orig pre l c) : SemReasonOK orig post l c :=
  ⟨h.1, fun q hq hne => semFalsifiedBefore_mono hsub (h.2 q hq hne)⟩

/-- Appending an entry whose reason is justified by the current trail. -/
theorem TrailSem.snoc {orig : List Domain} {trail : List TrailEntry} {e : TrailEntry}
    (h : TrailSem orig trail) (he : EntryReasonOK orig trail e) :
    TrailSem orig (trail ++ [e]) := by
  intro i e' hi
  by_cases hlt : i < trail.length
  · rw [List.getElem?_append_left hlt] at hi
    have := h i e' hi
    rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)]
  · have hge : trail.length ≤ i := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi
    obtain ⟨k, hk⟩ : ∃ k, i - trail.length = k := ⟨_, rfl⟩
    rw [hk] at hi
    cases k with
    | zero =>
        have hieq : i = trail.length := by omega
        have : e' = e := by simpa using hi.symm
        subst this; subst hieq
        simpa using he
    | succ k => simp at hi

/-- Restoring a trail prefix (backjump) keeps the contract. -/
theorem TrailSem.of_prefix {orig : List Domain} {a b : List TrailEntry}
    (h : TrailSem orig (a ++ b)) : TrailSem orig a := by
  intro i e hi
  have hlt : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
  have h' := h i e (by rw [List.getElem?_append_left hlt]; exact hi)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at h'

theorem TrailSem.nil (orig : List Domain) : TrailSem orig [] := by
  intro i e hi; simp at hi

/-- A decision (no reason) extends the trail. -/
theorem TrailSem.snoc_decision {orig : List Domain} {trail : List TrailEntry}
    {lit : Literal} {lvl : Nat} (h : TrailSem orig trail) :
    TrailSem orig (trail ++ [⟨lit, lvl, none⟩]) :=
  h.snoc (fun r hr => by cases hr)

/-- A propagation extends the trail when the propagator contract holds. -/
theorem TrailSem.snoc_propagated {orig : List Domain} {trail : List TrailEntry}
    {lit : Literal} {lvl : Nat} {r : Reason} (h : TrailSem orig trail)
    (hr : SemReasonOK orig trail lit r.clause) :
    TrailSem orig (trail ++ [⟨lit, lvl, some r⟩]) :=
  h.snoc (fun r' hr' => by
    have : r' = r := by simpa using hr'.symm
    subst this; exact hr)

/-! ## 2. Run-relative learned-DB / evidence bundle -/

/-- No stored learned clause is semantically falsified by the trail. -/
def DbSemUnfalsified {leaf : Assignment → Bool} (orig : List Domain) (bs : BranchState leaf) : Prop :=
  ∀ c ∈ bs.learned, ¬ ClauseSemFalsified orig bs.trail c

/-- The wipe-out clause, when buildable, is a semantically falsified clause
(replaces `UnitKitGate.no_wipe`; entailment is `LearnedEntailed [w]`). -/
def WipeoutOk {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop :=
  ∀ w, wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame = some w →
    ClauseSemFalsifiedR cfg.orig cfg.branch.trail w ∧ LearnedEntailed leaf [w]

/-- DB-side pool alignment (`halignDB`). **REFUTED for UNCLAMPED LCG runs**
(checker (f): e.g. seed 100046 learns `x2 > 2` on the box `-1..1`).
**REPAIRED by U1e**: with the registered propagators clamped
(`clampProps orig raw`, `LiteralClamp.lean`) alignment is a theorem along
supported runs (`ClampedRun.halignDB_of_clampedRun`) and checker (f) has 0
violations. NOT part of `LcgRunInv`; stated here as the statement the checker tests. -/
def PoolAligned {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop :=
  ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool cfg.orig

/-- **THE RUN INVARIANT of the LCG runtime** (run-relative; NOT a global
`ReachableState` property; no pool alignment, see `PoolAligned`). `closure` holds only at decide steps (R1c routes
database-falsified clauses to conflicts; `ClosureRefutation` stays a
counterexample for the unconditional form). -/
structure LcgRunInv (cfg : SchedulerConfig leaf) : Prop where
  entailed : LearnedEntailed leaf cfg.branch.learned
  reasons : TrailSem cfg.orig cfg.branch.trail
  evidence : ∀ ev, cfg.conflict = some ev →
    ClauseSemFalsifiedR cfg.orig cfg.branch.trail ev.clause
  wipe : WipeoutOk cfg
  closure : (∃ n m, schedulerNext cfg = .decide n m) → DbSemUnfalsified cfg.orig cfg.branch

/-! ## 3. Generic kit interface -/

/-- A propagator kit: a family gate, a gate on the (orig, original, props)
triple, and the run invariant it establishes. -/
structure KitSpec where
  Gate : (leaf : Assignment → Bool) → List Domain → List Clause → List Propagator → Prop
  RunInv : (leaf : Assignment → Bool) → SchedulerConfig leaf → Prop

/-- The kit's derived run-level fact (what `SupportedInstance` consumers need):
under the gate, the invariant holds on every supported configuration. -/
def KitFits (K : KitSpec) (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop :=
  K.Gate leaf orig original props →
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      K.RunInv leaf cfg

/-- Kit soundness: the invariant carries the generic LCG bundle. -/
def KitSound (K : KitSpec) : Prop :=
  ∀ (leaf : Assignment → Bool) (cfg : SchedulerConfig leaf),
    K.RunInv leaf cfg → LcgRunInv cfg

/-- The unit kit (the existing assembly). -/
def unitKit : KitSpec where
  Gate leaf orig original props :=
    ∃ dcs : List DomConstraint, props = dcs.filterMap propagatorOfProved ∧
      (∀ dc ∈ dcs, unitFamilyB dc = true) ∧ UnitKitGate (leaf := leaf) orig original props
  RunInv _ cfg := UnitRunInvariant cfg

/-- The unit kit fits the generic interface (cheap instance check). -/
theorem unitKit_fits (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    KitFits unitKit leaf orig original props := by
  rintro ⟨dcs, hprops, hSupp, hgate⟩ cfg h
  exact unitRunInvariant_of_supported hprops hSupp hgate h

/-- Intended LCG kit: unit + Boolean + ne/allDiff + int binary families. The
gate is the family restriction plus the run-semantic contract; its RunInv is
the bundle (soundness is then trivial). Proving `KitFits lcgKit` is U1a+U1c. -/
def lcgKit (famB : DomConstraint → Bool) : KitSpec where
  Gate leaf orig original props :=
    (∃ dcs : List DomConstraint, props = clampProps orig (dcs.filterMap propagatorOfProved) ∧
      ∀ dc ∈ dcs, famB dc = true) ∧ RunSemContract orig original props leaf
  RunInv _ cfg := LcgRunInv cfg

theorem lcgKit_sound (famB : DomConstraint → Bool) : KitSound (lcgKit famB) :=
  fun _ _ h => h

/-- Any fitting sound kit yields the bundle on the supported run. -/
theorem bundle_of_kit {K : KitSpec} (hK : KitSound K) {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hfit : KitFits K leaf orig original props) (hg : K.Gate leaf orig original props)
    {cfg : SchedulerConfig leaf} (h : SupportedReach orig original props cfg) :
    LcgRunInv cfg :=
  hK leaf cfg (hfit hg h)

end LeanFzn.Solver.UIP.LcgContract

/-
File: LeanFzn/Solver/Propagation/EventContract.lean

Purpose (PLAN task E0): the FROZEN dependency/event contract of the scheduled
propagation layer. The watch-projection scheduler
(`ScheduledPropagation.scanPropagatorsSched`) reuses a memorized result while
the *content* of a propagator's watched slots is unchanged; this module
replaces the content-stamp test by an observable-*event* vocabulary and fixes
the obligations a later work queue (PLAN task E1) will consume.

## 1. Observable change vocabulary

`DomainEvent` is a computable `slot + kind` record. The kinds are exactly the
observable changes named by PLAN §6: lower-bound change, upper-bound change,
singleton pin, arbitrary value removal, Boolean pin, and restoration/
replacement. `frameEvents old new` extracts, from the certified domain lists
`Frame.domains old`/`Frame.domains new` (prefix slots included), the list of
events the transition produced:

* `frameEvents_nil_iff` — the list is empty EXACTLY when the two domain lists
  are equal (so no change is ever invisible);
* `frameEvents_complete` — every slot whose domain changed carries at least
  one event at that slot;
* `slotEvents_sound_ne` and the per-kind soundness lemmas pin each emitted
  kind to its semantic meaning.

An event is emitted only when its kind is actually realised; whenever the
change is not a removal of present values that leaves a nonempty domain
(values entered the domain — a restoration/backjump — or the domain became
empty) it always carries `replaced`, and a removal no specific kind describes
(a pure reordering) falls back to `replaced` too. In particular every
extrema-reading run sees either a bound/pin event or a `replaced` event
(`keptB` is the precise guard). Definable events deliberately do NOT mention
the decision level or the trail: the contract is about `BranchFrame`
transitions; a scheduler-level restoration is an ordinary frame transition
here (the `replaced` events of the restored slots, plus `frameEventsTail`'s
replacement events when the slot count changes).

## 2. Subscription API

`PropagatorSubscribes p e` is the CONSERVATIVE subscription: `p` subscribes to
EVERY event kind at any slot of its declared watch footprint, and to every
event (all slots) when `p.watches = []`. This is the same convention the
scheduler uses (`EntryOK` treats the empty footprint as never reusable): a
`watches := []` registration is a scheduling hint, NOT a proof that no input
matters. `PropagatorSubscribesOn ws e` is the same test at an explicit
footprint `ws`, so a later queue can switch to an audited footprint without
changing this API.

## 3. The obligations

* `SkipSound p f g` (LOCAL soundness): if the transition from the reference
  frame `f` (the frame of `p`'s last run) to the current frame `g` produced
  only events `p` does not subscribe to, then re-running `p` at `g` produces
  exactly the recorded result at `f`. There is no separate "productive
  deduction or conflict" clause: the scan evaluates its productivity/liveness
  gates at the CURRENT frame on both sides (`scanPropagators` tests
  `productive l g`), so run equality is literally "nothing the run would
  contribute at `g` is missed".
* `SkipsStable original props f g db` (THE FROZEN LIST OBLIGATION): every
  member of `props` is `SkipSound` between the reference frame and the current
  frame. This is the invariant statement E1's queue carries. The `original`
  and `db` parameters are part of the frozen signature for interface stability
  with the clause layer: clause skipping is the W1 watched index's business
  (`ClauseWatch.scanDatabaseWatchIdx_fst_eq`), not this propagator contract,
  so the body does not mention them.
* `SkipsComplete original props f g db` (EVENTUAL QUIESCENCE/COMPLETENESS):
  on a transition whose events are all unsubscribed by every unit, replaying
  the recorded results at the current frame (`Propagator.replayAt`, a
  propagator whose `run` is the constant recorded result) reproduces the
  certified `nextPruningEvent` at `g` EXACTLY. Discharged from the list
  obligation by `skipsComplete_proof`. The "forever" part (each unit is
  re-run when work remains) is the queue loop's progress argument, E1's
  responsibility.

`runLocalOn_iff_propLocalOne` bridges the scheduled-locality hypothesis
`PropLocalOne` (ScheduledPropagation) to the footprint form `RunLocalOn` used
here; `skipSoundOn_of_runLocal` is the BRIDGE LEMMA: a locality theorem at a
footprint yields the local-soundness obligation at that footprint, via
`watchStamp_eq_of_eventSilent` (event-silence at a footprint implies equal
watch projections).

## 4. Discharged vs open instances

DISCHARGED for the registered propagators (`propagatorOfProved`):

* every family with a declared nonempty footprint — through
  `propagatorOfProved_local` (ScheduledFamilies), by
  `propagatorOfProved_skipSound` and its clamped form
  `propagatorOfProved_clamp_skipSound`; the certified route's actual list
  `clampProps orig (dcs.filterMap propagatorOfProved)` therefore satisfies the
  frozen obligation: `clampProps_skipsStable`;
* every family with `watches := []` — through the conservative default
  (`PropagatorSubscribes` is constantly `true`, so the event premise forces
  `frameEvents f g = []`, hence `Frame.domains f = Frame.domains g`, hence
  equal runs);
* the linear families at the AUDITED footprint
  `is.map (fun i => Atom.intLe i 0)` — through the proved locality layer
  `propLinLe2_propLocal`/`propLinEq2_propLocal`/`propLinNe_propLocal`.
  PLAN P1 WIRED `linEq`'s footprint into its registration
  (`propagatorOfProved`); PLAN P3 wired `linLe` and `linNe`, so all three
  declared-watch defaults consume their locality theorem directly.  The
  refined instances `propLinLe2_clamp_skipSoundOn`,
  `propLinNe_clamp_skipSoundOn` and the registered forms remain available
  for a queue using `PropagatorSubscribesOn (audited footprint)`;
* the reified binary families and the `bool2int` channel at their audited
  footprints (PLAN P3 batch 2) — through `propEqReifSlot_local`,
  `propLeReifSlotB_local`, `propNeReifSlot_local`, `propLinEqReif_local`,
  `propLinNeReif_local`, `propLinLeReif_local` and `propBool2intSlot_local`,
  wired into `propagatorOfProved` and exposed by the refined/registered
  `..._clamp_skipSoundOn` instances;
* the bounds `minSlot`/`maxSlot` families at `[i, j, k]` (P3 batch 4), the
  array-Boolean conjunction `arrayBoolAndSlot` at `k :: is` (P3 batch 5) and
  the variable-table integer element `arrayVarIntElementSlot` at
  `i :: k :: is` (P3 batch 6) and the variable-table Boolean element
  `arrayVarBoolElementSlot` at `i :: k :: is` (P3 batch 7) — through
  `propMin_local`/`propMax_local`/`propArrayBoolAnd_local`/
  `propArrayVarIntElement_local`/`propArrayVarBoolElement_local`, and the
  product family `timesSlot` at `[i, j, k]` (P3 batch 8) and the
  `absSlot`/`divGen`/`modGen` arithmetic families at `[i, k]` and the
  operands' named slots (P3 batch 9) and the n-ary `maxGen`/`minGen`
  families at their operands' named slots plus the result slot (P3 batch 10)
  and the all-slot `minPair`/`maxPair` shapes at `[i, j, k]` together with
  the generic checking propagator `propCheck` at `dcSlotsFull dc` (P3 batch
  11) through `propTimes_local`/`propAbs_local`/`propDiv_local`/
  `propMod_local`/`propMaxGen_local`/`propMinGen_local`/`propCheck_local`,
  wired and exposed by refined/registered `..._clamp_skipSoundOn` instances.

OPEN (documented, precise missing hypothesis): families whose audit identifies
a real footprint but where no `RunLocalOn` is proved yet — the missing
hypothesis is a `PropLocalOne`/`RunLocalOn` at the footprint, proved by
induction over the run's reads like the linear families' `propLin..._local`
chain. `FamilyFootprintClaim p fp` is the frozen schema for such claims.
Instance status (see the audit table below): every registered family now has
a discharged footprint; `allDiff` (footprint `is`, the nonempty slots read by
the watch-local run) joined the list in S3a via
`propAllDiffLCG_domains_local`.

## 5. Audit (per family: can the run's result depend on the event kind?)

`decl` = declared watches in `propagatorOfProved`; `reads` = symbols the run
actually reads. Event kinds: `LB` lowerBound, `UB` upperBound, `SN` singleton,
`VR` valueRemoved, `BP` boolPin, `RP` replaced.

For a family marked `VR: NO` the claim is that a pure `valueRemoved` at a
watched slot cannot change the run: interior removals keep the extrema
(`keptB` changes are bounded by `lowerBound`/`upperBound`), and domain
emptying carries `replaced`, which such families do subscribe to. The refined
subscription for them is `{LB, UB, SN, BP, RP}` at the family's slots; proving
`RunLocalOn` under that subscription (via `FamilyFootprintClaim`) is the open
refinement obligation.

| family / registered arm | run symbol | decl | reads (source) | LB | UB | SN | VR | BP | RP | status |
|---|---|---|---|---|---|---|---|---|---|---|
| leSlot, ltSlot, eqSlot | propLe, propLt, propEq | `[i,j]` | `domMinI`/`domMaxI` of i,j only (both the driver pair and every `narrowHi`/`narrowLo` arm read extrema: Propagate.lean) | yes | yes | yes | NO | yes | yes | conservative DISCHARGED; min/max refinement OPEN |
| neSlot | propNe | `[i,j]` | full list shapes `[x]`/`[y]`, `domSingletonI`, `valueMemB`, `domNeGate` (Propagate.lean) | yes | yes | yes | yes | yes | yes | conservative DISCHARGED; kind-selective refinement INCONCLUSIVE (full-content reads) |
| plusSlot | propPlus | `[i,j,k]` | extrema of i,j,k | yes | yes | yes | NO | yes | yes | as leSlot |
| leConstHi/Lo, ltConstHi/Lo | propLeConstHi etc. | `[i]` | extrema of i (`narrowHi`/`narrowLo`) | yes | yes | yes | NO | yes | yes | conservative DISCHARGED; refinement OPEN |
| constEq | propConstEq | `[i]` | int arm: extrema of i; bool arm: `valueMemB` + `valuesEqB` on the whole domain (Propagate.lean) | yes | yes | yes | yes | yes | yes | mixed; conservative DISCHARGED; refinement is case-dependent and OPEN |
| boolNotSlot/And/Or | propBoolNot/And/Or | `[i,j(,k)]` | `domBoolPin` (length + `valueMemB`), `implyBool` (`valueMemB` + `valuesEqB`) — full content (Fam/Bool.lean) | no direct | no direct | yes | yes | yes | yes | conservative DISCHARGED; refinement OPEN (content comparisons) |
| linLe | propLinLe2 | `is` (P3, wired) | extrema of the constraint's `is` (Fam/Lin.lean) | yes | yes | yes | NO | yes | yes | refined DISCHARGED and WIRED (propLinLe2_propLocal) |
| linEq | propLinEq2 | `is` (P1, wired) | extrema of `is` | yes | yes | yes | NO | yes | yes | refined DISCHARGED and WIRED (propLinEq2_propLocal) |
| linNe | propLinNe | `is` (P3, wired) | single-value-removal over `is` (full membership checks) | yes | yes | yes | yes | yes | yes | refined DISCHARGED and WIRED (propLinNe_propLocal); kind-selective INCONCLUSIVE |
| allDiff | propAllDiffLCG | `is` (P3, wired) | nonempty slots of `is` via `propAllDiff` + `allDiffElimFirst` | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propAllDiffLCG_domains_local) |
| minSlot/maxSlot | propMin/propMax | `[i,j,k]` (P3, wired) | extrema of i,j,k | yes | yes | yes | NO | yes | yes | DISCHARGED and WIRED (propMin_local / propMax_local) |
| timesSlot | propTimes | `[i, j, k]` (P3, wired) | extrema of i,j,k and target membership of the bound updates | yes | yes | yes | NO | yes | yes | DISCHARGED and WIRED (propTimes_local) |
| absSlot/divGen/modGen | propAbs/propDiv/propMod | `[i, k]` / `(o₁.slots ++ o₂.slots ++ r.slots).map ...` (P3, wired) | extrema of the operand/result slots, divisor pin | yes | yes | yes | NO | yes | yes | DISCHARGED and WIRED (propAbs_local / propDiv_local / propMod_local) |
| eqReifSlot/leReifSlot/neReifSlot | propEqReifSlot/propLeReifSlotB/propNeReifSlot | `[i,j,r]` (P3, wired) | pin of r (`domBoolPin`) + delegation to propEq/propLt/propNe on i,j; `leReifSlot`'s unpinned bounds arm reads the operand extrema (Fam/Reif.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propEqReifSlot_local / propLeReifSlotB_local / propNeReifSlot_local) |
| linEqReif/linNeReif | propLinEqReif/propLinNeReif | `r :: is` (P3, wired) | pin of r + `propLinEq2`/`propLinNe` on `is` + `domsIntOnlyB` (Fam/Lin.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propLinEqReif_local / propLinNeReif_local) |
| linLeReif | propLinLeReif | `r :: is` (P3, wired) | pin of r + dual unpinned bounds arm over `is` (Fam/Lin.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propLinLeReif_local) |
| maxGen/minGen | propMaxGen/propMinGen | `(os.flatMap DomIntArg.slots ++ r.slots).map ...` (P3, wired) | operand extrema + result slot | yes | yes | yes | NO | yes | yes | DISCHARGED and WIRED (propMaxGen_local / propMinGen_local) |
| minPair/maxPair slot forms | propMin/propMax | `[i, j, k]` (P3, wired) | extrema of i,j,k | yes | yes | yes | NO | yes | yes | DISCHARGED and WIRED (propMin_local / propMax_local) |
| minPair/maxPair literal operand forms | propCheck | `(dcSlotsFull dc).map ...` (P3, wired) | `dcSlotsFull dc` singleton shapes + `satisfiedB` (Proofs/PropCheck.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propCheck_local) |
| bool2intSlot | propBool2intSlot | `[i,k]` (P3, wired) | source Boolean pin (`domBoolPin`), target views (`firstBadView`/`domMaxI`/`domMinI`), raw `[.int 0]`/`[.int 1]` (`valuesEqB`) and `implyBool` content (Fam/Bool.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propBool2intSlot_local) |
| arrayIntElementSlot | propArrayIntElement | `[i, k]` (P1, wired) | index/target `valuesGet1` table reads (the table `xs` is a compile-time constant, not a footprint slot), raw `[.int v]` singleton checks (`valuesEqB`, `aieEntryEqB`/`aieSupportB`), `firstBadView` content and the `domsIntOnlyB` guard (Fam/Element.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propArrayIntElement_local / propArrayIntElement_propLocal) |
| arrayBoolAndSlot | propArrayBoolAnd | `k :: is` (P3, wired) | input/target Boolean pins (`domBoolPin`), `find?` scans, `domBoolOnlyB` and `implyBool` content (Fam/Bool.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propArrayBoolAnd_local) |
| arrayVarIntElementSlot | propArrayVarIntElement | `i :: k :: is` (P3, wired) | index/target/table entry reads (`avieEntry`, the `valuesGet1` semantics bridge), raw `[.int v]` singleton checks, `firstBadView` content, extrema (`domMaxI`/`domMinI`) and `valueMemB` support checks, plus the `domsIntOnlyB`/`Nodup`/`elem` guards (Fam/VarElement.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propArrayVarIntElement_local) |
| arrayVarBoolElementSlot | propArrayVarBoolElement | `i :: k :: is` (P3, wired) | index reads, table-entry reads (`avieEntry`, the `valuesGet1` semantics bridge), Boolean sub-domain scans (`avbeFirstBad`), `firstBadView` content, `valueMemB` support checks, `domBoolOnlyB`/`domsIntOnlyB`/`Nodup`/`elem` guards (Fam/BoolElement.lean) | yes | yes | yes | yes | yes | yes | DISCHARGED and WIRED (propArrayVarBoolElement_local) |
| boolClauseSlot, boolEq | none | — | no propagator is registered (leaf-enforced; seed clause in the DB) | — | — | — | — | — | — | not scheduled; no contract needed |
| setInSlot, setInReifSlot | none | — | no propagator is registered (leaf-enforced; constant-set shapes are compiled away by the §3.0.2 domain restriction) | — | — | — | — | — | — | not scheduled; no contract needed |
| unregistered families (no `propagatorOfProved` arm) | none | — | full scan re-runs them | — | — | — | — | — | — | no contract needed |

Inconclusive audits are called out explicitly: `neSlot`, the Boolean arm of
`constEq`, the Boolean families (all full-content reads), and `linNe`'s
value-removal arm. For every one of them the conservative subscription is the
safe contract; refining them requires proving that the specific content reads
factor through the emitted kinds.

## 6. How E1 consumes this API (queue shape)

* On a scheduler transition `old → new`, compute `frameEvents old new` and
  enqueue every unit `p` with `PropagatorSubscribes p e = true` for some
  extracted `e`; a unit all of whose events are unsubscribed is skipped, and
  its reference frame is carried in the queue entry.
* The queue's correctness invariant is `SkipsStable original props f g db`
  with `f` the entry's reference frame and `g` the current frame. A queue
  whose entries have DISTINCT reference frames keeps one `SkipSound p f g`
  fact per entry (the per-unit form is exposed); the list form and
  `SkipsComplete` are the uniform-reference-frame packaging used by the
  textbook scheduler loop. The concrete certified list
  `clampProps orig (dcs.filterMap propagatorOfProved)` is discharged by
  `clampProps_skipsStable`; the refined linear option by the
  `..._skipSoundOn` instances together with `PropagatorSubscribesOn` at the
  audited footprint (the declared-watch `PropagatorSubscribes` reuses the
  wired P1 footprints and never the `watches := []` registrations).
* `skipsComplete_proof` is the "stable means no omitted productive work"
  bridge: the list obligation together with the per-unit instances yields
  the exact certified event at the current frame.
* Backjump/restore needs no extra event kind: every slot whose domain differs
  between the reference frame and the restored frame carries `replaced` (or a
  bound/pin event) plus its specific events, so the conservative default
  re-enqueues every unit watching one of those slots; slots whose domains are
  already equal stay silent, which is exactly what the locality instances
  consume.

## DAG

Pruning + Propagate + ScheduledPropagation + ScheduledFamilies (the locality
layer) + Semantics.ValueEquality -> EventContract -> (E1 queue module, future
`SchedulerStep` wiring). This module only reads the scheduler layer; the
reverse dependency is E1's to add.

Frozen API: `DomainEvent`, `DomainEventKind`, `frameEvents`, the
`..._nil_iff`/`..._complete` extraction lemmas, `PropagatorSubscribes`,
`PropagatorSubscribesOn`, `SkipSound`, `SkipSoundOn`, `SkipsStable`,
`SkipsComplete`, `RunLocalOn`, `FamilyFootprintClaim`, `Propagator.replayAt`.
Bridge: `watchStamp_eq_of_eventSilent`, `skipSoundOn_of_runLocal`,
`skipSoundOn_of_footprintClaim`. Discharges: `propagatorOfProved_skipSound`,
`propagatorOfProved_clamp_skipSound`, `clampProps_skipsStable`,
`propLinLe2_clamp_skipSoundOn`/`propLinEq2_clamp_skipSoundOn`/
`propLinNe_clamp_skipSoundOn`, the registered
`propagatorOfProved_linLe/linEq/linNe_clamp_skipSoundOn`, and the P3 batch-2
reified/`bool2int` refined and registered instances; quiescence:
`scanPropagators_replayAt_eq`, `skipsComplete_proof`.
-/
import LeanFzn.Legacy.Solver.Propagation.ScheduledFamilies
open LeanFzn.Semantics LeanFzn.Solver.Core


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering

/- `SkipsStable`'s reference-signature parameters `original`/`db` are part of
the frozen E1 interface (see the docstring there) and are deliberately not
read by the propagator contract. -/
set_option linter.unusedVariables false

/-! ## 1. The observable event vocabulary -/

/-- The KIND of an observable domain change (the slot is carried by
`DomainEvent`). Every constructor is computably decided from a pair of old/new
slot domains; see `slotEventKinds` for the extraction. -/
inductive DomainEventKind where
  /-- The slot's integer minimum rose to `bound`. -/
  | lowerBound (bound : Int)
  /-- The slot's integer maximum fell to `bound`. -/
  | upperBound (bound : Int)
  /-- The slot's domain became the singleton `[value]`. -/
  | singleton (value : Value)
  /-- `value` left the slot's domain (an arbitrary value removal). -/
  | valueRemoved (value : Value)
  /-- The slot's domain became the singleton `[.bool value]`. -/
  | boolPin (value : Bool)
  /-- The slot's domain changed in a way no other kind describes: values
      entered the domain (a restoration/replacement), the domain became
      empty, or the change is a pure reordering. -/
  | replaced
  deriving Repr
/-- An observable change: a slot and the kind of change its domain underwent. -/
structure DomainEvent where
  /-- The slot whose domain changed. -/
  slot : Nat
  /-- What happened to that slot's domain. -/
  kind : DomainEventKind
  deriving Repr

/-! ## 2. The computable extraction -/

/-- The values that left `od` (arbitrary value removals). -/
def removedKinds (od nd : Domain) : List DomainEventKind :=
  (Dom.enum od).filterMap fun v =>
    if valueMemB v (Dom.enum nd) then none else some (.valueRemoved v)

/-- The lower-bound change of `od → nd`, if the minimum rose. -/
def lowerBoundKinds (od nd : Domain) : List DomainEventKind :=
  match domMinI od, domMinI nd with
  | some om, some nm => if om < nm then [.lowerBound nm] else []
  | _, _ => []

/-- The upper-bound change of `od → nd`, if the maximum fell. -/
def upperBoundKinds (od nd : Domain) : List DomainEventKind :=
  match domMaxI od, domMaxI nd with
  | some om, some nm => if nm < om then [.upperBound nm] else []
  | _, _ => []

/-- The pin events of `nd`: a singleton pin, and a Boolean pin when the
singleton is a Boolean. -/
def pinKinds (nd : Domain) : List DomainEventKind :=
  match Dom.enum nd with
  | [v] => .singleton v :: (match v with | .bool b => [.boolPin b] | _ => [])
  | _ => []

/-- All the specific event kinds of an `od → nd` change. -/
def slotEventKinds (od nd : Domain) : List DomainEventKind :=
  removedKinds od nd ++ lowerBoundKinds od nd ++ upperBoundKinds od nd ++ pinKinds nd

/-- The events of one slot change, at slot `s`. -/
def slotEventsSpecific (s : Nat) (od nd : Domain) : List DomainEvent :=
  (slotEventKinds od nd).map fun k => ⟨s, k⟩

/-- `true` when every new value was already present and the new domain is
nonempty: the change is a genuine (possibly reordering) removal, so
extrema-reading runs can only see `lowerBound`/`upperBound`/`singleton`/
`boolPin` changes. `false` means values entered the domain or the domain
became empty — a replacement (`replaced` is emitted). -/
def keptB (od nd : Domain) : Bool :=
  !nd.isEmpty && (Dom.enum nd).all (fun v => valueMemB v (Dom.enum od))

/-- The events of one slot's change `od → nd`. Empty exactly when the two
domains are equal; a change that is not a nonempty removal of present values
(values entered the domain, or the domain became empty) always carries
`⟨s, .replaced⟩`, and a removal no specific kind describes (a pure
reordering) falls back to `⟨s, .replaced⟩` too, so the list is never empty on
a change (`slotEvents_ne_nil_of_valuesEqB_false`). -/
def slotEvents (s : Nat) (od nd : Domain) : List DomainEvent :=
  if Dom.eqB od nd then []
  else
    (if keptB od nd then [] else [⟨s, .replaced⟩]) ++
    (if (slotEventsSpecific s od nd).isEmpty then [⟨s, .replaced⟩]
     else slotEventsSpecific s od nd)

/-- Extra slots present on only one side of a domain-list comparison are
replacement events at their slot. -/
def frameEventsTail (s : Nat) : List Domain → List DomainEvent
  | [] => []
  | _ :: es => ⟨s, .replaced⟩ :: frameEventsTail (s + 1) es

/-- Slot-indexed extraction over the two certified domain lists. -/
def frameEventsAux (s : Nat) : List Domain → List Domain → List DomainEvent
  | [], [] => []
  | [], e :: es => frameEventsTail s (e :: es)
  | d :: ds, [] => frameEventsTail s (d :: ds)
  | d :: ds, e :: es => slotEvents s d e ++ frameEventsAux (s + 1) ds es

/-- The events a frame transition produced, extracted from the certified
domain lists `Frame.domains` (chosen-prefix slots included). -/
def frameEvents (old new : BranchFrame) : List DomainEvent :=
  frameEventsAux 0 (Frame.domains old) (Frame.domains new)

/-! ## 3. Extraction lemmas -/

/-- `valuesEqB` is complete as well as sound. -/
theorem valuesEqB_complete {xs ys : List Value} (h : xs = ys) : valuesEqB xs ys = true := by
  induction xs generalizing ys with
  | nil => subst h; rfl
  | cons x xs ih =>
      cases ys with
      | nil => exact absurd h (by simp)
      | cons y ys =>
          injection h with hxy hxs
          subst hxy
          subst hxs
          simp only [valuesEqB, Bool.and_eq_true]
          exact ⟨LeanFzn.Semantics.Evaluation.value_eqB_iff.mpr rfl, ih rfl⟩

/-- Every emitted event is at the emitting slot. -/
theorem mem_slotEventsSpecific_slot {s : Nat} {od nd : Domain} {e : DomainEvent}
    (h : e ∈ slotEventsSpecific s od nd) : e.slot = s := by
  rcases List.mem_map.mp h with ⟨k, -, hk⟩
  rw [← hk]

/-- Every emitted event is at the emitting slot. -/
theorem mem_slotEvents_slot {s : Nat} {od nd : Domain} {e : DomainEvent}
    (h : e ∈ slotEvents s od nd) : e.slot = s := by
  unfold slotEvents at h
  split at h
  · cases h
  · rcases List.mem_append.mp h with h | h
    · split at h
      · cases h
      · rcases List.mem_singleton.mp h with rfl
        rfl
    · split at h
      · rcases List.mem_singleton.mp h with rfl
        rfl
      · exact mem_slotEventsSpecific_slot h

/-- The extraction of one changed slot is nonempty. -/
theorem slotEvents_ne_nil_of_valuesEqB_false {s : Nat} {od nd : Domain}
    (h : Dom.eqB od nd = false) : slotEvents s od nd ≠ [] := by
  unfold slotEvents
  split
  · rename_i hv
    rw [h] at hv
    exact absurd hv (by simp)
  · have hB : (if (slotEventsSpecific s od nd).isEmpty then [⟨s, .replaced⟩]
        else slotEventsSpecific s od nd) ≠ [] := by
      split
      · intro hnil
        cases hnil
      · rename_i hcond
        intro hnil
        exact hcond (by simp [hnil])
    intro hnil
    exact hB (List.append_eq_nil_iff.mp hnil).2

/-- The extraction of one slot change is empty exactly when the domains are
equal. -/
theorem slotEvents_nil_iff (s : Nat) (od nd : Domain) :
    slotEvents s od nd = [] ↔ od = nd := by
  constructor
  · intro hnil
    by_cases hv : Dom.eqB od nd = true
    · exact Dom.eqB_sound hv
    · exact absurd hnil (slotEvents_ne_nil_of_valuesEqB_false (by simpa using hv))
  · intro heq
    subst heq
    unfold slotEvents
    split
    · rfl
    · rename_i hv
      exact absurd (Dom.eqB_refl od) hv

/-- Soundness of `removedKinds`: a reported removal really left the domain
(and its values are `valueMemB`-absent). -/
theorem removedKinds_sound {od nd : Domain} {v : Value}
    (h : DomainEventKind.valueRemoved v ∈ removedKinds od nd) :
    v ∈ od ∧ valueMemB v (Dom.enum nd) = false := by
  unfold removedKinds at h
  rcases List.mem_filterMap.mp h with ⟨w, hw, hw_eq⟩
  split at hw_eq
  · cases hw_eq
  · rename_i hmem
    cases hw_eq
    exact ⟨(DomainLike.mem_iff _ _).mpr (by simpa [domElems_eq_enum] using hw),
      by simpa using hmem⟩

/-- Soundness of `lowerBoundKinds`: the reported bound is the new minimum. -/
theorem lowerBoundKinds_sound {od nd : Domain} {b : Int}
    (h : DomainEventKind.lowerBound b ∈ lowerBoundKinds od nd) :
    domMinI nd = some b := by
  unfold lowerBoundKinds at h
  split at h
  · rename_i hom hnm
    split at h
    · rw [List.mem_singleton] at h
      cases h
      exact hnm
    · cases h
  · cases h

/-- Soundness of `upperBoundKinds`: the reported bound is the new maximum. -/
theorem upperBoundKinds_sound {od nd : Domain} {b : Int}
    (h : DomainEventKind.upperBound b ∈ upperBoundKinds od nd) :
    domMaxI nd = some b := by
  unfold upperBoundKinds at h
  split at h
  · rename_i hom hnm
    split at h
    · rw [List.mem_singleton] at h
      cases h
      exact hnm
    · cases h
  · cases h

/-- Soundness of `pinKinds`: a singleton pin really pins the domain. -/
theorem pinKinds_singleton {nd : Domain} {v : Value}
    (h : DomainEventKind.singleton v ∈ pinKinds nd) : Dom.enum nd = [v] := by
  cases he : Dom.enum nd with
  | nil => simp [pinKinds, he] at h
  | cons w ws =>
      cases ws with
      | nil =>
          simp only [pinKinds, he] at h
          rcases List.mem_cons.mp h with hh | hh
          · injection hh with hv
            subst hv
            rfl
          · cases w <;> simp_all
      | cons w2 ws => simp [pinKinds, he] at h

/-- Soundness of `pinKinds`: a Boolean pin really pins the domain. -/
theorem pinKinds_boolPin {nd : Domain} {b : Bool}
    (h : DomainEventKind.boolPin b ∈ pinKinds nd) : Dom.enum nd = [.bool b] := by
  cases he : Dom.enum nd with
  | nil => simp [pinKinds, he] at h
  | cons w ws =>
      cases ws with
      | nil =>
          simp only [pinKinds, he] at h
          rcases List.mem_cons.mp h with hh | hh
          · cases hh
          · cases w <;> simp_all
      | cons w2 ws => simp [pinKinds, he] at h

/-- A change with a reported event is a genuine change. -/
theorem slotEvents_sound_ne {s : Nat} {od nd : Domain} {e : DomainEvent}
    (h : e ∈ slotEvents s od nd) : od ≠ nd := by
  intro heq
  subst heq
  unfold slotEvents at h
  split at h
  · cases h
  · rename_i hv
    exact absurd (Dom.eqB_refl od) hv

/-- A changed slot always carries at least one event. -/
theorem slotEvents_ne_nil_of_ne {s : Nat} {od nd : Domain} (h : od ≠ nd) :
    slotEvents s od nd ≠ [] := by
  by_cases hv : Dom.eqB od nd = true
  · exact absurd (Dom.eqB_sound hv) h
  · exact slotEvents_ne_nil_of_valuesEqB_false (by simpa using hv)

/-! ## 4. Frame-level extraction lemmas -/

/-- `frameEventsTail` reports only replacement events. -/
theorem mem_frameEventsTail {s : Nat} {es : List Domain} {e : DomainEvent}
    (h : e ∈ frameEventsTail s es) :
    ∃ i, e = ⟨s + i, .replaced⟩ := by
  induction es generalizing s with
  | nil => cases h
  | cons d ds ih =>
      rw [show frameEventsTail s (d :: ds)
            = ⟨s, .replaced⟩ :: frameEventsTail (s + 1) ds from rfl] at h
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact ⟨0, by simp⟩
      · obtain ⟨i, hi⟩ := ih h
        refine ⟨i + 1, ?_⟩
        rw [hi]
        exact congrArg (fun n => (⟨n, DomainEventKind.replaced⟩ : DomainEvent))
          (by omega)

/-- An exhausted domain list contributes an event at every further slot. -/
theorem frameEventsTail_complete (s : Nat) :
    ∀ (es : List Domain) (i : Nat), es.getD i Dom.empty ≠ Dom.empty →
      ∃ e ∈ frameEventsTail s es, e.slot = s + i := by
  intro es
  induction es generalizing s with
  | nil =>
      intro i h
      exact absurd rfl h
  | cons e es ih =>
      intro i h
      cases i with
      | zero =>
          exact ⟨⟨s, .replaced⟩, by simp [frameEventsTail], by simp⟩
      | succ i =>
          obtain ⟨ev, hm, hs⟩ := ih (s + 1) i (by simpa using h)
          exact ⟨ev, by simp [frameEventsTail, hm], by omega⟩

/-- Slot-indexed completeness: a changed slot contributes an event at it. -/
theorem frameEventsAux_complete (s : Nat) :
    ∀ (ds es : List Domain) (i : Nat), ds.getD i Dom.empty ≠ es.getD i Dom.empty →
      ∃ e ∈ frameEventsAux s ds es, e.slot = s + i := by
  intro ds
  induction ds generalizing s with
  | nil =>
      intro es i h
      cases es with
      | nil => exact absurd rfl h
      | cons e es =>
          refine frameEventsTail_complete s (e :: es) i ?_
          simpa [frameEventsAux] using h.symm
  | cons d ds ih =>
      intro es i h
      cases es with
      | nil =>
          refine frameEventsTail_complete s (d :: ds) i ?_
          simpa [frameEventsAux] using h
      | cons e es =>
          cases i with
          | zero =>
              have hne : d ≠ e := by simpa using h
              have hfalse : Dom.eqB d e = false := by
                cases hv : Dom.eqB d e with
                | false => rfl
                | true => exact absurd (Dom.eqB_sound hv) hne
              obtain ⟨ev, hev⟩ :=
                List.exists_mem_of_ne_nil _ (slotEvents_ne_nil_of_valuesEqB_false hfalse)
              exact ⟨ev, List.mem_append_left _ hev,
                by rw [mem_slotEvents_slot hev]; simp⟩
          | succ i =>
              have h' : ds.getD i Dom.empty ≠ es.getD i Dom.empty := by simpa using h
              obtain ⟨ev, hev, hslot⟩ := ih (s + 1) es i h'
              exact ⟨ev, List.mem_append_right _ hev, by rw [hslot]; omega⟩

/-- Slot-indexed completeness of the frame extraction. -/
theorem frameEvents_complete {f g : BranchFrame} {s : Nat}
    (h : (Frame.domains f).getD s Dom.empty ≠ (Frame.domains g).getD s Dom.empty) :
    ∃ e ∈ frameEvents f g, e.slot = s := by
  obtain ⟨e, he, hslot⟩ := frameEventsAux_complete 0 (Frame.domains f) (Frame.domains g) s h
  exact ⟨e, he, by rw [hslot]; omega⟩

/-- The frame extraction is empty exactly when the two domain lists are
equal: no change is invisible to the contract. -/
theorem frameEventsAux_nil_iff (s : Nat) : ∀ (ds es : List Domain),
    frameEventsAux s ds es = [] ↔ ds = es := by
  intro ds
  induction ds generalizing s with
  | nil =>
      intro es
      cases es with
      | nil => simp [frameEventsAux]
      | cons e es =>
          constructor
          · intro h
            have hne : frameEventsTail s (e :: es) ≠ [] := by simp [frameEventsTail]
            exact absurd (by simpa [frameEventsAux] using h) hne
          · intro h
            cases h
  | cons d ds ih =>
      intro es
      cases es with
      | nil =>
          constructor
          · intro h
            have hne : frameEventsTail s (d :: ds) ≠ [] := by simp [frameEventsTail]
            exact absurd (by simpa [frameEventsAux] using h) hne
          · intro h
            cases h
      | cons e es =>
          simp only [frameEventsAux]
          rw [List.append_eq_nil_iff, slotEvents_nil_iff, ih (s + 1) es]
          constructor
          · rintro ⟨hd, hes⟩
            rw [hd, hes]
          · intro h
            injection h with h1 h2
            exact ⟨h1, h2⟩

/-- **NO INVISIBLE CHANGE**: the frame events are empty exactly when the
certified domain lists agree. -/
theorem frameEvents_nil_iff {f g : BranchFrame} :
    frameEvents f g = [] ↔ Frame.domains f = Frame.domains g :=
  frameEventsAux_nil_iff 0 (Frame.domains f) (Frame.domains g)

/-- The extracted event list determines the changed-slot set: an event-silent
transition cannot change any slot's domain. -/
theorem domain_eq_of_eventSilent {f g : BranchFrame} {s : Nat}
    (h : ∀ e ∈ frameEvents f g, e.slot ≠ s) :
    (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty := by
  by_cases hne : (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty
  · exact hne
  · obtain ⟨e, he, hslot⟩ := frameEvents_complete hne
    exact absurd hslot (h e he)

/-! ## 5. The conservative subscription API -/

/-- The CONSERVATIVE subscription test at an explicit footprint `ws`: `true`
means "a change of this kind at this slot can change the run", so the unit
must be re-run. Every event kind at a footprint slot subscribes; the EMPTY
footprint subscribes to every event at every slot (the conservative default:
a propagator with no declared footprint is never skipped). Kind-selective
refinements are per-family claims (`FamilyFootprintClaim`, audit table in the
header), not part of this default. -/
def PropagatorSubscribesOn (ws : List Atom) (e : DomainEvent) : Bool :=
  ws.isEmpty || ws.any fun a => a.slot == e.slot

/-- The subscription of a propagator at its declared watch footprint. A
`watches := []` registration subscribes to everything: the declaration is a
scheduling decision, never a proof that no input matters. -/
def PropagatorSubscribes (p : Propagator) (e : DomainEvent) : Bool :=
  PropagatorSubscribesOn p.watches e

/-- Inversion of the subscription test: `false` means a nonempty footprint,
none of whose slots the event touches. -/
theorem propagatorSubscribesOn_eq_false_iff {ws : List Atom} {e : DomainEvent} :
    PropagatorSubscribesOn ws e = false ↔ ws ≠ [] ∧ ∀ a ∈ ws, a.slot ≠ e.slot := by
  simp only [PropagatorSubscribesOn, Bool.or_eq_false_iff, List.isEmpty_eq_false_iff,
    List.any_eq_false]
  constructor
  · rintro ⟨hne, hall⟩
    refine ⟨hne, fun a ha => ?_⟩
    have h := hall a ha
    simpa [beq_eq_false_iff_ne] using h
  · rintro ⟨hne, hall⟩
    refine ⟨hne, fun a ha => ?_⟩
    have h := hall a ha
    simpa [beq_eq_false_iff_ne] using h

/-- The declared-footprint form of the inversion. -/
theorem propagatorSubscribes_eq_false_iff {p : Propagator} {e : DomainEvent} :
    PropagatorSubscribes p e = false ↔
      p.watches ≠ [] ∧ ∀ a ∈ p.watches, a.slot ≠ e.slot :=
  propagatorSubscribesOn_eq_false_iff

/-! ## 6. The stability obligations -/

/-- LOCAL SOUNDNESS at an explicit footprint: if the transition from the
reference frame `f` (the frame of the unit's last run) to the current frame
`g` produced only events the footprint does not subscribe to, then re-running
at `g` produces exactly the recorded result at `f`. Because the scan tests
its productivity/liveness gates at the CURRENT frame on both the running and
the replaying side, this equality is exactly "no productive deduction or
conflict the skip would miss". -/
def SkipSoundOn (ws : List Atom) (p : Propagator) (f g : BranchFrame) : Prop :=
  (∀ e ∈ frameEvents f g, PropagatorSubscribesOn ws e = false) →
    p.run (frameState g) = p.run (frameState f)

/-- LOCAL SOUNDNESS of a unit at its declared footprint. -/
def SkipSound (p : Propagator) (f g : BranchFrame) : Prop :=
  SkipSoundOn p.watches p f g

/-- THE FROZEN LIST OBLIGATION: every unit in `props` is `SkipSound` between
the reference frame and the current frame. This is the invariant a work queue
(E1) maintains; `original`/`db` belong to the frozen signature for interface
stability with the clause layer (clause skipping is the W1 watched index's
contract, `ClauseWatch.scanDatabaseWatchIdx_fst_eq`), so the body does not
mention them. -/
def SkipsStable (original : List Clause) (props : List Propagator)
    (f g : BranchFrame) (db : List Clause) : Prop :=
  ∀ p ∈ props, SkipSound p f g

/-- The skip as a propagator: `run` replays the result recorded at the
reference frame `f` (no computation). -/
def Propagator.replayAt (f : BranchFrame) (p : Propagator) : Propagator :=
  { p with run := fun _ => p.run (frameState f) }

/-- EVENTUAL QUIESCENCE/COMPLETENESS: on a transition whose events are all
unsubscribed by every unit, replaying the recorded results at the current
frame reproduces the certified `nextPruningEvent` at that frame EXACTLY — no
productive deduction or conflict is postponed. The "forever" part (a unit
with pending work is re-run) is the queue loop's progress argument, E1's
responsibility; this def fixes the one-frame semantic core. Given the frozen
list obligation it holds for every list: `skipsComplete_proof`. -/
def SkipsComplete (original : List Clause) (props : List Propagator)
    (f g : BranchFrame) (db : List Clause) : Prop :=
  (∀ p ∈ props, ∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false) →
    nextPruningEvent original (props.map (Propagator.replayAt f)) g db
      = nextPruningEvent original props g db

/-! ## 7. The bridge lemma and its instances -/

/-- The footprint form of the scheduled-locality hypothesis shared by the
`scheduled` layer: the run depends only on the current domains of the
footprint's slots. `PropLocalOne p` is `RunLocalOn p.watches p`. -/
def RunLocalOn (ws : List Atom) (p : Propagator) : Prop :=
  ∀ f g : BranchFrame, watchStamp f ws = watchStamp g ws →
    p.run (frameState f) = p.run (frameState g)

/-- The scheduled-locality hypothesis is the declared-footprint instance. -/
theorem runLocalOn_iff_propLocalOne (p : Propagator) :
    RunLocalOn p.watches p ↔ PropLocalOne p := Iff.rfl

/-- Event-silence at a footprint forces equal watch projections: the frame
extraction reports every changed slot (`frameEvents_complete`). -/
theorem watchStamp_eq_of_eventSilent {f g : BranchFrame} {ws : List Atom}
    (h : ∀ e ∈ frameEvents f g, ∀ a ∈ ws, e.slot ≠ a.slot) :
    watchStamp f ws = watchStamp g ws := by
  induction ws with
  | nil => rfl
  | cons a as ih =>
      have ha : (Frame.domains f).getD a.slot Dom.empty = (Frame.domains g).getD a.slot Dom.empty :=
        domain_eq_of_eventSilent fun e he => h e he a (List.mem_cons_self ..)
      simp only [watchStamp, List.map_cons, List.cons.injEq]
      exact ⟨ha, ih fun e he b hb => h e he b (List.mem_cons_of_mem _ hb)⟩

/-- **THE BRIDGE LEMMA**: a locality claim at a footprint yields local
soundness of skipping at that footprint. -/
theorem skipSoundOn_of_runLocal {ws : List Atom} {p : Propagator}
    (hloc : RunLocalOn ws p) {f g : BranchFrame} : SkipSoundOn ws p f g := by
  intro h
  have hstamp : watchStamp f ws = watchStamp g ws :=
    watchStamp_eq_of_eventSilent fun e he a ha =>
      Ne.symm ((propagatorSubscribesOn_eq_false_iff.mp (h e he)).2 a ha)
  exact (hloc f g hstamp).symm

/-- A footprint-less unit subscribes to everything, so the event premise can
only hold on an event-free transition — where the domain lists agree. -/
theorem skipSoundOn_nil {p : Propagator} {f g : BranchFrame} : SkipSoundOn [] p f g := by
  intro h
  have hnil : frameEvents f g = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have hc := h e he
    simp [PropagatorSubscribesOn] at hc
  have hdom : Frame.domains f = Frame.domains g := frameEvents_nil_iff.mp hnil
  have hfs : frameState g = frameState f := by simp only [frameState, hdom]
  rw [hfs]

/-- The general discharge: a unit whose nonempty-footprint locality is proved
(and which is subscribed to everything when the footprint is empty) is
`SkipSound`. -/
theorem skipSound_of_localOrEmpty (p : Propagator)
    (hloc : p.watches ≠ [] → PropLocalOne p) {f g : BranchFrame} :
    SkipSound p f g := by
  by_cases hempty : p.watches = []
  · show SkipSoundOn p.watches p f g
    rw [hempty]
    exact skipSoundOn_nil
  · intro h
    have hloc' : PropLocalOne p := hloc hempty
    have hstamp : watchStamp f p.watches = watchStamp g p.watches :=
      watchStamp_eq_of_eventSilent fun e he a ha =>
        Ne.symm ((propagatorSubscribesOn_eq_false_iff.mp (h e he)).2 a ha)
    exact (hloc' f g hstamp).symm

/-- **DISCHARGED INSTANCE (registered families, declared footprint)**: every
propagator produced by `propagatorOfProved` is `SkipSound`. -/
theorem propagatorOfProved_skipSound {dc : DomConstraint} {p : Propagator}
    (hp : propagatorOfProved dc = some p) {f g : BranchFrame} :
    SkipSound p f g :=
  skipSound_of_localOrEmpty p fun hne => propagatorOfProved_local hp hne

/-- **DISCHARGED INSTANCE (clamped runtime list)**: the certified route's
propagators (`clampProps = map (Propagator.clamp orig)`) inherit the
discharge; `PropLocalOne.clamp` preserves the declared-footprint locality. -/
theorem propagatorOfProved_clamp_skipSound (orig : List Domain) {dc : DomConstraint}
    {p : Propagator} (hp : propagatorOfProved dc = some p) {f g : BranchFrame} :
    SkipSound (p.clamp orig) f g :=
  skipSound_of_localOrEmpty _ fun hne =>
    PropLocalOne.clamp (p := p) (propagatorOfProved_local hp
      (by simpa only [Propagator.clamp] using hne))

/-- **THE CONCRETE LIST INSTANCE**: the actual certified LCG propagator list
`clampProps orig (dcs.filterMap propagatorOfProved)` satisfies the frozen
list obligation for every frame transition. -/
theorem clampProps_skipsStable (orig : List Domain) (dcs : List DomConstraint)
    (original : List Clause) (db : List Clause) {f g : BranchFrame} :
    SkipsStable original (clampProps orig (dcs.filterMap propagatorOfProved)) f g db := by
  intro p hp
  obtain ⟨p0, hp0, hp_eq⟩ := List.mem_map.mp hp
  obtain ⟨_, _, hprop⟩ := propagatorsOfProved_mem hp0
  rw [← hp_eq]
  exact propagatorOfProved_clamp_skipSound orig hprop

/-! ### Refined linear-family instances (audited footprint)

All three linear registrations now declare the audited footprint
`is.map (fun i => Atom.intLe i 0)` (PLAN P1 for `linEq`, PLAN P3 for
`linLe`/`linNe`), so the declared-watch default consumes the locality
theorems `propLinLe2_propLocal`/`propLinEq2_propLocal`/
`propLinNe_propLocal` directly.  These refined instances also let a queue
schedule the runs at that footprint (through `PropagatorSubscribesOn`)
independently of the registration shape. -/

/-- Refined discharge for `linLe`'s run `propLinLe2` at the constraint slots. -/
theorem propLinLe2_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0)
      (({ watches := is.map fun i => Atom.intLe i 0,
          run := fun st => propLinLe2 st coeffs is b } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinLe2_propLocal coeffs is b))

/-- Refined discharge for `linEq`'s run `propLinEq2` at the constraint slots. -/
theorem propLinEq2_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0)
      (({ watches := is.map fun i => Atom.intLe i 0,
          run := fun st => propLinEq2 st coeffs is b } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinEq2_propLocal coeffs is b))

/-- Refined discharge for `linNe`'s run `propLinNe` at the constraint slots. -/
theorem propLinNe_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0)
      (({ watches := is.map fun i => Atom.intLe i 0,
          run := fun st => propLinNe st coeffs is b } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinNe_propLocal coeffs is b))

/-- The registered (unclamped) `linLe` propagator declares exactly its
constraint slots as its footprint (PLAN P3). -/
theorem propagatorOfProved_linLe_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {p : Propagator}
    (hp : propagatorOfProved (.linLe coeffs is b) = some p) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinLe2_propLocal coeffs is b))

/-- The registered (unclamped) `linEq` propagator at its constraint slots. -/
theorem propagatorOfProved_linEq_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {p : Propagator}
    (hp : propagatorOfProved (.linEq coeffs is b) = some p) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinEq2_propLocal coeffs is b))

/-- The registered (unclamped) `linNe` propagator at its constraint slots. -/
theorem propagatorOfProved_linNe_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {p : Propagator}
    (hp : propagatorOfProved (.linNe coeffs is b) = some p) {f g : BranchFrame} :
    SkipSoundOn (is.map fun i => Atom.intLe i 0) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinNe_propLocal coeffs is b))

/-! ### Refined reified-family instances (audited footprint, PLAN P3 batch 2)

The binary reified delegations read the reif pin and both operand domains
(`[i, j, r]`), and the linear equality/disequality delegations read the reif
pin and the constraint slots (`r :: is`).  The `bool2int` channel reads only
its source and target slots (`[i, k]`).  These instances expose the audited
footprints independently of the registrations. -/

/-- Refined discharge for `eqReifSlot`'s run at `[i, j, r]`. -/
theorem propEqReifSlot_clamp_skipSoundOn (orig : List Domain) (i j r : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0],
          run := fun st => propEqReifSlot st i j r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propEqReifSlot_propLocal i j r))

/-- Refined discharge for `leReifSlot`'s strengthened run at `[i, j, r]`. -/
theorem propLeReifSlotB_clamp_skipSoundOn (orig : List Domain) (i j r : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0],
          run := fun st => propLeReifSlotB st i j r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLeReifSlotB_propLocal i j r))

/-- Refined discharge for `neReifSlot`'s run at `[i, j, r]`. -/
theorem propNeReifSlot_clamp_skipSoundOn (orig : List Domain) (i j r : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0],
          run := fun st => propNeReifSlot st i j r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propNeReifSlot_propLocal i j r))

/-- Refined discharge for `linEqReif`'s run at `r :: is`. -/
theorem propLinEqReif_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) (r : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0))
      (({ watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
          run := fun st => propLinEqReif st coeffs is b r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinEqReif_propLocal coeffs is b r))

/-- Refined discharge for `linNeReif`'s run at `r :: is`. -/
theorem propLinNeReif_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) (r : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0))
      (({ watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
          run := fun st => propLinNeReif st coeffs is b r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinNeReif_propLocal coeffs is b r))

/-- Refined discharge for `linLeReif`'s run at `r :: is` (all three arms:
    pinned true, pinned false, and the unpinned dual bounds arm). -/
theorem propLinLeReif_clamp_skipSoundOn (orig : List Domain) (coeffs : List Int)
    (is : List Nat) (b : Int) (r : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0))
      (({ watches := Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0),
          run := fun st => propLinLeReif st coeffs is b r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propLinLeReif_propLocal coeffs is b r))

/-- Refined discharge for `bool2intSlot`'s run at `[i, k]`. -/
theorem propBool2intSlot_clamp_skipSoundOn (orig : List Domain) (i k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe k 0],
          run := fun st => propBool2intSlot st i k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propBool2intSlot_propLocal i k))

/-- Refined discharge for `minSlot`'s run at `[i, j, k]`. -/
theorem propMin_clamp_skipSoundOn (orig : List Domain) (i j k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0],
          run := fun st => propMin st i j k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propMin_propLocal i j k))

/-- Refined discharge for `maxSlot`'s run at `[i, j, k]`. -/
theorem propMax_clamp_skipSoundOn (orig : List Domain) (i j k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0],
          run := fun st => propMax st i j k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propMax_propLocal i j k))

/-- Refined discharge for `arrayVarIntElementSlot`'s run at `i :: k :: is`. -/
theorem propArrayVarIntElement_clamp_skipSoundOn (orig : List Domain)
    (is : List Nat) (i k : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe i 0 :: Atom.intLe k 0 ::
        is.map (fun j => Atom.intLe j 0))
      (({ watches := Atom.intLe i 0 :: Atom.intLe k 0 ::
             is.map (fun j => Atom.intLe j 0),
          run := fun st => propArrayVarIntElement st is i k } :
          Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propArrayVarIntElement_propLocal is i k))

/-- Refined discharge for `timesSlot`'s run at `[i, j, k]`. -/
theorem propTimes_clamp_skipSoundOn (orig : List Domain) (i j k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0],
          run := fun st => propTimes st i j k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propTimes_propLocal i j k))

/-- Refined discharge for `maxGen`'s run at its named slots. -/
theorem propMaxGen_clamp_skipSoundOn (orig : List Domain)
    (os : List DomIntArg) (r : DomIntArg) {f g : BranchFrame} :
    SkipSoundOn ((os.flatMap DomIntArg.slots ++ r.slots).map
        (fun j => Atom.intLe j 0))
      (({ watches := (os.flatMap DomIntArg.slots ++ r.slots).map
             (fun j => Atom.intLe j 0),
          run := fun st => propMaxGen st os r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propMaxGen_propLocal os r))

/-- Refined discharge for `minGen`'s run at its named slots. -/
theorem propMinGen_clamp_skipSoundOn (orig : List Domain)
    (os : List DomIntArg) (r : DomIntArg) {f g : BranchFrame} :
    SkipSoundOn ((os.flatMap DomIntArg.slots ++ r.slots).map
        (fun j => Atom.intLe j 0))
      (({ watches := (os.flatMap DomIntArg.slots ++ r.slots).map
             (fun j => Atom.intLe j 0),
          run := fun st => propMinGen st os r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propMinGen_propLocal os r))

/-- Refined discharge for the all-slot `minPair` shape at `[i, j, k]`. -/
theorem propMinPairSlot_clamp_skipSoundOn (orig : List Domain) (i j k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0],
          run := fun st => propMin st i j k } : Propagator).clamp orig) f g :=
  propMin_clamp_skipSoundOn orig i j k

/-- Refined discharge for the all-slot `maxPair` shape at `[i, j, k]`. -/
theorem propMaxPairSlot_clamp_skipSoundOn (orig : List Domain) (i j k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0],
          run := fun st => propMax st i j k } : Propagator).clamp orig) f g :=
  propMax_clamp_skipSoundOn orig i j k

/-- Refined discharge for `propCheck`'s run at `dcSlotsFull dc`. -/
theorem propCheck_clamp_skipSoundOn (orig : List Domain) (dc : DomConstraint)
    {f g : BranchFrame} :
    SkipSoundOn ((dcSlotsFull dc).map (fun s => Atom.intLe s 0))
      (({ watches := (dcSlotsFull dc).map (fun s => Atom.intLe s 0),
          run := (propCheck dc).run } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propCheck_propLocal dc))

/-- Refined discharge for `absSlot`'s run at `[i, k]`. -/
theorem propAbs_clamp_skipSoundOn (orig : List Domain) (i k : Nat)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe k 0]
      (({ watches := [Atom.intLe i 0, Atom.intLe k 0],
          run := fun st => propAbs st i k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propAbs_propLocal i k))

/-- Refined discharge for `divGen`'s run at the operands' named slots. -/
theorem propDiv_clamp_skipSoundOn (orig : List Domain)
    (o₁ o₂ r : DomIntArg) {f g : BranchFrame} :
    SkipSoundOn ((o₁.slots ++ o₂.slots ++ r.slots).map
        (fun j => Atom.intLe j 0))
      (({ watches := (o₁.slots ++ o₂.slots ++ r.slots).map
             (fun j => Atom.intLe j 0),
          run := fun st => propDiv st o₁ o₂ r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propDiv_propLocal o₁ o₂ r))

/-- Refined discharge for `modGen`'s run at the operands' named slots. -/
theorem propMod_clamp_skipSoundOn (orig : List Domain)
    (o₁ o₂ r : DomIntArg) {f g : BranchFrame} :
    SkipSoundOn ((o₁.slots ++ o₂.slots ++ r.slots).map
        (fun j => Atom.intLe j 0))
      (({ watches := (o₁.slots ++ o₂.slots ++ r.slots).map
             (fun j => Atom.intLe j 0),
          run := fun st => propMod st o₁ o₂ r } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propMod_propLocal o₁ o₂ r))

/-- Refined discharge for `arrayVarBoolElementSlot`'s run at `i :: k :: is`. -/
theorem propArrayVarBoolElement_clamp_skipSoundOn (orig : List Domain)
    (is : List Nat) (i k : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe i 0 :: Atom.intLe k 0 ::
        is.map (fun j => Atom.intLe j 0))
      (({ watches := Atom.intLe i 0 :: Atom.intLe k 0 ::
             is.map (fun j => Atom.intLe j 0),
          run := fun st => propArrayVarBoolElement st is i k } :
          Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propArrayVarBoolElement_propLocal is i k))

/-- Refined discharge for `arrayBoolAndSlot`'s run at `k :: is`. -/
theorem propArrayBoolAnd_clamp_skipSoundOn (orig : List Domain) (is : List Nat)
    (k : Nat) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe k 0 :: is.map (fun i => Atom.intLe i 0))
      (({ watches := Atom.intLe k 0 :: is.map (fun i => Atom.intLe i 0),
          run := fun st => propArrayBoolAnd st is k } : Propagator).clamp orig) f g :=
  skipSoundOn_of_runLocal (PropLocalOne.clamp (propArrayBoolAnd_propLocal is k))

/-- The registered `eqReifSlot` propagator at `[i, j, r]`. -/
theorem propagatorOfProved_eqReifSlot_clamp_skipSoundOn (orig : List Domain)
    {i j r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.eqReifSlot i j r) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propEqReifSlot_propLocal i j r))

/-- The registered `leReifSlot` propagator at `[i, j, r]`. -/
theorem propagatorOfProved_leReifSlot_clamp_skipSoundOn (orig : List Domain)
    {i j r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.leReifSlot i j r) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propLeReifSlotB_propLocal i j r))

/-- The registered `neReifSlot` propagator at `[i, j, r]`. -/
theorem propagatorOfProved_neReifSlot_clamp_skipSoundOn (orig : List Domain)
    {i j r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.neReifSlot i j r) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe r 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propNeReifSlot_propLocal i j r))

/-- The registered `linEqReif` propagator at `r :: is`. -/
theorem propagatorOfProved_linEqReif_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.linEqReif coeffs is b r) = some p) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propLinEqReif_propLocal coeffs is b r))

/-- The registered `linNeReif` propagator at `r :: is`. -/
theorem propagatorOfProved_linNeReif_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.linNeReif coeffs is b r) = some p) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propLinNeReif_propLocal coeffs is b r))

/-- The registered `linLeReif` propagator at `r :: is`. -/
theorem propagatorOfProved_linLeReif_clamp_skipSoundOn (orig : List Domain)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat} {p : Propagator}
    (hp : propagatorOfProved (.linLeReif coeffs is b r) = some p) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe r 0 :: is.map (fun i => Atom.intLe i 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propLinLeReif_propLocal coeffs is b r))

/-- The registered `bool2intSlot` propagator at `[i, k]`. -/
theorem propagatorOfProved_bool2intSlot_clamp_skipSoundOn (orig : List Domain)
    {i k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.bool2intSlot i k) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe k 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propBool2intSlot_propLocal i k))

/-- The registered `minSlot` propagator at `[i, j, k]`. -/
theorem propagatorOfProved_minSlot_clamp_skipSoundOn (orig : List Domain)
    {i j k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.minSlot i j k) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propMin_propLocal i j k))

/-- The registered `maxSlot` propagator at `[i, j, k]`. -/
theorem propagatorOfProved_maxSlot_clamp_skipSoundOn (orig : List Domain)
    {i j k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.maxSlot i j k) = some p) {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propMax_propLocal i j k))

/-- The registered `arrayBoolAndSlot` propagator at `k :: is`. -/
theorem propagatorOfProved_arrayBoolAndSlot_clamp_skipSoundOn (orig : List Domain)
    {is : List Nat} {k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.arrayBoolAndSlot is k) = some p) {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe k 0 :: is.map (fun i => Atom.intLe i 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propArrayBoolAnd_propLocal is k))

/-- The registered `arrayVarIntElementSlot` propagator at `i :: k :: is`. -/
theorem propagatorOfProved_arrayVarIntElementSlot_clamp_skipSoundOn
    (orig : List Domain) {is : List Nat} {i k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.arrayVarIntElementSlot is i k) = some p)
    {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe i 0 :: Atom.intLe k 0 ::
        is.map (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propArrayVarIntElement_propLocal is i k))

/-- The registered `timesSlot` propagator at `[i, j, k]`. -/
theorem propagatorOfProved_timesSlot_clamp_skipSoundOn (orig : List Domain)
    {i j k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.timesSlot i j k) = some p)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propTimes_propLocal i j k))

/-- The registered `maxGen` propagator at its named slots. -/
theorem propagatorOfProved_maxGen_clamp_skipSoundOn (orig : List Domain)
    {os : List DomIntArg} {r : DomIntArg} {p : Propagator}
    (hp : propagatorOfProved (.maxGen os r) = some p)
    {f g : BranchFrame} :
    SkipSoundOn ((os.flatMap DomIntArg.slots ++ r.slots).map
        (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propMaxGen_propLocal os r))

/-- The registered `minGen` propagator at its named slots. -/
theorem propagatorOfProved_minGen_clamp_skipSoundOn (orig : List Domain)
    {os : List DomIntArg} {r : DomIntArg} {p : Propagator}
    (hp : propagatorOfProved (.minGen os r) = some p)
    {f g : BranchFrame} :
    SkipSoundOn ((os.flatMap DomIntArg.slots ++ r.slots).map
        (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propMinGen_propLocal os r))

/-- The registered all-slot `minPair` propagator at `[i, j, k]`. -/
theorem propagatorOfProved_minPairSlot_clamp_skipSoundOn (orig : List Domain)
    {i j k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.minPair (.slot i) (.slot j) (.slot k)) = some p)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propMin_propLocal i j k))

/-- The registered all-slot `maxPair` propagator at `[i, j, k]`. -/
theorem propagatorOfProved_maxPairSlot_clamp_skipSoundOn (orig : List Domain)
    {i j k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.maxPair (.slot i) (.slot j) (.slot k)) = some p)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe j 0, Atom.intLe k 0]
      (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propMax_propLocal i j k))

/-- The registered checking propagator at `dcSlotsFull dc`. -/
theorem propagatorOfProved_check_clamp_skipSoundOn (orig : List Domain)
    (dc : DomConstraint) {p : Propagator}
    (hf : propCheckFamB dc = true)
    (hp : propagatorOfProved dc = some p) {f g : BranchFrame} :
    SkipSoundOn ((dcSlotsFull dc).map (fun s => Atom.intLe s 0))
      (p.clamp orig) f g := by
  have hp' : p = { watches := (dcSlotsFull dc).map (fun s => Atom.intLe s 0),
                   run := (propCheck dc).run } := by
    obtain ⟨hw, hr⟩ := propagatorOfProved_check_eq hf hp
    cases p
    simp only at hw hr ⊢
    rw [hw, hr]
  rw [hp']
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propCheck_propLocal dc))

/-- The registered `absSlot` propagator at `[i, k]`. -/
theorem propagatorOfProved_absSlot_clamp_skipSoundOn (orig : List Domain)
    {i k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.absSlot i k) = some p)
    {f g : BranchFrame} :
    SkipSoundOn [Atom.intLe i 0, Atom.intLe k 0] (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal (PropLocalOne.clamp (propAbs_propLocal i k))

/-- The registered `divGen` propagator at the operands' named slots. -/
theorem propagatorOfProved_divGen_clamp_skipSoundOn (orig : List Domain)
    {o₁ o₂ r : DomIntArg} {p : Propagator}
    (hp : propagatorOfProved (.divGen o₁ o₂ r) = some p)
    {f g : BranchFrame} :
    SkipSoundOn ((o₁.slots ++ o₂.slots ++ r.slots).map
        (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propDiv_propLocal o₁ o₂ r))

/-- The registered `modGen` propagator at the operands' named slots. -/
theorem propagatorOfProved_modGen_clamp_skipSoundOn (orig : List Domain)
    {o₁ o₂ r : DomIntArg} {p : Propagator}
    (hp : propagatorOfProved (.modGen o₁ o₂ r) = some p)
    {f g : BranchFrame} :
    SkipSoundOn ((o₁.slots ++ o₂.slots ++ r.slots).map
        (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propMod_propLocal o₁ o₂ r))

/-- The registered `arrayVarBoolElementSlot` propagator at `i :: k :: is`. -/
theorem propagatorOfProved_arrayVarBoolElementSlot_clamp_skipSoundOn
    (orig : List Domain) {is : List Nat} {i k : Nat} {p : Propagator}
    (hp : propagatorOfProved (.arrayVarBoolElementSlot is i k) = some p)
    {f g : BranchFrame} :
    SkipSoundOn (Atom.intLe i 0 :: Atom.intLe k 0 ::
        is.map (fun j => Atom.intLe j 0)) (p.clamp orig) f g := by
  simp only [propagatorOfProved, Option.some.injEq] at hp
  subst hp
  exact skipSoundOn_of_runLocal
    (PropLocalOne.clamp (propArrayVarBoolElement_propLocal is i k))

/-! ### The open-obligation schema -/

/-- OPEN-OBLIGATION SCHEMA (per family): a locality claim at an audited
footprint `fp`. The audit table in the header lists, per family, the
candidate footprint and whether the claim is discharged (declared-footprint
families and the three linear families) or open (the missing hypothesis is
exactly this `RunLocalOn fp p`, proved by induction over the run's reads).
`skipSoundOn_of_footprintClaim` converts a claim into the local-soundness
obligation at the audited footprint. -/
def FamilyFootprintClaim (p : Propagator) (fp : List Atom) : Prop :=
  RunLocalOn fp p

/-- A discharged footprint claim gives `SkipSoundOn` at that footprint. -/
theorem skipSoundOn_of_footprintClaim {p : Propagator} {fp : List Atom}
    (h : FamilyFootprintClaim p fp) {f g : BranchFrame} :
    SkipSoundOn fp p f g :=
  skipSoundOn_of_runLocal h

/-! ## 8. Quiescence: the replay theorem -/

/-- Replaying the recorded results at the current frame is exactly the full
scan at that frame, whenever the recorded runs are stable (the scan's
productivity gate is evaluated at the current frame on both sides). -/
theorem scanPropagators_replayAt_eq (f g : BranchFrame) (props : List Propagator)
    (h : ∀ p ∈ props, p.run (frameState g) = p.run (frameState f)) :
    scanPropagators g (props.map (Propagator.replayAt f)) = scanPropagators g props := by
  induction props with
  | nil => rfl
  | cons p ps ih =>
      have hp : p.run (frameState g) = p.run (frameState f) := h p (by simp)
      have hps : ∀ q ∈ ps, q.run (frameState g) = q.run (frameState f) :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      cases hf : p.run (frameState f) with
      | stable =>
          have hg : p.run (frameState g) = .stable := by rw [hp, hf]
          simp only [List.map_cons, scanPropagators, Propagator.replayAt, hf, hg,
            ih hps]
      | conflict c =>
          have hg : p.run (frameState g) = .conflict c := by rw [hp, hf]
          simp only [List.map_cons, scanPropagators, Propagator.replayAt, hf, hg]
      | implied l r =>
          have hg : p.run (frameState g) = .implied l r := by rw [hp, hf]
          by_cases hprod : productive l g = true
          · simp only [List.map_cons, scanPropagators, Propagator.replayAt, hf, hg,
              hprod, if_pos]
          · simp only [List.map_cons, scanPropagators, Propagator.replayAt, hf, hg,
              hprod, Bool.false_eq_true, if_false, ih hps]

/-- **THE QUIESCENCE/COMPLETENESS OBLIGATION IS DISCHARGED**: given the
frozen list obligation (the per-unit local-soundness instances), the replay
of the recorded results never omits an event at the current frame. -/
theorem skipsComplete_proof (original : List Clause) (props : List Propagator)
    (f g : BranchFrame) (db : List Clause)
    (hstable : SkipsStable original props f g db) :
    SkipsComplete original props f g db := by
  intro hev
  have hrun : ∀ p ∈ props, p.run (frameState g) = p.run (frameState f) :=
    fun p hp => hstable p hp (hev p hp)
  have hscan := scanPropagators_replayAt_eq f g props hrun
  simp only [nextPruningEvent, hscan]

end LeanFzn.Solver.Propagation

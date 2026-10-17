/-
File: LeanFzn/Solver/Propagation/DbScanIndex.lean

Purpose (PLAN task P1b): an OPTIMISED, PROVABLY EQUAL re-implementation of the
learned-database scan chain `scanDatabase` -> `clauseRemaining` ->
`literalImpossible`, with the slot index hoisted out of the per-literal loop.

Measured hot spots (E1 instrumentation, `Tests/E1/ScanCounts.lean` +
`Tests/E1/DbScanCounts.lean`): the chain is the single largest component of
the step cost (~51% of the estimated per-step time on the harness battery).
The cost is per LITERAL of every VISITED clause of the learned database:

* `Frame.domains f` is `f.2.map (fun v => [v]) ++ f.1` — the projection
  ALLOCATES the pinned-singleton prefix on every call, once per literal;
* `List.getD` then WALKS the domain list to the literal's slot, once per
  literal (the battery's real frames average ~50 slots, the deep instances
  far more);
* `c.filter` walks EVERY literal of the clause even when two remaining
  literals already settle the classification.

The optimised scan fixes all three, with no change of semantics:

* `frameDomainArray` builds the slot index ONCE per scan (one projection +
  `toArray`), and `literalImpossibleArr` looks a slot up in O(1);
* `clauseClassify` is a first-order recursion that stops at the SECOND
  remaining literal and never allocates the remaining list.

`scanDatabaseFast_eq` proves — UNCONDITIONALLY, on every frame and database —
that the optimised scan returns exactly the certified `scanDatabase` event.
`scanDatabase` and `clauseRemaining`/`literalImpossible` are UNTOUCHED, so
every certified lemma about them continues to hold verbatim; the scheduled
route (`nextPruningEventSched`) is the only consumer wired to the fast scan.

DAG: Pruning + ClausePropagation -> DbScanIndex -> ScheduledPropagation.
-/
import LeanFzn.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.ClausePropagation
open LeanFzn.Semantics LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The slot index -/

/-- The frame's slot→domain index as an array. Built once per scan; the
slot order is exactly `Frame.domains`'s (pinned singletons ++ remaining). -/
def frameDomainArray (f : BranchFrame) : Array Domain :=
  (Frame.domains f).toArray

/-- `literalImpossible` against a precomputed slot index. -/
def literalImpossibleArr (a : Array Domain) (l : Literal) : Bool :=
  ((a[l.atom.slot]?.getD []).all fun v => !l.valueHolds v)

/-- **EQUIVALENCE (literal form)**: the indexed literal test is the certified
`literalImpossible` at the frame's own slot index. -/
theorem literalImpossibleArr_eq (f : BranchFrame) (l : Literal) :
    literalImpossibleArr (frameDomainArray f) l = literalImpossible f l := by
  unfold literalImpossibleArr literalImpossible frameDomainArray
  rw [List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-! ## First-order clause classification -/

/-- The compressed remaining set: `none` = no remaining literal (the scan
reports a conflict on the clause), `some (some l)` = exactly one remaining
(the first one, in clause order), `some none` = at least two remaining. -/
def reduceRemaining : Clause → Option (Option Literal)
  | [] => none
  | [l] => some (some l)
  | _ => some none

/-- First-order classification of one clause against a slot index: the
`acc` carries the first remaining literal seen so far. Runs in clause order,
short-circuits at the second remaining literal, and allocates nothing. -/
def clauseClassify (a : Array Domain) : List Literal → Option Literal → Option (Option Literal)
  | [], none => none
  | [], some l => some (some l)
  | l :: ls, acc =>
    match literalImpossibleArr a l with
    | true => clauseClassify a ls acc
    | false =>
      match acc with
      | none => clauseClassify a ls (some l)
      | some _ => some none

/-- **EQUIVALENCE (one remaining already seen)**: with a remaining literal
already recorded, the classifier reports `some (some l₀)` iff no further
remaining literal exists and `some none` otherwise — exactly the compressed
remaining set of the certified `clauseRemaining`. -/
theorem clauseClassify_some (a : Array Domain) (f : BranchFrame) (c : Clause)
    (l₀ : Literal)
    (h : ∀ l ∈ c, literalImpossibleArr a l = literalImpossible f l) :
    clauseClassify a c (some l₀)
      = (match c.filter (fun l => !literalImpossible f l) with
         | [] => some (some l₀)
         | _ => some none) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleArr a l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleArr a q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassify, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]

/-- **EQUIVALENCE (no remaining literal seen)**: the first-order classifier at
the start state IS the compressed remaining set of the certified
`clauseRemaining` (i.e. of `c.filter (¬literalImpossible)`). -/
theorem clauseClassify_none (a : Array Domain) (f : BranchFrame) (c : Clause)
    (h : ∀ l ∈ c, literalImpossibleArr a l = literalImpossible f l) :
    clauseClassify a c none = reduceRemaining (c.filter (fun l => !literalImpossible f l)) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleArr a l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleArr a q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassify, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]
        rw [clauseClassify_some a f ls l hls]
        cases hq : ls.filter (fun l => !literalImpossible f l) with
        | nil => simp only [hq, reduceRemaining]
        | cons q qs => simp only [hq, reduceRemaining]

/-! ## The optimised database scan -/

/-- The optimised scan recursion: the certified `scanDatabase` with a
prebuilt slot index and the first-order clause classifier. Same recursion
order, same event payloads, same `productive` gate, same `original.contains`
flag. -/
def scanDatabaseFastAux (original : List Clause) (f : BranchFrame) (a : Array Domain) :
    List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match clauseClassify a c none with
    | none => .conflict [c]
    | some none => scanDatabaseFastAux original f a rest
    | some (some l) =>
        match productive l f with
        | true => .implied l c false (!(original.contains c))
        | false => scanDatabaseFastAux original f a rest

/-- The optimised database scan: the slot index is built ONCE per call. -/
def scanDatabaseFast (original : List Clause) (f : BranchFrame) (db : List Clause) :
    PruningEvent :=
  scanDatabaseFastAux original f (frameDomainArray f) db

/-- **THE EQUALITY THEOREM (P1b DoD, indexed form)**: at any slot index that
agrees with `literalImpossible` pointwise, the optimised scan returns exactly
the certified `scanDatabase` event. -/
theorem scanDatabaseFastAux_eq (original : List Clause) (f : BranchFrame)
    (a : Array Domain)
    (h : ∀ l, literalImpossibleArr a l = literalImpossible f l) (db : List Clause) :
    scanDatabaseFastAux original f a db = scanDatabase original f db := by
  induction db with
  | nil => rfl
  | cons c rest ih =>
      rw [scanDatabaseFastAux, scanDatabase]
      rw [clauseClassify_none a f c (fun l _ => h l)]
      rw [show c.filter (fun l => !literalImpossible f l) = clauseRemaining f c from rfl]
      cases hr : clauseRemaining f c with
      | nil => simp only [reduceRemaining]
      | cons x xs =>
          cases xs with
          | nil =>
              simp only [reduceRemaining]
              by_cases hp : productive x f = true
              · rw [hp]
                simp
              · rw [Bool.eq_false_iff.mpr hp]
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih
          | cons y ys =>
              exact ih

/-- **THE EQUALITY THEOREM (P1b DoD)**: the optimised database scan returns
EXACTLY the certified `scanDatabase` event — on every frame, every database
and every original clause list; no invariant, no side condition. -/
theorem scanDatabaseFast_eq (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    scanDatabaseFast original f db = scanDatabase original f db :=
  scanDatabaseFastAux_eq original f (frameDomainArray f)
    (fun l => literalImpossibleArr_eq f l) db

end LeanFzn.Solver.Propagation

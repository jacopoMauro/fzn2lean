import LeanFzn.Solver.Propagation.Operations

/-!
# Literal clamp (U1e)

Runtime normalization of order/removal literals against the ORIGINAL slot
domains. Propagators (e.g. `int_times`) compute bounds outside the box; such a
literal is meaning-equivalent, under `a.Fits orig`, to a literal whose
threshold lies in the finite representative set
`threshPool d = ints d ++ (ints d).map (· - 1)` of the slot's original domain.
`snapLit orig` performs that normalization:

* `s ≤ k` becomes `s ≤ r`, `r` the largest pool threshold `≤ k` (or the least
  pool threshold `min - 1` when none is `≤ k`);
* `s ≠ v` with `v` outside the original integer values (root-true) becomes
  `¬ (s ≤ min - 1)` (and `¬ (s ≠ v)`, root-false, becomes `s ≤ min - 1`).

Everything else (Booleans, in-pool literals, slots outside `orig`, slots with no
integer values) is unchanged. `snapLit` is the identity on pool literals.
-/

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core

/-- Integer values of a slot's original domain. -/
def clampInts (d : Domain) : List Int := d.filterMap Value.intView

/-- Threshold representatives: values and their predecessors. -/
def clampPool (ints : List Int) : List Int := ints ++ ints.map (fun i => i - 1)

/-- Least element of a nonempty list (default `0` on `[]`). -/
def clampMin (xs : List Int) : Int := xs.foldl min (xs.headD 0)

/-- The pool threshold a bound `k` is mapped to. -/
def snapBound (ints : List Int) (k : Int) : Int :=
  ((clampPool ints).filter (· ≤ k)).foldl max (clampMin (clampPool ints))

/-- The clamp of one literal against the original domains. -/
def snapLit (orig : List Domain) (l : Literal) : Literal :=
  match l.atom with
  | .intLe s k =>
      match orig[s]? with
      | none => l
      | some d =>
          if (clampInts d).isEmpty then l
          else ⟨.intLe s (snapBound (clampInts d) k), l.positive⟩
  | .intNe s v =>
      match orig[s]? with
      | none => l
      | some d =>
          if (clampInts d).isEmpty ∨ v ∈ clampInts d then l
          else ⟨.intLe s (clampMin (clampPool (clampInts d))), !l.positive⟩
  | .boolEq _ _ => l

/-- Clamp of a clause. -/
def snapClause (orig : List Domain) (c : Clause) : Clause := c.map (snapLit orig)

/-- Clamp of a propagation result. -/
def snapResult (orig : List Domain) : PropagationResult → PropagationResult
  | .stable => .stable
  | .implied l r => .implied (snapLit orig l) { r with clause := snapClause orig r.clause }
  | .conflict c => .conflict (snapClause orig c)

/-- Clamp of a propagator: same watches, clamped emissions. -/
def Propagator.clamp (orig : List Domain) (p : Propagator) : Propagator :=
  { p with run := fun st => snapResult orig (p.run st) }

/-- Clamp a registered propagator list. -/
def clampProps (orig : List Domain) (props : List Propagator) : List Propagator :=
  props.map (Propagator.clamp orig)

end LeanFzn.Solver.Propagation

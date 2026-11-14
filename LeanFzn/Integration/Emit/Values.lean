/-
Purpose: Describe the literal values emitted for a typed source-model store.
Dependencies: Emit.Model supplies the actual declaration-aware output; the
solution runtime supplies the decoded entry type. No parser-success premise
appears in the value correspondence proved here.
DAG: source-model semantics + Emit.Model -> Emit.Values -> Emit.RoundTrip.
-/
import LeanFzn.Integration.Emit.Model
import LeanFzn.Checker.SolutionGrammar

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Checker.Solution

/-- Exactly the scalar values admitted by the non-float solution format. -/
def ScalarSolutionValue : Value → Prop
  | .bool _ | .int _ | .setOfInt _ => True
  | .array _ => False

/-- The literal the emitter writes. Sets are normalized extensionally,
not compared as lists: sorting and removing duplicates preserve their value. -/
def emittedScalarLiteral : Value → BasicLiteral
  | .bool b => .bool b
  | .int i => .int i
  | .setOfInt s => .set (.intSet s.sortElems)
  | .array _ => .bool false

/-- The decoded entry corresponding to a declaration's emitted value. -/
def emittedDeclEntry (d : VarDeclItem) (v : Value) : Entry :=
  ⟨d.name.name, match d, v with
    | .array _ _ _ _, .array vs => .array (vs.map emittedScalarLiteral)
    | _, v => .scalar (emittedScalarLiteral v)⟩

/-- Typed scalar declarations cannot hold arrays. -/
theorem scalarSolutionValue_of_contains {ty : BasicVarType} {v : Value}
    (h : ty.contains v) : ScalarSolutionValue v := by
  cases ty <;> cases v <;> simp_all [BasicVarType.contains, ScalarSolutionValue]

/-- Every member survives the emitter's sorted set enumeration. -/
theorem mem_emittedSet {s : IntSetValue} {x : Int} :
    x ∈ s.sortElems ↔ s.Contains x := by
  cases s with
  | enumeration xs =>
      simp only [IntSetValue.sortElems, IntSetValue.Contains]
      rw [List.mem_mergeSort, List.mem_eraseDups]
  | interval lo hi =>
      simp only [IntSetValue.sortElems, IntSetValue.Contains]
      by_cases h : hi < lo
      · simp [h]; omega
      · simp only [h, ↓reduceIte, List.mem_map, List.mem_range]
        constructor
        · rintro ⟨n, hn, rfl⟩
          have hlen : ((hi - lo + 1).toNat : Int) = hi - lo + 1 :=
            Int.toNat_of_nonneg (by omega)
          have hn' : (n : Int) < (hi - lo + 1).toNat := Int.ofNat_lt.mpr hn
          omega
        · rintro ⟨hlo, hhi⟩
          refine ⟨(x - lo).toNat, ?_, ?_⟩
          · have h1 : ((x - lo).toNat : Int) = x - lo := Int.toNat_of_nonneg (by omega)
            have h2 : ((hi - lo + 1).toNat : Int) = hi - lo + 1 :=
              Int.toNat_of_nonneg (by omega)
            exact Int.ofNat_lt.mp (by omega)
          · rw [Int.toNat_of_nonneg (by omega)]
            omega

/-- Every scalar literal emitted by the solver has exactly the original
semantic value, including interval and noncanonical enumeration sets. -/
theorem emittedScalarLiteral_denotes {v : Value} (hv : ScalarSolutionValue v) :
    (emittedScalarLiteral v).denote.SemEq v := by
  cases v with
  | bool b => rfl
  | int i => rfl
  | setOfInt s =>
      intro x
      exact mem_emittedSet
  | array vs => cases hv

/-- Exact semantic values for solution entries, allowing the set
normalization mandated by emission and comparing arrays elementwise. -/
def SolValueMatches : SolValue → Value → Prop
  | .scalar l, v => l.denote.SemEq v
  | .array ls, .array vs => Forall2 (fun l v => l.denote.SemEq v) ls vs
  | .array _, _ => False

/-- A declaration and its value have the scalar/flat-array shape guaranteed
by model satisfaction. The array length is part of the contract. -/
def DeclValueFits (d : VarDeclItem) (v : Value) : Prop :=
  match d, v with
  | .basic ty _ _ _, v => ty.contains v
  | .array ty _ _ _, .array vs =>
      vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v
  | .array _ _ _ _, _ => False

/-- The decoded entry prescribed for every well-typed declaration denotes
its original scalar or array value. -/
theorem emittedDeclEntry_denotes {d : VarDeclItem} {v : Value}
    (h : DeclValueFits d v) : SolValueMatches (emittedDeclEntry d v).value v := by
  cases d with
  | basic ty n anns init =>
      exact emittedScalarLiteral_denotes (scalarSolutionValue_of_contains h)
  | array ty n anns es =>
      cases v with
      | bool _ | int _ | setOfInt _ => cases h
      | array vs =>
          change Forall2 _ (vs.map emittedScalarLiteral) vs
          have hall := h.2
          clear h
          induction vs with
          | nil => trivial
          | cons v vs ih =>
              exact ⟨(emittedScalarLiteral_denotes (scalarSolutionValue_of_contains
                  (hall v (by simp)))),
                (ih (fun w hw => hall w (by simp [hw])))⟩

/-- The semantic assignment facts of a satisfying store imply the output
shape contract, independently of lexical or parser behavior. -/
theorem declValueFits_of_satisfiesDyn {pred : PredicateInterpretation}
    {m : Model} {store : Store} (h : SatisfiesDyn pred m store)
    {d : VarDeclItem} (hd : d ∈ m.variables) :
    ∃ v, store d.name = some v ∧ DeclValueFits d v := by
  have hv := h.2.1 d hd
  cases d with
  | basic ty n anns init => exact hv
  | array ty n anns es =>
      obtain ⟨vs, hs, hlen, hall⟩ := hv
      exact ⟨.array vs, hs, hlen, hall⟩

end LeanFzn.Integration

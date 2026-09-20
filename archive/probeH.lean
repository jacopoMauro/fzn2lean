import solver.Emit.Roundtrip

namespace LeanFzn.Solver

open LeanFzn.Lexer

/-! Probe for the P0.7g helper layer: list reshaping for the
left-associated entry-line composite.  If these land, the bool
sibling reduces to: segment lemma + array-equality transports. -/

-- 1. The composite's length, spelled left-to-right:
example {nm lit tl : List Char} :
    (nm ++ [' ', '=', ' '] ++ lit ++ [';'] ++ tl).length
      = (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length
        + lit.length + 1 + tl.length := by
  have h1 : (nm ++ [' ', '=', ' '] ++ lit ++ [';'] ++ tl).length
      = (nm ++ [' ', '=', ' ']).length + (lit ++ [';'] ++ tl).length := by
    show (nm ++ [' ', '=', ' '] ++ (lit ++ [';'] ++ tl)).length
        = (nm ++ [' ', '=', ' ']).length + (lit ++ [';'] ++ tl).length
    exact List.length_append _ _
  have h2 : (lit ++ [';'] ++ tl).length = lit.length + 1 + tl.length := by
    have h3 : (lit ++ [';'] ++ tl).length
        = lit.length + (([';'] : List Char) ++ tl).length := by
      show (lit ++ (([';'] : List Char) ++ tl)).length
          = lit.length + (([';'] : List Char) ++ tl).length
      exact List.length_append _ _
    have h4 : (([';'] : List Char) ++ tl).length = 1 + tl.length := by
      show ((';' : Char) :: tl).length = 1 + tl.length
      simp
    omega
  have hws : (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)]).length
      = (nm ++ [' ', '=', ' ']).length := rfl
  omega

-- 2. the array equality between the two spellings (used as the
--    transport for lexToken calls):
example {nm lit tl : List Char} :
    ((nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
      ++ (lit ++ ((';' : Char) :: tl))).toArray
      = (nm ++ [' ', '=', ' '] ++ lit ++ [';'] ++ tl).toArray := by
  apply congrArg List.toArray
  show (nm ++ [(' ' : Char), ('=' : Char), (' ' : Char)])
      ++ (lit ++ (';' :: tl))
      = nm ++ [' ', '=', ' '] ++ lit ++ [';'] ++ tl
  exact List.append_assoc _ _ _

end LeanFzn.Solver

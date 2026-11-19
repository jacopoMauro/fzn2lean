% G2 — truncated integer modulo `mod` (the companion of `int_div`).
%
% MiniZinc 2.10.1 handbook, "Integer FlatZinc builtins": "int_mod(x,y,z)
% Constrains x % y = z".  The same handbook page defines `int_div` as
% truncation, and MiniZinc's `mod` satisfies `x mod y = x - (x div y) * y`,
% so the result takes the sign of the dividend.  The Lean interpretation
% `intMod` in `LeanFzn/Semantics/StdLib.lean` (`stdInterp "int_mod"`) is
% `c = Int.tmod a b` under a `b != 0` guard; `Int.tmod` is Lean's truncating
% modulo, which also takes the sign of the dividend.
%
% The divisor-zero case is undefined upstream; see `int_div_zero.mzn`.

array[int, int] of int: cases = array2d(1..10, 1..2,
  [-7, 2,   -7, -2,   7, 2,   7, -2,
   13, 5,  -13, 5,   13, -5, -13, -5,
    1, 2,   -1, 2]);
solve satisfy;
output [ show(cases[i, 1]) ++ " mod " ++ show(cases[i, 2]) ++
         " = " ++ show(cases[i, 1] mod cases[i, 2]) ++ "\n" |
         i in index_set_1of2(cases) ];

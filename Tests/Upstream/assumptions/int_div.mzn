% G2 — truncated integer division `div`.
%
% MiniZinc 2.10.1 handbook, "Integer FlatZinc builtins": "int_div(x,y,z)
% Constrains x / y = z, where z is rounded to the value closest to zero
% (i.e., truncated)."  The Lean interpretation `intDiv` in
% `LeanFzn/Semantics/StdLib.lean` (`stdInterp "int_div"`) is `c = Int.tdiv a b`
% under a `b ≠ 0` guard; `Int.tdiv` is Lean's truncating division.  This
% model makes MiniZinc *evaluate* the operator on all four sign
% combinations and on cases where the dividend's magnitude is smaller than
% the divisor's.
%
% The division-by-zero case is undefined upstream (an evaluation error); it
% cannot appear in a `show` that must produce a value, so it lives in
% `int_div_zero.mzn` instead.
array[int, int] of int: cases = array2d(1..10, 1..2,
  [-7, 2,   -7, -2,   7, 2,   7, -2,
   13, 5,  -13, 5,   13, -5, -13, -5,
    1, 2,   -1, 2]);
solve satisfy;
output [ show(cases[i, 1]) ++ " div " ++ show(cases[i, 2]) ++
         " = " ++ show(cases[i, 1] div cases[i, 2]) ++ "\n" |
         i in index_set_1of2(cases) ];

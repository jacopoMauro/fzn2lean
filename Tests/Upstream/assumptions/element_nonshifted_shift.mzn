% G6 — the shift the `_nonshifted` variants apply on a non-`1..n` array.
%
% This is the boundary that justifies the "same as the plain form on `1..n`"
% simplification: on the array `5..7` the MiniZinc redefinition subtracts
% `min(index_set) - 1 = 4`, so the nonshifted index `5` selects the first
% element and `2` names nothing (`unsatisfiable`).  The model has no solution
% (expected `=====UNSATISFIABLE=====`), confirming that the simplification is
% *only* licensed for `1..n` arrays; the Lean side never sees the others.
array[int] of var int: xs = array1d(5..7, [10, 20, 30]);
predicate ns(var int: i, array [int] of var int: a, var int: e) =
  array_var_int_element_nonshifted(i, a, e);
var int: y = 20;
constraint ns(2, xs, y);
solve satisfy;
output [show(y)];

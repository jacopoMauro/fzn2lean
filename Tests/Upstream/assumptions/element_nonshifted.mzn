% G6 — `*_nonshifted` element variants on a `1..n` array.
%
% MiniZinc 2.10.1 defines the `_nonshifted` element constraints in
% `share/minizinc/std/redefinitions-2.0.2.mzn` as
%   array_var_int_element_nonshifted(idx, xs, y) =
%     array_var_int_element((idx - (min(index_set(xs)) - 1)) :: domain,
%       array1d(xs), y)
% (likewise for the bool and set variants).  When the array's index set is
% `1..n`, `min(index_set(xs)) - 1 = 0` and the shift is the identity.  The
% Lean interpretation in `LeanFzn/Semantics/StdLib.lean` makes the plain and
% `_nonshifted` variants coincide on `1..n` arrays (both `valuesGet1 xs i`),
% which is the project's array-index convention.
%
% This model asks MiniZinc (its own redefinition, not a property test) to
% evaluate the nonshifted variant at a valid index and prints the value.
array[int] of var int: xs = array1d(1..3, [10, 20, 30]);
predicate ns(var int: i, array [int] of var int: a, var int: e) =
  array_var_int_element_nonshifted(i, a, e);
var int: y = 20;
constraint ns(2, xs, y);
solve satisfy;
output [show(y)];

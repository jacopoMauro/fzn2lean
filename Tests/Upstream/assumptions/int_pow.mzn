% G4 — integer power `pow` at corner exponents.
%
% MiniZinc 2.10.1 handbook, "Integer FlatZinc builtins": "int_pow(x,y,z)
% Constrains z = x^y, z is constrained to 1 div pow(x, abs(y)) when y < 0."
% The Lean interpretation `intPow` in `LeanFzn/Semantics/StdLib.lean` is
% `if y < 0 then Int.tdiv 1 (x ^ (-y).toNat) else x ^ y.toNat`, and
% `stdInterp "int_pow"` adds the side condition `y < 0 -> x != 0` for the
% undefined `0 ^ negative` case (see `int_pow_zero_negative.mzn`).
% `int_pow_fixed` has the same interpretation (`stdInterp "int_pow_fixed"`).
%
% This model evaluates every corner case the handbook distinguishes: positive
% exponents, the exponent 0 (including `0 ^ 0`, which is 1 upstream), negative
% exponents on bases with |x| >= 2 (where the truncated `1 div x^|y|` is 0)
% and on the bases 1/-1 (where it is 1/-1).  Base/exponent pairs are printed
% with explicit parentheses so the reading is not confused with MiniZinc's
% unary-minus precedence (`-3 ^ 2` parses as `-(3 ^ 2)`).
array[int, int] of int: cases = array2d(1..20, 1..2,
  [ 0, 0,   1, 0,  -1, 0,   2, 0,  -2, 0,
    3, 2,  -3, 2,   7, 2,  -7, 2,
    2, 3,  -2, 3,   1, -1, -1, -1,
    2, -1, -2, -1,  3, -2, -3, -2,
    7, -2, -7, -2, 10, -3]);
solve satisfy;
output [ "(" ++ show(cases[i, 1]) ++ ") ^ (" ++ show(cases[i, 2]) ++
         ") = " ++ show(pow(cases[i, 1], cases[i, 2])) ++ "\n" |
         i in index_set_1of2(cases) ];

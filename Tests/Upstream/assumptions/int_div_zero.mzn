% G2 — the divisor-zero boundary.
%
% MiniZinc 2.10.1 handbook: `int_div(x,y,z)` constrains `x / y = z` with
% truncation and says nothing about `y = 0`; the driver rejects it at
% evaluation time with "division by zero".  The Lean interpretation
% (`stdInterp "int_div"`, "int_mod") guards the equation by `b != 0`, so the
% predicate is *false* for every divisor zero and both divide and modulo
% predicates fail closed.
%
% This model is expected to *fail* to evaluate (stderr contains "division by
% zero").  The runner records that as the observed upstream behaviour; it is
% not a model to solve.
var int: q = -7 div 0;
solve satisfy;
output [show(q)];

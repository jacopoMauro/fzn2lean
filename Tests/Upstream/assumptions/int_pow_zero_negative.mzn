% G4 — the excluded `0 ^ negative` boundary.
%
% The Lean interpretation excludes the case `y < 0` with `x = 0` by the side
% condition `y < 0 -> x != 0`, so `int_pow(0, -1, z)` is *false* for every z.
% Upstream, `pow(0, -1)` is undefined ("1 div pow(0, 1)" divides by zero), so
% this model is expected to *fail* to evaluate; the runner records that.
var int: q = pow(0, -1);
solve satisfy;
output [show(q)];

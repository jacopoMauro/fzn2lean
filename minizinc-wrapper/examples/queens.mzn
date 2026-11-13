% Satisfaction: n-queens.
include "globals.mzn";
int: n = 8;
array[1..n] of var 1..n: q;
constraint all_different(q);
constraint all_different([q[i] + i | i in 1..n]);
constraint all_different([q[i] - i | i in 1..n]);
solve satisfy;
output ["q = \(q)\n"];

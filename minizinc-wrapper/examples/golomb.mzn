% Hard optimization: Golomb ruler (use with a time limit).
include "globals.mzn";
int: m = 11;
int: n = m * m;
array[1..m] of var 0..n: mark;
array[1..(m * (m - 1)) div 2] of var 0..n: diffs =
  [mark[j] - mark[i] | i in 1..m, j in i + 1..m];
constraint mark[1] = 0;
constraint forall(i in 1..m - 1)(mark[i] < mark[i + 1]);
constraint all_different(diffs);
constraint diffs[1] < diffs[(m * (m - 1)) div 2];
solve minimize mark[m];
output ["mark = \(mark), length = \(mark[m])\n"];

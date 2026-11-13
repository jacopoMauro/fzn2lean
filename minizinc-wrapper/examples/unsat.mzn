% Unsatisfiable: pigeonhole, 4 pigeons in 3 holes.
include "globals.mzn";
array[1..4] of var 1..3: hole;
constraint all_different(hole);
solve satisfy;

% Optimization: 0/1 packing (knapsack-style).
int: n = 6;
array[1..n] of int: w = [12, 7, 11, 8, 9, 6];
array[1..n] of int: v = [24, 13, 23, 15, 16, 11];
int: cap = 26;
array[1..n] of var bool: take;
constraint sum(i in 1..n)(w[i] * bool2int(take[i])) <= cap;
var int: value = sum(i in 1..n)(v[i] * bool2int(take[i]));
solve maximize value;
output ["take = \(take), value = \(value)\n"];

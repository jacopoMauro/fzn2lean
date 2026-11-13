% Outside the certified fragment (float variables): reported as UNSUPPORTED.
var 0.0..10.0: x;
constraint x * x >= 2.0;
solve minimize x;

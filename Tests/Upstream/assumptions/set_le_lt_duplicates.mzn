% G5 — the sort/dedup normalisation of `set_le`/`set_lt`.
%
% A set literal with a repeated element still denotes the same set, and the
% lexicographic order is defined on *sorted, de-duplicated* elements, so the
% interior ordering of an enumeration must not matter.  The Lean side
% (`IntSetValue.sortElems`) sorts with `List.mergeSort` and calls
% `List.eraseDups` before `listLexLe`/`listLexLt`; this model confirms that
% MiniZinc agrees that `{4,1,4,3}` is the same set as `{1,3,4}` and orders
% like it.
set of int: A = {4,1,4,3};
set of int: B = {1,3,9};
set of int: C = {3,1,7};
solve satisfy;
output [ "A <= B : " ++ show(A <= B) ++ " " ++ show(A < B) ++ "\n" ++
         "A <= C : " ++ show(A <= C) ++ " " ++ show(A < C) ++ "\n" ];

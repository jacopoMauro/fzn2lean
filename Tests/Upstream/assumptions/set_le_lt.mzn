% G5 — `set_le` / `set_lt` as lexicographic order on the sorted elements.
%
% MiniZinc 2.10.1 handbook, "Set FlatZinc builtins": "set_le(s,t) Constrains
% s <= t (lexicographic order of the sorted lists of elements)" and
% "set_lt(s,t) Constrains s < t (lexicographic order of the sorted lists of
% elements)".  The Lean interpretation `setLe`/`setLt` in
% `LeanFzn/Semantics/StdLib.lean` compares `IntSetValue.sortElems`: the sorted,
% deduplicated element list (enumeration order and duplicates are normalized
% away; a reversed interval is empty), using `listLexLe`/`listLexLt`.
%
% The cases exercise: equal-length sets differing at a smaller element; equal
% sets (<= true, < false); a proper prefix (a strictly-smaller last element
% decides); sets that differ only in a *larger* element (the lexicographic
% order, unlike subset, still decides); empty sets; and first-element
% differences.  Each printed pair is (s <= t, s < t).
set of int: S1 = {1,3};     set of int: T1 = {1,4};
set of int: S2 = {1,3};     set of int: T2 = {1,3};
set of int: S3 = {1,3};     set of int: T3 = {1,3,9};
set of int: S4 = {1,9};     set of int: T4 = {1,3,9};
set of int: S5 = {};        set of int: T5 = {2};
set of int: S6 = {2};       set of int: T6 = {};
set of int: S7 = {5};       set of int: T7 = {1,9};
set of int: S8 = {1,2,3};   set of int: T8 = {1,2};
solve satisfy;
output [ show(S1) ++ " <= " ++ show(T1) ++ " : " ++ show(S1 <= T1) ++ " " ++ show(S1 < T1) ++ "\n" ++
         show(S2) ++ " <= " ++ show(T2) ++ " : " ++ show(S2 <= T2) ++ " " ++ show(S2 < T2) ++ "\n" ++
         show(S3) ++ " <= " ++ show(T3) ++ " : " ++ show(S3 <= T3) ++ " " ++ show(S3 < T3) ++ "\n" ++
         show(S4) ++ " <= " ++ show(T4) ++ " : " ++ show(S4 <= T4) ++ " " ++ show(S4 < T4) ++ "\n" ++
         show(S5) ++ " <= " ++ show(T5) ++ " : " ++ show(S5 <= T5) ++ " " ++ show(S5 < T5) ++ "\n" ++
         show(S6) ++ " <= " ++ show(T6) ++ " : " ++ show(S6 <= T6) ++ " " ++ show(S6 < T6) ++ "\n" ++
         show(S7) ++ " <= " ++ show(T7) ++ " : " ++ show(S7 <= T7) ++ " " ++ show(S7 < T7) ++ "\n" ++
         show(S8) ++ " <= " ++ show(T8) ++ " : " ++ show(S8 <= T8) ++ " " ++ show(S8 < T8) ];

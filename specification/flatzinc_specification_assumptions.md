# FlatZinc Specification Ambiguities and Resolutions

Each point where the pinned specification was ambiguous, silent, or
contradictory, and the decision taken. The normative reference is MiniZinc
2.10.0, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`); the general MiniZinc language
specification resolves semantic notions that FlatZinc inherits but does not
repeat. This project formalizes the integer/Boolean fragment (no floats).

**Where the different kinds of decision live:**

* **R-series (below)** — ambiguities of the FlatZinc *syntax and static
  semantics* (grammar, scoping, typing), each resolved once, globally.
* **A-series (below)** — behavior the specification leaves *silent*
  (integer width, error taxonomy, solution-string format, …).
* **G-series (below)** — the interpretive decisions behind the
  *predicate semantics*: what each builtin and `fzn_*` global constraint
  means as a predicate on assignments.  This is the largest body of
  assumption, because the FlatZinc specification itself assigns no
  meaning to `fzn_*` names (they are defined by the MiniZinc standard
  library decompositions, and several handbook texts are loose,
  partial, or omit corner cases).  Every G-entry names the predicate
  family, the decision, its normative justification, and where the
  decision is implemented and tested.
* **Module docstrings** — each of `LeanFzn/FznStdLib.lean` and the ten
  `LeanFzn/FznGlobals/*` family modules opens with the per-predicate
  handbook quotations and decomposition citations backing its
  interpretations; the G-series below records only the decisions that
  went *beyond* a literal reading of that text.
* **`specification/minizinc-2.10.0/predicates_and_globals_report.md`** —
  the inventory of all builtin and global names (the scope checklist).


## Ambiguities resolved

### R1. Reversed range bounds

**Ambiguity:** Is a range whose lower bound exceeds its upper bound, such as
`5..1`, an error or an empty set?

**Resolution:** It is valid and denotes the empty set. A variable with such a
domain makes the model unsatisfiable, not ill-formed.

### R2. Duplicate or unordered set elements

**Ambiguity:** May set literals contain duplicate elements, and does element
order matter?

**Resolution:** Sets are extensional: `{1, 1, 2}` denotes `{1, 2}`.
Duplicates and order in the source never affect semantics and are not syntax
errors.

### R3. Array index set versus initializer

**Ambiguity:** What happens when an explicit array index set does not match
the initializer?

**Resolution:** A static well-formedness error, not a parse error. In this
one-dimensional fragment the check reduces to comparing lengths. A predicate
parameter `array [int]` accepts any length; `array [1..n]` requires exactly
that index set.

### R4. Duplicate declarations

**Ambiguity:** May a variable, parameter, or predicate be declared more than
once?

**Resolution:** No. Parameters and variables share one value namespace and
must be pairwise distinct; predicate names occupy a separate namespace;
predicate formal-parameter names must be distinct within a declaration. All
violations are static errors.

### R5. Declaration order

**Ambiguity:** Must an identifier be declared before it is used?

**Resolution:** No. References resolve against the completed global
environment; forward references are permitted, and references to absent names
are static errors.

### R6. Variable initializers and aliases

**Ambiguity:** What does `var T: x = e;` mean — aliasing, equality, or
assignment?

**Resolution:** It imposes equality: `x = eval(e)` in every solution. Alias
cycles contribute equality conditions rather than being rejected. A fixed
value outside the variable's domain makes the model unsatisfiable rather than
ill-formed; parameter data outside its type is an instance error.

### R7. Objective types

**Ambiguity:** The grammar allows any basic expression as a minimize/maximize
objective, including Boolean and set values.

**Resolution:** The objective must have type `int`; Boolean and set objectives
parse but are statically invalid.

### R8. Predicate availability and checking

**Ambiguity:** Which predicates must a reader support, and how are calls
checked?

**Resolution:** Static checking is parameterized by a signature environment:
a constraint is valid iff its predicate is declared in the model or supplied
by the environment and its arguments match the signature, including
par-to-var coercion. Meanings remain external (`PredicateInterpretation`);
the parser does not decide support.

### R9. Annotation semantics

**Ambiguity:** Do annotations change the set of solutions, and are
annotation collections ordered?

**Resolution:** No. Core satisfaction ignores annotations. Outer annotation
collections are unordered and idempotent; arrays inside an annotation (such
as `seq_search` arguments) remain ordered. Unknown annotations are accepted.

### R10. Identifier classes

**Ambiguity:** Which name positions may start with an underscore?

**Resolution:** Only variable and parameter identifiers. Predicate names,
predicate-parameter names, and annotation names may not; the parser and the
grammar enforce this at every occurrence.

### R11. String escape syntax

**Ambiguity:** The FlatZinc prose says only “as in C”.

**Resolution:** Adopt the MiniZinc lexical rules: `\"`, `\\`, `\n`, `\t`,
one or two hex digits after `\x`, and one to three octal digits; single-line
UTF-8 literals; no interpolation. Unknown escapes, physical newlines, and
unterminated strings are rejected.

**Implementation status (known gap):** the lexer implements `\"`, `\\`,
`\n`, `\t`, `\r`, `\'` and rejects physical newlines and unterminated
strings, but **keeps unknown escapes literally** (including `\x…`/octal
digit sequences, which are not decoded) instead of rejecting them.
Strings appear only inside annotations, which core satisfaction ignores
(R9), so this does not affect the checker's verdicts today; tighten the
lexer before giving strings semantic weight.

### R12. Specification version

**Ambiguity:** The local RST does not identify an upstream commit, and
upstream grammar details change over time.

**Resolution:** Pin MiniZinc 2.10.0 at immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` with a vendored grammar;
upgrading is an explicit migration requiring a new version directory and an
audit of syntax, semantics, assumptions, implementation, and proofs.

## Unspecified behavior, assumed

Where the specification is silent rather than ambiguous, the project adopts
these assumptions.

### A1. Integer capacity

**Unspecified:** solver integer width and overflow behavior.

**Assumption:** unbounded mathematical integers (Lean `Int`); a solver
interface may add a representability predicate, but the core semantics never
wraps silently.

### A2. Invalid UTF-8 from byte escapes

**Unspecified:** what a reader must do when byte escapes decode to invalid
UTF-8.

**Assumption:** reject such strings.

### A3. Unsupported or multiply matching predicates

**Unspecified:** there is no solver-independent closed predicate environment
or formal overload-resolution judgement.

**Assumption:** each context supplies a finite signature environment with
deterministic lookup; ambiguous matching is a static error.

### A4. Alias identity and annotations

**Unspecified:** whether annotations on aliased names merge, and which
internal variable owns the storage.

**Assumption:** aliases mean equality only; annotations stay attached to
their declaration; storage sharing is a solver optimization.

### A5. Error classification

**Unspecified:** no single formal error taxonomy for malformed hand-written
`.fzn` files.

**Assumption:** four layers — (1) lex/parse error, (2) static
well-formedness error, (3) instance evaluation error, (4) well-formed but
unsatisfiable model. The parser theorem concerns only layer 1.

### A6. Global-constraint semantics (`fzn_*` solver predicates)

**Unspecified:** the FlatZinc specification itself assigns no meaning to
`fzn_*` solver predicates; they are defined by the MiniZinc standard
library decompositions.

**Assumption:** the semantics of each supported `fzn_*` global constraint
follow the MiniZinc 2.10.0 stdlib (the vendored `lib-globals-*.html`
handbook pages, cross-checked against the pinned
`share/minizinc/std/fzn_*.mzn` decompositions). 138 names of the non-float,
non-opt, non-reified fragment are formalized with mathematical
interpretations and verified executable twins; the semantics of the others
(float/opt/`_reif` variants) are deliberately **not guessed** — the
five out-of-fragment core names (`fzn_alternative`, `fzn_span`,
`fzn_neural_net`, `fzn_piecewise_linear`,
`fzn_piecewise_linear_non_continuous`) are listed in
`globalsUnsupported` and reported rather than silently mis-checked.

The individual interpretive decisions that went beyond a literal
reading of the handbook/decompositions are recorded in the **G-series**
below (G1 generalizes this entry); the builtin-level decisions are
G2–G6, the family-specific ones G7–G23.

### A7. Solution strings

**Unspecified:** the exact solution-output format a checker must accept.

**Assumption:** Section 4.3.3.1 of the MiniZinc 2.10.0 handbook: lines of
the form `x = <literal>;` or `xs = array1d(1..n, [...]);`, with the
standard separator lines (`----------`, `==========`, `%%%mzn-stat`)
stripped before parsing; `array1d` index sets must be 1-based. A solution
string assigns decision variables only; parameters keep their model-given
values. This is now *enforced* by the front door (`entriesOkB` in
`LeanFzn/FznCheck.lean`): an entry assigning a parameter name, an
undeclared name, or the same name twice is a malformed solution (the
dynamic checker `checkSolutionFull` alone accepted parameter
reassignments — fixed by classifying them out before the dynamic
phase). A string that tokenizes to something but contains no
`;`-terminated assignment line is likewise malformed
(`parseSolution` rejects it).

### A8. Truncated integer division and modulo

**Unspecified in prose detail:** the handbook says `int_div` is "rounded to
the value closest to zero (i.e., truncated)" but gives no sign-combination
table.

**Resolution (pinned by Gecode's `test_int_div.cpp`/`test_int_mod.cpp`):**
truncated semantics — `7 div 4 = 1`, `-7 div 4 = -1`, `7 div -4 = -1`,
`-7 div -4 = 1`; `7 mod 4 = 3`, `-7 mod 4 = -3`, `7 mod -4 = 3`,
`-7 mod -4 = -3`. Implemented with `Int.tdiv`/`Int.tmod` (Lean's `/` and
`%` are Euclidean and were wrong here); regression-tested by the ported
Gecode cases in `Tests/Gecode.lean`.

### A9. Boolean clause negative literals

**Ambiguity:** whether `bool_clause(as, bs)` requires a negative literal
`bs[j]` to be true or *false* to satisfy the clause.

**Resolution:** the handbook defines `∨ᵢ as[i] ∨ ∨ⱼ ¬bs[j]` — a negative
literal satisfies the clause when it is **false**. The original
implementation tested `bs[j] = true`, inverting the meaning; fixed and
pinned by Gecode's `bool_clause.cpp` reference output
(`bool_clause([], [x])` satisfied by `x = false`).

### A10. Solution strings assign output variables only

**Unspecified:** whether a solution string must assign *every* declared
variable or only those the solver prints (those annotated
`:: output_var` / `:: output_array`).

**Resolution:** real solver output assigns only the annotated output
variables; compiler-introduced variables are omitted. The checker
therefore completes the candidate store under variable initializers
(`completedStore` in `FznSolution.lean`): a variable absent from the
solution string takes its value from its declaration's initializer
(`array [1..3] of var 1..9: a = [x, y, z];`) when derivable. Explicit
solution entries are never overridden; a variable neither assigned nor
derivable still fails `allAssignedB`, preserving the checker's
completeness contract. The front door (`entriesOkB`) additionally
enforces that entries assign declared *variables* only and at most one
entry per name, per A7: the entry layer of the dynamic checker alone
let a parameter assignment override the parameter's model-given
value, so `entriesOkB` rejects such strings before the dynamic
phase.

## Predicate-semantics assumptions (G-series)

The FlatZinc specification defines the standard builtins briefly and
assigns no meaning at all to `fzn_*` solver predicates (A6). The
meanings formalized here therefore follow, in order of precedence:
(1) the MiniZinc 2.10.0 handbook pages (`lib-flatzinc-*.html` for
builtins, `lib-globals-*.html` for globals); (2) the stdlib
decompositions `share/minizinc/std/fzn_*.mzn` of the pinned tree;
(3) reference-solver behavior (Gecode) where both texts are loose.
Each entry below records a decision that went beyond a *literal*
reading of those sources. Per-predicate citations are in the module
docstrings (`FznStdLib.lean`, `FznGlobals/*`); correctness of each
entry is pinned by `Tests/Coverage.lean` (every name, both truth
values) and, where a reference solver was consulted, by
`Tests/Gecode.lean`.

### G1. Overall status of this section (was A6, generalized)

**Unspecified:** the FlatZinc specification assigns no meaning to
`fzn_*` solver predicates; several handbook glosses are loose about
shapes, partiality, and corner cases.

**Assumption:** each of the 138 supported `fzn_*` names and every
checkable builtin has a mathematical interpretation
(`PredicateInterpretation`, a Prop) and an executable Boolean twin,
related by a per-name agreement theorem `<name>_iff`. The five
out-of-fragment core names (`fzn_alternative`/`fzn_span` — opt;
`fzn_neural_net`/`fzn_piecewise_linear`/
`fzn_piecewise_linear_non_continuous` — float; plus every `_reif`,
float, and opt variant of other names) are listed in
`globalsUnsupported` and *reported*, never guessed. A wrong argument
shape makes every interpretation `False` and every twin `false`
(static checking is the separate `wellFormedB` layer, R8).

### G2. Truncated `int_div` / `int_mod`

See A8 (sign-combination table pinned by Gecode; `Int.tdiv`/`Int.tmod`).
Implemented in `FznStdLib.lean` (`int_div`, `int_mod`); a
division-by-zero argument makes the predicate false by the shape guard
`b ≠ 0 ∧ …`.

### G3. Boolean clause negative literals

See A9 (`bool_clause(as, bs)` = `∨ as ∨ ∨ ¬bs`; a negative literal
satisfies when *false*). Originally implemented inverted; the fix is
pinned by Gecode's `bool_clause.cpp`.

### G4. `int_pow` and `int_pow_fixed` at negative and zero exponents

**Under-specified:** the handbook defines `z = x^y` with `z` "constrained
to 1 div pow(x, abs(y)) when y < 0" but not the `x = 0, y < 0` case.

**Assumption:** `0 ^ negative` evaluates to `0` in the helper `intPow`
(Lean's `x ^ n : Int` with `n : Nat` cannot represent it); the
predicate forms exclude the case *implicitly* by the arithmetic — no
side condition is imposed, because the handbook imposes none.
`int_pow_fixed(x, y, z)` is the same equation with `y` a par argument
(3 arguments total; there is no modulus operand).

### G5. Set comparisons `set_le` / `set_lt` are lexicographic

**Under-specified:** the handbook says only "less than or equal" for
sets without defining the order.

**Assumption:** MiniZinc defines set comparison as the lexicographic
order of the *sorted lists of elements*. Implemented by
`IntSetValue.sortElems` (sorted, deduplicated canonical representation;
reversed intervals empty per R1) compared with `listLexLe`/`listLexLt`
(`FznStdLib.lean`, `FznSolution.lean`).

### G6. `*_nonshifted` element predicates coincide with the plain forms

**Under-specified:** the 2.0.2 `nonshifted` element variants are defined
by `redefinitions-2.0.2.mzn` in terms of the array's index set, which
the FlatZinc grammar here fixes to `1..n`.

**Assumption:** since every array of this fragment has index set
`1..n`, the nonshifted and shifted forms are the *same predicate*
(`e = xs[i]`, 1-based); they share one interpretation. If the grammar
ever generalizes index sets, these must be revisited.

### G7. All-different over sets is extensional

**Under-specified:** "pairwise different" for arrays of sets.

**Assumption:** `fzn_all_different_set` (and `all_equal_set`) compare
sets *extensionally* (`∀ k, Contains k ↔ Contains k`), via the
decidable `setEqB`; two representations of the same element set are
equal. Likewise all other set-typed arguments (e.g. counting families)
compare extensionally.

### G8. `all_different_except` and `_except_0` read as occurrence bounds

**Under-specified:** "pairwise different except for those values that
appear in the set S" (pairwise phrasing).

**Assumption:** the equivalent occurrence form is formalized: every
value *outside* `S` occurs at most once (`∀ v ∉ S, count ≤ 1`);
for `_except_0`, `S = {0}`. The twin drops `S`-elements (or zeros)
before the sort-based distinctness check.

### G9. `symmetric_all_different` as an involutive permutation

**Under-specified:** "all different, and for all i, xs[i]=j → xs[j]=i".

**Assumption:** formalized as distinctness plus the involutive index
condition `xs[xs[i]−1] = i+1` (1-based positions), which also forces
every value into `1..n`; the range conditions of the plain `inverse`
are *not* repeated (they follow).

### G10. Counting predicates orient toward the occurrence count

**Under-specified:** the deprecated `at_least/at_most/exactly` and the
`count_*` family are documented with solver phrasing ("constrains n
to be …"), leaving the inequality direction implicit.

**Assumption:** directions follow the stdlib decompositions exactly:
`count_geq(x, y, c)` is `count ≤ c`, `count_gt` is `count < c`,
`count_leq` is `c ≤ count`, `count_lt` is `c < count`, `count_eq`
`c = count`, `count_neq` `c ≠ count`; `at_least_int(n, x, v)` is
`n ≤ count`, `at_most_int` `count ≤ n`, `exactly_int` equality. The
set-valued variants count positions whose set *equals* (extensionally)
the value set. Recorded per-name in the `Counting.lean` docstring.

### G11. Global cardinality: closed vs low_up vs plain

**Under-specified:** the differences between the four gcc variants are
prose ("The elements of xs must take their values from cover").

**Assumption:** `global_cardinality` constrains only occurrences of
`cover` values; `_closed` adds `∀ j, xs[j] ∈ cover`; `_low_up` bounds
each `cover[i]` count by `low[i]`/`up[i]` (not closed, per the
deprecated-globals page); `_low_up_closed` adds the closedness. The
deprecated `at_least/at_most/exactly` int variants are their scalar
specializations.

### G12. Lex, sort, argsort: prefix order, permutation equality, stability

**Under-specified:** "lexicographic" for int arrays; `sort`'s output
uniqueness; `arg_sort`'s tie-breaking; `maximum_arg`/`minimum_arg`
tie-breaking.

**Assumption:** lex order is the standard first-difference order with
proper-prefix-smaller (`lexLess`); `sort(x, y)` is `y` a permutation
of `x` *and* non-decreasing (uniqueness follows mathematically, both
sides proved against `List.mergeSort`); `arg_sort(x, p)` requires `p`
to be a permutation of `1..n` that orders `x` non-decreasingly and
*stably* (ties by ascending index) — stability is the stdlib's
`fzn_arg_sort_int` decomposition; `maximum_arg`/`minimum_arg` return
the *least* index attaining the extremum.

### G13. Value-precedence family

**Under-specified:** "every occurrence of `after` must be preceded by
an occurrence of `before`" leaves the no-`after` case implicit.

**Assumption:** `value_precede(b, a, xs)`: every position holding `a`
has some strictly earlier position holding `b` (vacuously true when
`a` does not occur); `value_precede_chain(order, xs)` composes it
pairwise over consecutive order values; `seq_precede_chain(xs)` is
`value_precede(v−1, v)` for every `v ≥ 2` (the documented meaning of
the stdlib predicate).

### G14. Channeling: guarded and unguarded inverses

**Under-specified:** `inverse_in_range` vs `inverse` differ only in
prose about "if j is in the index set of ys".

**Assumption:** `inverse` imposes both directions unconditionally
(plus range conditions); `inverse_in_range` makes each direction an
*implication guarded by range membership*, so out-of-range values are
vacuous — strictly weaker. `int_set_channel` adds the range conditions
of its decomposition; `link_set_to_booleans(s, bs)` is `bs[i] = true ↔
i ∈ s` with 1-based `bs`. Recorded in `Channeling.lean`.

### G15. `arg_val` forces occurrence (partiality)

**Under-specified:** the user-level function is partial ("Note that
this function forces the value to occur").

**Assumption:** the `fzn_arg_val_{int,bool}` *predicates* are false
when the value is absent (the decomposition via `fzn_maximum_arg_bool`
behaves so); when present, the least 1-based index is returned.

### G16. `write` is total; `writes` is partial

**Under-specified:** position-out-of-range behavior.

**Assumption:** `fzn_write(x, i, v, y)` follows its total decomposition:
`y[j] = if j+1 = i then v else x[j]` for every `j` — an out-of-range
`i` leaves `y = x`. `fzn_writes(x, p, v, y)` is *false* when some
`p[j]` is out of range (the array access is undefined), and otherwise
assigns `y[p[j]] = v[j]` with untouched positions keeping `x`.

### G17. Overlap conventions in `diffn`, `disjunctive`, `geost_nonoverlap_k`

**Under-specified:** edge-touching and zero-duration cases.

**Assumption:** `diffn` allows rectangles that touch edges (open
intervals); `diffn_nonstrict` additionally allows degenerate
zero-area overlaps; `disjunctive` allows zero-duration tasks to
overlap anything; `disjunctive_strict` forbids all overlap including
zero-duration ones; `geost_nonoverlap_k` (the k-dimensional
restricted form) separates two objects when their projections are
disjoint on some axis, with the second/fourth argument arrays par.

### G18. `cumulative` checked at event points

**Under-specified:** the resource-usage function is quantified over
real time in the handbook.

**Assumption:** usage is piecewise constant between event points, so
checking task *start and end* times plus a `0 ≤ capacity` guard
(the guard captures negative resource amounts) is equivalent; both
directions proved in `cumulativeB_iff` (the equivalence argument is
in `PackSched.lean`).

### G19. `table_int` row shape and empty arrays

**Under-specified:** how the flat tuple array lays out rows; the empty
`xs` case.

**Assumption:** tuples are consecutive rows of `|xs|` values; a row
matches when every column agrees; `xs = []` is vacuously satisfied.
`fzn_table_bool` etc. are out of fragment (reported).

### G20. `if_then_else` without a true condition is vacuous

**Under-specified:** what the total (non-partial) if-then-else
decomposition means when no condition holds.

**Assumption:** the condition array and the branch array must have
equal length (a shape condition), and if no condition is `true` the
constraint imposes nothing beyond that (vacuous satisfaction); with
some `c[i] = true`, the *first* such `i` selects `y = x[i]`. This
follows the total decomposition; the partial variant
(`fzn_if_then_else_partiality`) is unsupported and reported.

### G21. `at_most1` is overlap ≤ 1, not disjointness

**Under-specified:** easily misread as pairwise near-disjointness.

**Assumption:** each pair of sets may *share at most one element*
(`card(xs[i] ∩ xs[j]) ≤ 1`), strictly weaker than disjointness;
recorded with the `.mzn` citation in `SetMath.lean`.

### G22. Set/math corner cases

**Assumption (each recorded at its definition in `SetMath.lean`):**
`array_set_union` of the empty array is the empty set;
`array_set_intersect` of the empty array is *false* (its `.mzn`
comment says "False if x is empty"); `sum_set` sums `weights[j]` over
positions `j` whose `values[j]` is in the selected set;
`sum_pred(idx, sets, cs, t)`: `t` is the sum of `cs[k]` over the
1-based indices `k` in the `idx`-th set, out-of-range `k` dropped,
and an out-of-range `idx` makes the predicate false; `range`/`roots`
treat array positions 1-based and make the image/preimage sets
*exactly* the hit positions (both directions, per the decomposition
strengthenings); sliding windows with `window_size ≤ 0` are vacuous
(no sub-sequence of that length exists).

### G23. Solution-output conventions relevant to predicate checking

A10 (output variables only, initializer completion) plus: `array1d`
index sets must be 1-based (A7), and the `setElems` enumeration of
interval sets is ascending (reversed intervals empty, R1). These are
the conventions the executable twins rely on when deciding extensional
set predicates by enumeration.

### G24. Reverse lex and 2D lex-family representations

**Under-specified:** upstream 2.10.0 has no `fzn_lex_greater_int`,
`fzn_lex_greatereq_int`, or chain-greater `fzn_` files; the 2D lex
predicates are declared over `array [int,int]` but FlatZinc syntax has
only 1D arrays.

**Assumption:** `fzn_lex_greater_int(xs, ys) ≡
fzn_lex_less_int(ys, xs)` and `fzn_lex_greatereq_int(xs, ys) ≡
fzn_lex_lesseq_int(ys, xs)` (argument swap, per the user-level
`lex_greater.mzn` decomposition). The chain/2D predicates
(`fzn_lex_chain_less_int`, `fzn_lex_chain_lesseq_int`, `fzn_lex2`,
`fzn_strict_lex2`, `fzn_lex_chain_lesseq_orbitope`) take a matrix
modelled as a *nested* array (a `List (List Int)`, one inner list per
column in FlatZinc order — a flat row-major array whose column count
must divide the outer length); adjacent columns are compared with
`lexLess`/`lexLesseq`; `lex2` additionally compares the transpose;
`strict_lex2` uses the strict variants; the orbitope's `_kind` is
0 = no extra constraint, 1 = every row sums to 1, 2 = every row sums
to ≤ 1. Chains over ≤ 1 column are vacuously true. Because
`array-literal` grammar cannot nest, real `.fzn` files cannot carry
these 2D arguments; the nested-array shape is a documented
extension of the fragment for completeness of the name inventory.

### G24a. Greater-direction chain/2D lex predicates

**Under-specified:** upstream 2.10.0 has no `fzn_` files for the
greater-direction chain/2D predicates (the compiler never emits them
without library rewrites), but the user-level definitions are
normative for their meaning.

**Assumption (per `lex_chain_greater.mzn`,
`lex_chain_greatereq.mzn`, `lex_chain_greatereq_orbitope.mzn`):**
each reverses the *column* index set (`index_set_2of2`) and delegates
to the less/lesseq version, so with the nested-array representation
of G24:

* `fzn_lex_chain_greater_int(cols) ≡ lexChainLess(cols.reverse)`;
* `fzn_lex_chain_greatereq_int(cols) ≡ lexChainLesseq(cols.reverse)`;
* `fzn_lex_chain_greatereq_orbitope(cols, kind) ≡
  orbitopeProp kind (cols.reverse)` with the same `_kind` codes
  (0 = none, 1 = every row sums to 1, 2 = every row sums to ≤ 1).

Reversal is column-only (row order is preserved); the arguments use
the same nested-array value-model extension as G24 (real `.fzn`
files cannot carry them).

### G25. `circuit` / `subcircuit`

**Under-specified:** self-loops and the empty array.

**Assumption:** `fzn_circuit(xs)` (per `fzn_circuit.mzn`): empty ⇒
true; otherwise `xs` is a permutation of `1..n` with no fixed point
(`xs[i] ≠ i`) forming one cycle (equivalently: iterating the
successor function from any index visits all n indices). 1-based
positions. `fzn_subcircuit(xs)`: `xs[i] = i` marks i out of the
circuit; the non-fixed positions must form one single cycle (the
all-fixed-points case, the empty subcircuit, is allowed); every
value is still in `1..n` and positions are 1-based.

### G26. `cumulatives` event-point semantics and machine indexing

**Under-specified:** the handbook's user-level overloads differ from
the `fzn_` layer's signature; loads are checked "over time".

**Assumption:** the FlatZinc signature is
`fzn_cumulatives(start, duration, resource, machine, bound :
array[int] of var int, is_upper_bound : bool, min_machine : int)`
(7 args; `fzn_cumulatives_decomp` has 6 — no `min_machine`), per the
pinned `fzn_cumulatives.mzn`. The resource sum of tasks on machine
`machine[i]` is checked only at event points (each task's start and
end), only when some task runs on that machine at that point (the
`cov` guards of Carlsson's decomposition): `is_upper_bound` ⇒ load ≤
`bound[machine[j]]`, else load ≥ `bound[machine[j]]`. Zero-duration
tasks execute at no instant (empty half-open interval) and trigger
no check. Machine values index `bound` 1-based (the `min_machine`
offset of the fzn layer is normalized away: machines are `1..m`).

### G27. `regular` family representations

**Assumption (per `fzn_regular.mzn`, `fzn_regular_nfa.mzn`,
`fzn_cost_regular.mzn`):** `fzn_regular(xs, Q, S, d, q0, F)` with `d`
the Q×S transition matrix flattened row-major (Q, S are the sibling
par ints): `xs` values must lie in `1..S`, states in `1..Q`, state 0
is the reserved sink (a `d[q,s] = 0` transition makes the run fail);
empty `xs` ⇒ `q0 ∈ F`. `fzn_regular_nfa` differs only in `d` being a
Q×S matrix of *sets* (nested-array columns of sets), `a[i+1] ∈
d[a[i], xs[i]]`. `fzn_cost_regular` adds the Q×S par cost matrix
(row-major) and `total_cost` = sum of the traversed transition costs
(0 for the empty run).

### G28. `mdd` family edge-list representation

**Assumption (per `fzn_mdd.mzn` etc.):** the signature is
`fzn_mdd(xs, N, level, E, from, label, to)`: `N` nodes (root 1,
true node 0), `level[n]` the level of node n, `E` edges with
`from[e] ∈ 1..N`, par-set `label[e]`, `to[e] ∈ 0..N` (0 = T). The
declarative reading: there is a root-to-T path whose edge labels
cover the variables level-by-level; concretely the *satisfying walks*
predicate — there exists a path `1 → … → 0` in the edge list such
that every `xs[i]` is in the label of the edge taken at level `i+1`
and the path's level sequence is strictly increasing. `fzn_mdd_nondet`
coincides (the P1/P4 determinism axioms only restrict the MDD, not
the satisfying-assignment relation). `fzn_cost_mdd(xs, N, level, E,
from, label, cost, to, total_cost)` (cost between label and to):
the satisfying-walks condition plus `total_cost` = the cost of *some*
satisfying walk (existential; the decomposition's longest-path
variables make total_cost the maximum, but any satisfying walk's
cost is accepted here — recorded as a deliberate relaxation, see
`Regular.lean` for the exact equivalence proof strategy).

### G29. Graph-family signatures and readings

**Assumption (per the pinned `fzn_*_int.mzn` decompositions):** all
graph predicates take par `from`/`to` edge arrays (1-based, nodes
`1..N`) plus `ns`/`es` var bool arrays; the *int* form's leading
`N`,`E` are not separate FlatZinc parameters here (they are recovered
from the array lengths, since the enum form has no such parameters;
both forms are accepted with the same tail shape). Readings:
`subgraph`: every selected edge has both endpoints selected;
`dag`: the selected subgraph is acyclic; `reachable`/`dreachable`:
the selected nodes are exactly those reachable from a var root
(undirected: each edge usable both ways, both directions selected
together); `tree`/`dtree`: the selected edges form an
arborescence rooted at a var root spanning exactly the selected
nodes (`dtree`: edges directed away from the root; `tree`:
undirected); `path`/`dpath`: the selected nodes form a simple path
from source to sink (both var); `bounded path` variants add
`weight_bound = Σ es[e]·w[e]`; `steiner`/`dsteiner` = tree +
weight bound (steiner with existential root); `wst`/`dwst` = tree
over *all* nodes + weight bound (wst without an explicit root);
`connected`/`dconnected` = reachable/dreachable with existential
root. Declared but unprovable-in-fragment corner cases (edges
outside `1..N`) make the predicate false.

### G30. `geost` family and `diffn_k` representation

**Assumption (per `fzn_geost.mzn`):** `fzn_geost(k, rect_size,
rect_offset, shape, xs, kind)`: `rect_size`/`rect_offset` are R×k
matrices flattened row-major (R rectangles, k given as the first par
int), `shape` an array of par sets of rectangle indices, `xs` the
O×k matrix of object origins (flat), `kind` the object shape
selector. Two objects overlap iff some shape-pair of their kinds has
two rectangles not separated on any axis (open-interval overlap:
touching is allowed, per `fzn_geost_nonoverlap_k`). `geost_bb`
adds per-dimension bounds over every possibly-used shape's
rectangles; `geost_smallest_bb` additionally requires each of the
2k boundaries to be touched. `fzn_diffn_k(box_posn, box_size)` /
`fzn_diffn_nonstrict_k(...)`: matrices as *nested* arrays (rows =
boxes; same G24 caveat: real `.fzn` cannot carry them), pairwise
non-overlap resp. non-overlap with zero-size boxes free.
`fzn_diffn_nonoverlap_k(x1, w1, x2, w2)`: 1D per-axis lists,
separated on at least one axis.

### G31. `writes_seq` last-write-wins; `span`/`alternative` stay unsupported

**Assumption (per `fzn_writes_seq.mzn`):** `fzn_writes_seq(I, P, V,
O)`: for every position i, `O[i] = V[j]` for the *largest* j with
`P[j] = i`, or `O[i] = I[i]` if no such j (the initial array
provides defaults; `I`, `O` are the same length). `fzn_span` and
`fzn_alternative` remain in `globalsUnsupported`: their signatures
(per `fzn_span.mzn`, `fzn_alternative.mzn`) require `var opt int`
starts (`occurs`/`absent` on `span_start` and every `start[i]`),
which the fragment's value model does not carry — implementing them
would require optional-variable semantics (PLAN item for opt
support). (The G20 entry's report of
`fzn_if_then_else_partiality` as unsupported is superseded: it is
now supported — see G32.)

### G32. `if_then_else_partiality` definedness

**Assumption (per `fzn_if_then_else_partiality.mzn`):**
`fzn_if_then_else_partiality(c, def, b)`: with `d[i]` marking that
case i is the first whose condition holds, `b ↔ def[first true i]`
(and `b = false` when no condition holds — the d-chain then forces
all `d[i]`... every `c[i] ∧ d[i]` is false, so the b-implications
are vacuous and `b = false` is derivable from the second family:
`d[i] ∧ c[i] ∧ def[i] → b` never fires. We read the predicate as:
the selected branch is the first true condition; b is the
definedness of the result; `b` must equal the definedness of the
selected branch; with no true condition, `b` is forced false).

### G33. `fzn_neural_net` and `fzn_piecewise_linear*` stay unsupported

These require `var float` arrays (neural_net inputs/outputs) or
`var float` scalars (piecewise_linear's x, y) — outside the
integer/Boolean/set fragment until step 3 (float support) decides the
numerical model. They remain in `globalsUnsupported`.

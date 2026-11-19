# Consequential FlatZinc Specification Assumptions

This document records only unresolved choices for which a different decision
changes accepted inputs, satisfying assignments, or the checker's treatment of
a candidate solution. It distinguishes ambiguities in FlatZinc from choices
in the checker interface, which FlatZinc does not specify.

The reference is MiniZinc 2.10.1 at immutable commit
`c3448c48e7f05f13805616cfd1b9e94972eef58c`; see
[minizinc-2.10.1/README.md](minizinc-2.10.1/README.md). The entries below
concern the integer/Boolean/set fragment. Float-specific decisions are recorded
in [flatzinc_float_specification.md](flatzinc_float_specification.md).

An assumption belongs here only if:

* the reference leaves a consequential question unresolved;
* the project selects a definite interpretation or interface policy; and
* an alternative has an observable effect, demonstrated below.

Specified predicate meanings, equivalent mathematical formulations, proof
techniques, supported-name inventories, version pinning, and implementation
bugs are not assumptions. Predicate definitions and their source citations
belong in `LeanFzn/Semantics/StdLib.lean` and the `LeanFzn/Semantics/Globals/*` modules;
the inventory belongs in
[minizinc-2.10.1/predicates_and_globals_report.md](minizinc-2.10.1/predicates_and_globals_report.md).
Agreement between a Boolean checker and its project-defined proposition does
not, by itself, establish agreement with the upstream specification.

The retained R/A identifiers preserve references from existing source comments.
Removed identifiers are historical references, not additional assumptions.

## R5. Forward references within variable declarations

**Unresolved question.** FlatZinc specifies the order of item categories
(predicates, parameters, variables, constraints, solve), but does not explicitly
settle whether a variable initializer may refer to a variable declared later
within the variable-declaration block.

**Decision.** Resolve variable names against the completed global declaration
environment. Forward references within that block are allowed; an undeclared
name is a static error. This decision does not relax the required order of
item categories.

**Chosen-policy example and rationale.** A generator may emit an alias before
the variable it refers to:

```fzn
var 0..9: result = source;
var 0..9: source;
constraint int_eq(source, 4);
solve satisfy;
```

The completed environment gives both names type `int`; the initializer adds
`result = source`, so the unique assignment is `result = source = 4`.
Moving the `source` declaration before `result` gives the same assignments.
The choice makes declaration order within this block irrelevant to name
resolution, avoiding an extra ordering requirement on model generators.
The constraint determines the assignment mathematically; it does not cause
initializer completion to infer `source` from an incomplete candidate.

**Alternative and effect.** A declaration-before-use rule rejects the following
model; the chosen rule admits it, with `x = y = 1`:

```fzn
var 0..1: x = y;
var 0..1: y = 1;
solve satisfy;
```

**Implementation.** `Model.staticEnv` in `LeanFzn/Semantics/Model.lean` looks up
names across all declarations. Initializer completion in
`LeanFzn/Checker/Solution.lean` can propagate values through forward references.

## R6. Cyclic aliases and inconsistent variable initializers

**Unresolved question.** The prose describes variable initializers as fixing a
value or creating an alias. It does not give a complete treatment of cyclic
aliases or specify whether a type-correct fixed value outside the declared
domain is an invalid model or an unsatisfiable one.

**Decision.** Interpret each variable initializer as an equality that must hold
alongside the variable's domain. Alias cycles are not rejected merely because
they are cyclic. A type-correct initializer outside the domain makes the model
unsatisfiable. Type mismatches remain static errors.

**Chosen-policy example and rationale.** Domain restrictions remain active
when two variables are aliases:

```fzn
var 0..2: x;
var 1..3: y = x;
solve satisfy;
```

The equality and both domains hold together, yielding exactly
`x = y = 1` and `x = y = 2`. No declaration overwrites the other variable's
domain. If the domains were `0..0` and `1..1`, the same rule would yield no
assignment. Likewise, fixing `var 0..0: x = 1;` imposes incompatible
requirements `x = 0` and `x = 1`. Treating all these cases as conjunctions of
equalities and domains gives one uniform satisfaction rule, including cycles
and inconsistent fixed values.

**Alternative and effect.** An acyclic-alias requirement rejects:

```fzn
var 0..1: x = y;
var 0..1: y = x;
solve satisfy;
```

Under the chosen interpretation this model has two assignments:
`x = y = 0` and `x = y = 1`. Checking such an assignment still requires values
for the cycle; initializer completion cannot invent a value for an unassigned
cycle.

Similarly, `var 0..1: x = 2; solve satisfy;` has no satisfying assignment under
the chosen interpretation. Rejecting it during static validation instead
changes its result category from unsatisfiable to invalid; it does not create
or remove any satisfying assignment.

The equality is semantic: set values are equal when they have the same
elements. With `var set of 1..3: s = {1,2,3};`, the solution value `s = 1..3`
(the form MiniZinc prints for a contiguous set) satisfies the initializer, as
does `s = {3,2,1}`; comparing representations would reject both.

**Implementation.** Initializer typing is checked in
`LeanFzn/Semantics/Model.lean` (`Value.SemEq` defines the equality); initializer
equalities and domain membership are checked by `LeanFzn/Checker/Solution.lean`
(`semEqB`).

## R11. Exact interpretation of string escapes

**Unresolved question.** FlatZinc describes strings as having C syntax without
specifying an exact escape repertoire or the treatment of invalid byte
sequences. Different readings can accept different annotation strings or
decode them differently.

**Decision.** Use the MiniZinc lexical rules recorded by the project:
`\"`, `\\`, `\n`, `\t`, one or two hexadecimal digits after `\x`, and one to
three octal digits. Reject unknown escapes, physical newlines, unterminated
strings, and byte escapes that do not decode to valid UTF-8. The last rule
consolidates the former A2 entry.

**Chosen-policy example and rationale.** Under the intended policy, the
annotation string `"row\t\x41"` decodes to `row`, a tab, and `A`. The string
`"\101"` also decodes to `A`, so the hexadecimal and octal spellings give
the same annotation value. By contrast, `"\xFF"` is rejected because the
single decoded byte `FF` is not valid UTF-8. Explicit decoding and validation
give annotation consumers a definite Unicode string rather than leaving
escape interpretation to each consumer.

**Alternative and effect.** A permissive reader can accept `"\q"`, whereas the
chosen policy rejects it. A reader that leaves hexadecimal escapes undecoded
produces a different annotation string for `"\x41"` than a reader that decodes
it to `"A"`.

This choice affects lexical acceptance and decoded annotation values. Strings
occur in annotations in this fragment, so it does not currently change core
assignment satisfaction.

Every escape outside this list is rejected, including `\(` (MiniZinc string
interpolation, also excluded by the vendored grammar's `<string-contents>`), a
backslash before a physical newline, and octal escapes above `\377`.

**Implementation.** `lexEscape` and `lexString` in `LeanFzn/Parser/Lexer.lean`.
**Physical linebreaks in a string body.** The vendored grammar explicitly
excludes physical LF from `<string-contents>`. The project's declared strict
linebreak policy additionally rejects raw CR. This is an explicit policy choice,
not a claim that the upstream LF character class itself includes CR. Escaped
linebreaks remain available: `\n`, `\x0A` and `\12` encode LF; `\t`, `\x09`
and `\11` encode tab; `\x0D` and `\15` encode CR. This restricts physical
source characters, not decoded contents.

The former lexer rejected LF but accepted raw CR inside a quoted string. The
implementation now rejects both, and `Tests/Parser/LexicalSpec.lean` checks that
regression together with escaped-linebreak and Unicode cases.

`LeanFzn.Parser.Lexical.tokenize_correct` now proves the lexer sound and complete
against the independent character-level relation in `Parser/Lexical.lean`.
`parseModel_iff_sourceGrammar` composes it with the existing token grammar and
preserves the exact AST. The older `ValidFlatZinc` definition is still
lexer-relative; the new theorem does not use it as its independent contract.
This certification establishes the declared policy, not equivalence to every
upstream lexical convention.

## A1. Integer capacity and overflow

**Unresolved question.** The solver interface does not prescribe one universal
integer width or overflow policy for all solvers.

**Decision.** Core semantics use unbounded mathematical integers (Lean `Int`).
Arithmetic never silently wraps. A bounded solver interface must impose its
representability restrictions explicitly.

**Chosen-policy example and rationale.** The model

```fzn
var int: z;
constraint int_plus(2147483647, 1, z);
constraint int_gt(z, 2147483647);
solve satisfy;
```

has the assignment `z = 2147483648`: the addition produces the mathematical
sum, which satisfies the strict inequality. Using `Int` keeps this meaning
independent of a solver's machine word size and preserves ordinary integer
arithmetic across the boundary. Representability can then be checked
separately when connecting to a bounded solver.

**Alternative and effect.** For an interface using signed 32-bit integers,
`int_plus(2147483647, 1, z)` cannot produce a representable mathematical result.
The unbounded interpretation requires `z = 2147483648`; a wrapping
interpretation instead requires `z = -2147483648`; a checked bounded interface
rejects the operation or input. These policies therefore differ in accepted
values or satisfying assignments.

**Implementation.** Integer values and arithmetic in `LeanFzn/Syntax/AST.lean` and
`LeanFzn/Semantics/StdLib.lean` use Lean `Int`.

## A7/A10. Checking a candidate with omitted variables

**Unresolved question.** This is a checker-interface choice, not an ambiguity
in what a complete FlatZinc assignment means. Solver output may omit internal
variables; the specification does not prescribe how an independent checker
must reconstruct their values from a projected candidate.

**Decision.** Start with model parameter values and the supplied variable
entries. Add omitted variable values only when their declaration initializers
can be evaluated from values already known, repeating to a fixed point.
Explicit entries are never overwritten. After completion, every declared
variable must be assigned before the candidate can be accepted. The checker
does not search for an existential extension through arbitrary constraints.

Entries must name declared variables and may assign each name at most once.
This preserves the existing A7 input contract; rejecting parameter
reassignments protects their model-defined values rather than selecting an
alternative parameter semantics.

**Chosen-policy example and rationale.** Omitted aliases and arrays can be
reconstructed from a supplied scalar:

```fzn
var 0..9: x :: output_var;
var 0..9: alias = x;
array [1..2] of var 0..9: pair = [alias, x];
solve satisfy;
```

For candidate `x = 4;`, completion adds `alias = 4` and `pair = [4,4]`;
all variables are then assigned and the initializer equalities hold.
This accommodates omitted values already determined by declarations without
requiring the checker to run a constraint search. If the candidate explicitly
also supplies `alias = 5;`, completion preserves that value and the subsequent
equality check rejects the candidate. Preserving explicit entries ensures
completion cannot repair an incorrect submitted assignment into a valid one.

**Alternatives and effects.** Requiring every variable to be explicitly supplied
rejects a candidate that the chosen policy can complete:

```fzn
var 0..1: x :: output_var;
var 0..1: y = x;
solve satisfy;
```

For candidate `x = 1;`, initializer completion supplies `y = 1`.

Conversely, searching for a satisfying extension accepts some candidates that
the current completion policy cannot accept:

```fzn
var 0..1: x;
var 0..1: y :: output_var;
constraint int_eq(x, y);
solve satisfy;
```

For candidate `y = 1;`, an existential checker can choose `x = 1`, but initializer
completion leaves `x` unassigned. Failure to complete this candidate does not
establish that the model, or the projected candidate, is unsatisfiable.

Thus the contract is **complete assignments, allowing initializer-derived
omissions**, rather than unrestricted acceptance of output-variable-only
solutions.

A candidate is one solution. Solver output that contains several solutions,
each ended by a `----------` line, is split into its solutions and each is
checked separately; the `check` command accepts the output only if every
solution is accepted.

**Implementation.** `completedStore` and `allAssignedB` in
`LeanFzn/Checker/Solution.lean` (`completedStore_entry` and
`completedStore_paramHonest` prove that explicit entries and parameter values
are preserved); entry validation through `entriesOkB` and solution splitting
through `splitSolutions` in `LeanFzn/Checker/Check.lean`.

## R27. Scalar parameter declarations

**Unresolved question.** The vendored grammar's `<par-decl-item>` admits only
array parameters, while the prose of the same specification shows scalar
declarations such as `bool: beer_is_good = true;` and describes `<par-expr>` as
"a basic integer, float or bool literal, or a set or array of such literals".

**Decision.** Accept scalar parameter declarations
`<basic-par-type> ":" <var-par-identifier> "=" <basic-literal-expr> ";"` in
addition to the grammar's array form.

**Chosen-policy example and rationale.** The model

```fzn
int: k = 3;
var 0..9: x;
constraint int_le(x, k);
solve satisfy;
```

is accepted and has the assignments `x = 0` to `x = 3`. MiniZinc-generated
FlatZinc contains such declarations, and the prose examples use them.

**Alternative and effect.** A reader following only the BNF rejects this model
as a syntax error.

**Implementation.** `ParDeclItem.basic` in `LeanFzn/Syntax/AST.lean`,
`GrParDeclItem.basic` in `LeanFzn/Parser/Grammar.lean`, and `parseParDeclItem` in
`LeanFzn/Parser/Parser.lean`.

## R28. Nested arrays in annotation arguments

**Unresolved question.** The vendored grammar allows only basic annotation
expressions inside an annotation array (`"[" [ <basic-ann-expr> "," ... ] "]"`),
so `[[1], [2]]` is not derivable; the specification does not say whether
annotation arguments may nest arrays.

**Decision.** Allow annotation arrays to contain any annotation expression,
including further arrays.

**Chosen-policy example and rationale.** `solve :: a([[1], [2]]) satisfy;` is
accepted. Annotations carry no semantics in this fragment, so accepting a
superset of the grammar here cannot change any satisfying assignment, and it
avoids rejecting solver-specific annotations.

**Alternative and effect.** A reader following only the BNF rejects the model
as a syntax error.

**Implementation.** `AnnExpr.array` in `LeanFzn/Syntax/AST.lean` and
`GrAnnExpr.array` in `LeanFzn/Parser/Grammar.lean`.

## R29. Spelling of the index-set lower bound

**Unresolved question.** The grammar writes `<index-set> ::= "1" ".." <int-literal>`
with the literal `"1"`, but integer literals have several spellings
(`1`, `01`, `0x1`, `0o1`).

**Decision.** Accept any integer literal whose value is 1 as the lower bound.

**Chosen-policy example and rationale.** `array [0x1..2] of int: a = [1, 2];`
is accepted. The parser works on tokens, and every spelling denotes the same
index set.

**Alternative and effect.** A character-level reading rejects `0x1..2` and
`01..2`; no satisfying assignment changes.

**Implementation.** `GrIndexSet` in `LeanFzn/Parser/Grammar.lean` matches the
token `intLit 1`; `parseIndexSet` in `LeanFzn/Parser/Parser.lean` checks the
value.

## G-series: evaluation-time decisions beyond a literal reading

The entries below record the G-series decisions cited by
`LeanFzn/Semantics/StdLib.lean`: how the evaluator settles operator
corner cases the handbook leaves open. Each was checked against
MiniZinc 2.10.1 by a committed ground model under
`Tests/Upstream/assumptions/` (see that directory's README).

## G2. Truncated `int_div`/`int_mod` and the zero divisor

**Unresolved question.** The handbook states `int_div(x,y,z)` constrains
`x / y = z` "where z is rounded to the value closest to zero (i.e.,
truncated)" and `int_mod(x,y,z)` constrains `x % y = z`
(`minizinc-2.10.1/lib-flatzinc-int.html`), but it fixes neither the sign of a
negative remainder beyond truncation nor how either predicate behaves with
`y = 0` — division by zero is an evaluation error in MiniZinc, not a
satisfying assignment.

**Decision.** `int_div` and `int_mod` mean Lean's truncating division and
modulo, `c = Int.tdiv a b` and `c = Int.tmod a b`, and both are guarded by
`b ≠ 0`. With truncation the quotient rounds towards zero and the remainder
takes the sign of the dividend: `(-7) div 2 = -3`, `(-7) mod 2 = -1`,
`7 div (-2) = -3`, `7 mod (-2) = 1`. For `b = 0` the predicate is **false**
for every `c`, so a model that divides by zero has no satisfying assignment
under the checker (fail closed) instead of an undefined value.

**Chosen-policy example and rationale.** The ground model
`Tests/Upstream/assumptions/int_div.mzn` has MiniZinc evaluate all four sign
combinations (and `1 div 2`, `-1 div 2`); MiniZinc 2.10.1 prints

```
-7 div 2 = -3
-7 div -2 = 3
7 div 2 = 3
7 div -2 = -3
13 div 5 = 2
-13 div 5 = -2
13 div -5 = -2
-13 div -5 = 2
1 div 2 = 0
-1 div 2 = 0
```

which is exactly `Int.tdiv` on the same inputs. `int_mod.mzn` evaluates the
companion operator and prints `-7 mod -2 = -1`, `-13 mod 5 = -3`,
`-13 mod -5 = -3` and the rest, exactly `Int.tmod`. Matching the reference's
truncation (rather than floor or Euclidean division) keeps the checker's
acceptance identical to what a MiniZinc user observes; the example values are
the reference's own.

**Alternative and its effect.** Floor division would give `-7 div 2 = -4` and
`-7 mod 2 = 1`, so `int_div(-7, 2, -4)` would be accepted by a floor policy
and rejected here, and `int_div(-7, 2, -3)` vice versa; a pre-truncation
reading would instead accept `int_div(-7, 2, -3.5)`, which is not
representable. For the zero divisor, an unguarded reading would leave the
result unconstrained: `int_div(1, 0, c)` would then be satisfiable for every
`c`, and a model whose only constraint divided by zero would spuriously have
solutions. MiniZinc itself supplies no value there — `-7 div 0` is rejected
with "result of evaluation is undefined: division by zero"
(`Tests/Upstream/assumptions/int_div_zero.mzn`) — so the `b ≠ 0` guard is the
only reading that agrees on the defined fragment and fails closed on the
undefined one.

**Implementation.** `int_div`/`int_mod` in `stdInterp` of
`LeanFzn/Semantics/StdLib.lean` (the `| "int_div" =>` and `| "int_mod" =>`
cases: `b ≠ 0 ∧ c = Int.tdiv a b` and `b ≠ 0 ∧ c = Int.tmod a b`) and their
executable twins (`stdInterpB`, `FznSolution.lean`'s `interpB`); the
`builtin_int_div_iff`/`builtin_int_mod_iff` agreement theorems are in
`StdLib.lean`. Upstream tests: `Tests/Upstream/assumptions/int_div.mzn`,
`int_mod.mzn`, `int_div_zero.mzn`, replayed by
`Tests/Upstream/assumptions/run.sh`.

## G4. `int_pow` at corner exponents, including the excluded `0 ^ negative`

**Unresolved question.** The handbook's sentence for `int_pow(x,y,z)` is
"Constrains z = x^y, z is constrained to 1 div pow(x, abs(y)) when y < 0"
(`minizinc-2.10.1/lib-flatzinc-int.html`). It does not say whether `0 ^ 0` is
defined, and it leaves the value of `x ^ negative` to a truncated division
whose divisor `pow(x, abs y)` is `0` when `x = 0`, an undefined expression.

**Decision.** `intPow x y` is `x ^ y.toNat` for `y ≥ 0` and
`Int.tdiv 1 (x ^ (-y).toNat)` for `y < 0`, so positive exponents are the usual
power, `x ^ 0 = 1` for every `x` (including `0 ^ 0 = 1`), and a negative
exponent is the truncated `1 div x^|y|`: `2 ^ (-1) = 0`, `1 ^ (-1) = 1`,
`(-1) ^ (-1) = -1`, `(-2) ^ (-3) = 0`, `(-3) ^ 2 = 9`. The case `y < 0` with
`x = 0` is **excluded** by the side condition `y < 0 → x ≠ 0`, so
`int_pow(0, -1, z)` is false for every `z`; `int_pow_fixed` has the identical
reading. The `pow` operator of the test models is MiniZinc's own; the corner
values were checked with `pow`, which is what the FlatZinc `int_pow` constraint
implements.

**Chosen-policy example and rationale.** `Tests/Upstream/assumptions/int_pow.mzn`
evaluates all twenty corner cases; MiniZinc 2.10.1 prints, among them,

```
(0) ^ (0) = 1
(-1) ^ (0) = 1
(3) ^ (2) = 9
(-3) ^ (2) = 9
(1) ^ (-1) = 1
(-1) ^ (-1) = -1
(2) ^ (-1) = 0
(-7) ^ (-2) = 0
```

which is exactly `intPow` on the same inputs. The exponents are parenthesised
so the reading cannot be confused with MiniZinc's unary-minus precedence
(`-3 ^ 2` parses as `-(3 ^ 2)`); the `pow(x, y)` call is used so the printed
base is unambiguous. `0 ^ negative` cannot be evaluated — MiniZinc reports
"negative power of zero is undefined" (`int_pow_zero_negative.mzn`) — and the
side condition turns that undefined value into a false predicate, which is the
only choice consistent with G2's guard on `1 div 0`. Matching these values
keeps `int_pow` acceptance identical to the reference, including the
truncated-to-zero results that distinguish it from an exact rational power.

**Alternative and its effect.** An exact-rational reading would give
`2 ^ (-1) = 1/2`, so such a policy would accept `int_pow(2, -1, 1/2)` — not
representable — and reject `int_pow(2, -1, 0)`; the truncated policy accepts
`0`. A policy leaving `0 ^ negative` unconstrained would make
`int_pow(0, -1, z)` satisfiable for every `z`, whereas the side condition
makes it unsatisfiable; MiniZinc gives no value there, so failing closed is
the only reading that does not invent one. Treating `0 ^ 0` as undefined
instead of `1` would reject `int_pow(0, 0, 1)`, which MiniZinc accepts.

**Implementation.** `intPow` and the `| "int_pow" =>` / `| "int_pow_fixed" =>`
cases of `stdInterp` in `LeanFzn/Semantics/StdLib.lean`
(`(y < 0 → x ≠ 0) ∧ z = intPow x y`), their `stdInterpB`/`interpB` twins and
the `builtin_int_pow_iff`/`builtin_int_pow_fixed_iff` agreement theorems. The
signature row for `int_pow_fixed` (`stdSig`) restricts the exponent to a `par`
argument. Upstream tests: `Tests/Upstream/assumptions/int_pow.mzn` and
`int_pow_zero_negative.mzn`, replayed by `run.sh`.

## G5. `set_le`/`set_lt` as lexicographic order on the sorted, deduplicated elements

**Unresolved question.** The handbook defines `set_le(s,t)` and `set_lt(s,t)`
as "lexicographic order of the sorted lists of elements"
(`minizinc-2.10.1/lib-flatzinc-set.html`) but a FlatZinc set value can be
written as an enumeration whose order and repetition are not canonical, and
as a reversed interval, so "the sorted list of elements" needs a definite
normal form before it can order a pair.

**Decision.** Each set is normalised to its sorted, deduplicated element list
before comparison: an enumeration is de-duplicated and sorted, an interval
`lo..hi` is its increasing element list, and a reversed interval is empty.
`set_le` is lexicographic `≤` and `set_lt` is lexicographic `<` of those two
lists (a proper prefix is less, then the first differing element decides; `<`
is `≤` and not `≥`). So `{1,3} ≤ {1,4}`, `{1,3} < {1,3,9}`, `{} < {2}`,
`{5} ≰ {1,9}`, and sets that differ only in a larger element are still
ordered — unlike the subset order. The reified variants return the truth of
the same comparison.

**Chosen-policy example and rationale.**
`Tests/Upstream/assumptions/set_le_lt.mzn` prints, per pair, `(s ≤ t, s < t)`;
MiniZinc 2.10.1 prints

```
{1,3} <= {1,4} : true true
{1,3} <= {1,3} : true false
{1,3} <= {1,3,9} : true true
{1,9} <= {1,3,9} : false false
{} <= 2..2 : true true
2..2 <= {} : false false
5..5 <= {1,9} : false false
1..3 <= 1..2 : false false
```

and `set_le_lt_duplicates.mzn` confirms that `{4,1,4,3}` (an enumeration with
a repeat, out of order) orders exactly as `{1,3,4}`: `{4,1,4,3} ≤ {1,3,9}` and
`{4,1,4,3} < {1,3,9}` are both true. These are exactly the Lean results. The
normal form is what makes the comparison total and well defined on the set
values the parser produces, and the empty list is the least element, so the
order is total.

**Alternative and its effect.** Comparing the elements in written order, or
comparing by subset, would change the acceptances: `{1,9} ⊆ {1,3,9}` is true,
so a subset policy would accept `set_le({1,9}, {1,3,9})`, whereas the
lexicographic reading (and MiniZinc) rejects it (`false`). An order-sensitive
reading would order `{4,1,3}` differently from `{1,3,4}`, so
`set_le({4,1,3}, {1,3,9})` would be decided by the interior order rather than
by the elements, contradicting MiniZinc's `true`. The empty set being the
least is required for `{} ≤ {2}` to hold, as MiniZinc confirms.

**Implementation.** `IntSetValue.sortElems`, `listLexLe`/`listLexLt`,
`lexLeB`/`lexLtB` and the `| "set_le" =>` / `| "set_lt" =>` (and `_reif`)
cases of `stdInterp` in `LeanFzn/Semantics/StdLib.lean`; the executable twins
are `lexLeB`/`lexLtB` with the agreement theorems `lexLeB_iff`/`lexLtB_iff`
and the reified agreement lemmas in `LeanFzn/Semantics/Evaluation.lean`.
Upstream tests: `Tests/Upstream/assumptions/set_le_lt.mzn` and
`set_le_lt_duplicates.mzn`, replayed by `run.sh`.

## G6. `*_nonshifted` element variants coincide with the plain forms on `1..n` arrays

**Unresolved question.** MiniZinc 2.10.1 defines the `_nonshifted` element
constraints by *shifting* the index:
`array_var_int_element_nonshifted(idx, xs, y)` is
`array_var_int_element(idx - (min(index_set(xs)) - 1), array1d(xs), y)` (and
likewise for the bool and set variants; the definition lives in the solver's
`share/minizinc/std/redefinitions-2.0.2.mzn`, not in the handbook page). The
shift depends on the array's index set, which the project's FlatZinc arrays do
not carry: every array the checker accepts is indexed `1..n`.

**Decision.** On `1..n` arrays `min(index_set(xs)) - 1 = 0`, so the shift is
the identity and the `_nonshifted` variants mean exactly their plain forms:
`valuesGet1 xs i` in `LeanFzn/Semantics/StdLib.lean`. The checker's arrays are
all `1..n` (the `valuesGet1` 1-based accessor). An index outside `1..n`
selects nothing and the predicate is false, exactly as for the plain form.

**Chosen-policy example and rationale.** `Tests/Upstream/assumptions/element_nonshifted.mzn`
asks MiniZinc's own redefinition to evaluate the nonshifted variant on the
`1..n` array `[10, 20, 30]` at index `2`; MiniZinc 2.10.1 prints `20`, the
same value the plain `array_var_int_element(2, [10,20,30], 20)` gives and the
value `valuesGet1` computes. On a `1..n` array the two forms are therefore
interchangeable, which lets the interpreter give them one case.

**Alternative and its effect.** The simplification is *only* licensed for
`1..n` arrays. On the array `5..7` of `[10, 20, 30]` the shift is
`min(index_set) - 1 = 4`, so the nonshifted index `2` selects nothing;
`element_nonshifted_shift.mzn` (which asks for `ns(2, [10,20,30]@5..7, 20)`) is
`=====UNSATISFIABLE=====`, whereas the plain form at `2` on the same array
would be in range. Treating the two forms as identical for arbitrary index
sets would therefore accept an assignment MiniZinc rejects; because the
project never builds such arrays (they are `1..n` by construction), the
consequence is confined to models the checker does not admit.

**Implementation.** The `| "array_var_int_element_nonshifted" =>`,
`| "array_var_bool_element_nonshifted" =>` and
`| "array_var_set_element_nonshifted" =>` cases of `stdInterp` in
`LeanFzn/Semantics/StdLib.lean` (each `valuesGet1 xs i = some (.int e)` /
`.bool e` / extensional set equality, identical to the plain case), their
`stdInterpB`/`interpB` twins (for the set variant in
`LeanFzn/Semantics/Evaluation.lean`), and the `builtin_*_nonshifted_iff`
agreement theorems. Upstream tests:
`Tests/Upstream/assumptions/element_nonshifted.mzn` and
`element_nonshifted_shift.mzn`, replayed by `run.sh`.

## Solution assignment syntax and checker interface

The solution language for the supported non-float fragment follows the pinned
MiniZinc 2.10.1 handbook §4.3.3.1. Its independent, value-sensitive definition is
`SolutionGrammar` in `LeanFzn/Checker/SolutionGrammar.lean`; `ValidSolution`
means that some sequence of entries has a derivation in that grammar. Neither
predicate invokes the solution parser. As with `ValidFlatZinc`, lexical
conventions are supplied by the shared lexer, including comments, whitespace,
reserved words and integer spellings.

An assignment body is a sequence of complete `name = value;` assignments.
Scalar values are Booleans, integers, integer ranges or enumerated integer
sets. Flat arrays may be written as `[literal, ...]` (the current handbook
format) or `array1d(1..n, [literal, ...])` (the handbook examples and historical
solver format). The wrapper's upper bound must equal the element count;
an empty wrapped array has index set `1..0`. Commas separate set members
and array elements at their own nesting level. Trailing commas, missing
separators, nested arrays and unterminated assignment suffixes have no grammar
production. An empty or comment-only body denotes no assignments; whether it
satisfies a particular model is a separate semantic question.

The checker consumes one solution at a time. `splitSolutions` handles streams;
`stripSeparators` removes standard solution/status separator lines before the
assignment-body parser runs. Syntax correctness is distinct from the
model-specific gate for declared variable names, parameter reassignment and
duplicate entries. The main checker correctness theorems use grammatical
entries and their completed stores, rather than defining syntactic validity
by parser success.

Emitter round trips require printable, nonreserved FlatZinc names and a store
whose values fit each declaration. Arbitrary hand-built AST strings need not
be legal identifiers, so semantic model well-formedness alone cannot supply
that lexical premise. The value-shape premise follows from `SatisfiesDyn`.
The round trip preserves scalar values and array positions, and compares sets
extensionally because output sorts/deduplicates enumerations. Array output
uses the actual element count, including `1..0` for every empty array.
Canonical output places whitespace between tokens; this has no effect on the
handbook syntax or the decoded values.

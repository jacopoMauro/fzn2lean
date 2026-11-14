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
The lexer is not covered by the parser recognition theorem: `ValidFlatZinc`
is defined over the tokens this lexer produces.

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

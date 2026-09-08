# FlatZinc Specification Ambiguities and Resolutions

Each point where the pinned specification was ambiguous, silent, or
contradictory, and the decision taken. The normative reference is MiniZinc
2.10.0, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`); the general MiniZinc language
specification resolves semantic notions that FlatZinc inherits but does not
repeat. This project formalizes the integer/Boolean fragment (no floats).

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
unterminated strings are rejected. (The lexer does not fully implement this
yet.)

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

# LeanFzn — FlatZinc, formalized in Lean 4

LeanFzn is a machine-checked formalization of the **integer/Boolean fragment
of FlatZinc**, the solver input language of the MiniZinc toolchain. It provides
a lexer, a parser, an independent declarative grammar, static and dynamic
semantics — and a machine-checked proof that the parser accepts **exactly** the
grammatically valid FlatZinc strings.

It can also be used to **check a solver-produced solution against a FlatZinc
model**. The checker parses the candidate assignments, completes aliases and
initializers, checks declared domains, and evaluates every supported standard
and global constraint. Its executable decision procedure is connected to the
declarative semantics by Lean proofs; the exact supported fragment and
preconditions are described below.

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## Main results

### Exact parser recognition

The recognition theorem is proven with no `sorry` or user-declared `axiom`.

```lean
theorem parseModel_ok_iff_valid (s : String) :
    (∃ m, Parser.parseModel s = .ok m) ↔ ValidFlatZinc s

theorem parseModel_error_iff_invalid (s : String) :
    (∃ e, Parser.parseModel s = .error e) ↔ ¬ ValidFlatZinc s
```

That is: the parser succeeds on a string if and only if that string is a valid
FlatZinc program, and it fails exactly on the invalid ones. This is the
combination of two directions, each proven independently:

- **Soundness** (`FznCorrectness.lean`): every successful parse yields a model
  that the declarative grammar derives — the parser never accepts garbage.
- **Completeness** (`FznCompleteness.lean`, `FznAssembled.lean`): every grammar
  derivation is accepted by the parser, producing exactly the derived AST —
  the parser never rejects, or mangles, a valid program.

The parser is a fuelled recursive-descent implementation; completeness
includes a proof that the fuel budget `8 * (tokens + 1)` always suffices.

### Verified solution checker

The executable checker uses a small number of `opaque` logical wrappers
paired with verified executable implementations.

`checkSolutionFull` has a machine-checked correctness theorem for the
predicates in `fullCheckableNames`. That closed list currently contains
**174 names**:

- 61 non-extensional standard FlatZinc predicates;
- 19 extensional set predicates; and
- 94 supported `fzn_*` global constraints.

For each of those names, the executable Boolean interpretation is proved
equivalent to the corresponding declarative `Prop` interpretation. Subject
to the theorem's explicit predicate-name hypothesis,
`checkSolutionFull_correct` states that the checker accepts exactly when the
solution parses and its completed store satisfies all variable domains,
initializers, and constraints according to `fullInterp`.

This guarantee is relative to the semantics formalized in this repository.
MiniZinc leaves parts of the `fzn_*` predicate semantics to solver libraries,
so choices and corner cases that are not fixed literally by the reference
material are recorded in
`specification/flatzinc_specification_assumptions.md`. Tests against Gecode
provide useful cross-validation but are not part of the proof.

The checker does **not** support every predicate shipped with MiniZinc 2.10.0.
`Globals.globalsUnsupported` lists the intentionally unsupported globals,
including graph, automaton, optional-value, multidimensional, and
float-dependent families. Unknown or unsupported constraints evaluate to
`false`, so they are rejected rather than assigned guessed semantics. Float
syntax and semantics are outside the project fragment entirely.

Finally, `checkSolutionFull` decides the dynamic part of satisfaction only.
Its correctness theorem does not claim that the input model is statically
well formed, and the current CLI `check` command does not call `wellFormedB`
before checking a solution. Callers that require full `Satisfies fullSig
fullInterp` should first establish `WellFormed fullSig m` (or run its
executable checker) and ensure that every constraint name belongs to
`fullCheckableNames`.

## Project layout

```
leanfzn/
├── LeanFzn.lean              # Umbrella module — imports the whole library
├── Main.lean                  # CLI: parse a file/stdin, or check a solution
├── PLAN.md                    # Current status and prioritized future work
├── lakefile.toml              # Lake build configuration
├── lean-toolchain             # Lean 4.33.1
│
├── LeanFzn/                   # The formalization library
│   ├── FznAST.lean            #   AST: items, expressions, types, annotations
│   ├── FznLexer.lean           #   Total lexer: tokens, integers, strings
│   ├── FznParser.lean          #   Fuelled recursive-descent parser
│   ├── FznGrammar.lean         #   Independent declarative grammar (Gr* rules)
│   ├── FznSemantics.lean       #   Values, evaluation, constraint satisfaction
│   ├── FznSuffix.lean          #   Suffix/consumption lemmas (fuel bookkeeping)
│   ├── FznCorrectness.lean     #   Soundness: parse success ⇒ grammar validity
│   ├── FznCompleteness.lean    #   Component completeness: each Gr* rule is parsed
│   ├── FznAssembled.lean       #   Model-level completeness + recognition theorem
│   ├── FznPretty.lean          #   Canonical pretty-printer (round-trip tested)
│   ├── FznStdLib.lean          #   Standard predicate signatures + interpretations
│   ├── FznSolution.lean        #   Solution-string parser + verified checker
│   ├── FznGlobals.lean         #   Global constraints: signatures, twins, master theorem
│   └── FznGlobals/             #   Global-constraint families (frozen, verified)
│       ├── Common.lean         #     Shared list/set helpers
│       ├── AllDiffCounting.lean #   all-different family (8 fzn_* names)
│       ├── LexSort.lean        #     lex/sort/value-precedence family (12 names)
│       ├── PackSched.lean      #     packing/scheduling family (17 names)
│       ├── Counting.lean       #     counting family (32 names)
│       ├── Channeling.lean     #     channeling family (11 names)
│       └── SetMath.lean        #     set/mathematical family (14 names)
│
├── Tests/
│   ├── Smoke.lean              # 30 parser smoke tests (valid + malformed input)
│   ├── WellFormed.lean         # static well-formedness tests (library-only)
│   ├── Pretty.lean             # 39 pretty-printer round-trip tests (library-only)
│   ├── StdLib.lean             # 64 standard-library tests (static + dynamic)
│   ├── Solution.lean           # solution-checker end-to-end tests
│   ├── Globals.lean            # 52 global-constraint tests (static + dynamic + e2e)
│   ├── Gecode.lean             # 64 Gecode-ported regression tests (15 models)
│   ├── Coverage.lean           # 371 tests covering ALL checkable predicates
│   └── Bench.lean              # compiled perf regression suite (checker + parser)
│
└── specification/
    ├── minizinc-2.10.0/        # The pinned normative reference
    │   ├── README.md           #   Provenance: commit, checksums, links
    │   ├── predicates_and_globals_report.md  # inventory of all builtin/global names
    │   └── fzn-grammar.mzn     #   Vendored official FlatZinc grammar
    └── flatzinc_specification_assumptions.md  # R/A/G-series: every assumption, incl.
                                  #   all predicate-semantics decisions (G-series)
```

### The proof pipeline

The modules form a deliberate chain, each layer building on the last:

1. **`FznAST`** defines the abstract syntax that both the parser and the
   grammar produce.
2. **`FznLexer`** turns a string into tokens, totally, with progress lemmas.
3. **`FznParser`** (implementation) and **`FznGrammar`** (specification) are
   kept strictly independent: the grammar is an inductive relation over token
   lists, not a transcription of the parser.
4. **`FznSuffix`** proves that every grammar rule consumes input, giving the
   fuel bookkeeping needed for termination of the completeness argument.
5. **`FznCorrectness`** proves the parser sound against the grammar.
6. **`FznCompleteness`** proves each grammar rule is matched by the parser,
   with the fuel invariant `2 * remaining + K ≤ fuel`.
7. **`FznAssembled`** chains the component lemmas into `parseModel_complete`
   and the recognition theorems above.
8. **`FznSemantics`** gives the dynamic meaning of models (evaluation,
   satisfaction, objectives), kept separate from the parsing story.
9. **`FznStdLib`** gives the builtins a Prop semantics (`stdInterp`) plus a
   computable twin (`stdInterpB`), proved equivalent per name.
10. **`FznSolution`** checks solution strings against a model; every check
    step is mirrored by a per-name `iff` theorem, capped by the master
    correctness theorem for the standard fragment.
11. **`FznGlobals/*`** (six family modules, frozen) supply the same
    Prop/twin/agreement triple for the 94 `fzn_*` globals; **`FznGlobals`**
    assembles them into the combined interpretation, the master agreement
    `globalsInterpB_iff`, and the full-checker correctness theorem
    `checkSolutionFull_correct`.

### Where the predicate semantics come from

The FlatZinc specification assigns no meaning to `fzn_*` solver
predicates, and several builtin glosses are loose about corner cases.
Every interpretive decision — 1-based array positions, tie-breaking,
partiality, set-lexicographic order, closedness of global
cardinalities, cumulative event-point checking, … — is recorded with
its normative justification in
`specification/flatzinc_specification_assumptions.md` (**G-series**),
with per-predicate handbook quotations and `.mzn` decomposition
citations in the module docstrings (`FznStdLib.lean` and
`LeanFzn/FznGlobals/*.lean`). Reference-solver behavior (Gecode) pins
the two cases where the handbook was genuinely wrong-footing
(truncated division, clause negation). Every decision is executable:
`Tests/Coverage.lean` exercises all 174 checkable names in both truth
directions and fails the build if a name is untested.

## Building and running

Requires Lean 4.33.1 (see `lean-toolchain`; `elan` installs it automatically).

```sh
# Build the library and all executables (the lakefile has no default
# target, so name them; `lake build LeanFzn` builds only the library)
lake build leanfzn tests_smoke tests_stdlib tests_solution tests_globals \
      tests_gecode tests_coverage tests_bench

# Run the test suites
lake env tests_smoke      # 30 parser smoke tests
lake env tests_stdlib     # 64 standard-library tests (static + dynamic)
lake env tests_solution   # solution-checker end-to-end tests
lake env tests_globals    # 52 global-constraint tests (static + dynamic + e2e)
lake env tests_gecode     # 64 Gecode-derived solution-checker regression tests (15 models)
lake env tests_coverage   # 371 tests covering every checkable predicate and global
lake env tests_bench      # compiled perf regression suite (checker + parser timings)

# Parse a FlatZinc file (prints the AST), or pipe via stdin
lake env leanfzn model.fzn
echo 'solve satisfy;' | lake env leanfzn -

# Check a solution string against a model (verified global-constraint checker)
lake env leanfzn check model.fzn solution.txt
# exit 0 = accepted, 1 = rejected, 2 = usage/IO/parse error
```

Exit codes of `leanfzn` (parse mode): 0 = success, 1 = parse error,
2 = usage/IO error. The `check` subcommand: 0 = solution accepted,
1 = solution rejected, 2 = usage/IO/model-parse error.

`Tests/WellFormed.lean` and `Tests/Pretty.lean` can also be run directly
with `lake env lean`; their `#eval`-based checks are compiled by the
corresponding executable targets above. The current Lean build succeeds but
still reports non-fatal linter warnings, primarily unused `simp` arguments in
proof scripts.

## Project status and roadmap

See [`PLAN.md`](PLAN.md) for the completed milestones, current limitations,
and prioritized correctness-preserving extensions and performance work.

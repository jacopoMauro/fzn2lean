# LeanFzn — FlatZinc, formalized in Lean 4

LeanFzn is a machine-checked formalization of the **integer/Boolean fragment
of FlatZinc**, the solver input language of the MiniZinc toolchain. It provides
a lexer, a parser, an independent declarative grammar, static and dynamic
semantics — and a machine-checked proof that the parser accepts **exactly** the
grammatically valid FlatZinc strings.

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## The main result

The recognition theorem, proven with no `sorry`, `axiom`, or `opaque`
declarations anywhere in the project:

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

## Project layout

```
leanfzn/
├── LeanFzn.lean              # Umbrella module — imports the whole library
├── Main.lean                  # CLI: parse a file or stdin, print AST or error
├── PLAN.md                    # Status document: what is done, what remains
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
│   └── FznStdLib.lean          #   Standard predicate signatures + interpretations
│
├── Tests/
│   ├── Smoke.lean              # 15 parser smoke tests (valid + malformed input)
│   ├── WellFormed.lean         # 49 static well-formedness tests
│   ├── Pretty.lean             # 39 pretty-printer round-trip tests
│   └── StdLib.lean             # 64 standard-library tests (static + dynamic)
│
└── specification/
    ├── minizinc-2.10.0/        # The pinned normative reference
    │   ├── README.md           #   Provenance: commit, checksums, links
    │   └── fzn-grammar.mzn     #   Vendored official FlatZinc grammar
    └── flatzinc_specification_assumptions.md  # Scope assumptions
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

## Building and running

Requires Lean 4.33.1 (see `lean-toolchain`; `elan` installs it automatically).

```sh
# Build the library and executables
lake build

# Run the test suites
lake env leanfzn_smoke    # 15 parser smoke tests
lake env leanfzn_wf       # 49 well-formedness tests
lake env leanfzn_pretty   # 39 pretty-printer round-trip tests
lake env leanfzn_stdlib   # 64 standard-library tests

# Parse a FlatZinc file (prints the AST), or pipe via stdin
lake env leanfzn model.fzn
echo 'solve satisfy;' | lake env leanfzn -
```

## Status

All planned milestones are complete: the grammar and parser are aligned
(audit in `specification/grammar-parser-audit.md`), soundness and completeness
are proven, the recognition theorem holds unconditionally, and the static
semantics (`WellFormed` with its executable checker `wellFormedB`) covers
environments, name resolution, initializer/alias equality, array lengths,
objective types, duplicate declarations, and predicate-signature checking.
The optional work is done too: a canonical pretty-printer with round-trip
tests (`FznPretty.lean`), and standard FlatZinc predicate signatures and
interpretations (`FznStdLib.lean`). The build is warning-free and contains
zero `sorry`.

The only remaining extension is float support, deliberately deferred
(see `PLAN.md`).

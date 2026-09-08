# Pinned FlatZinc specification

This directory pins the formalization to **MiniZinc 2.10.0**:

- release: <https://github.com/MiniZinc/libminizinc/releases/tag/2.10.0>
- immutable commit: `c9f9b649b2a251a40aa427a84d7cce73a8807fea`
- published handbook: <https://docs.minizinc.dev/en/2.10.0/fzn-spec.html>
- specification source: <https://github.com/MiniZinc/libminizinc/blob/c9f9b649b2a251a40aa427a84d7cce73a8807fea/docs/en/fzn-spec.rst>
- grammar source: <https://github.com/MiniZinc/libminizinc/blob/c9f9b649b2a251a40aa427a84d7cce73a8807fea/docs/en/fzn-grammar.mzn>

The vendored `fzn-grammar.mzn` is the normative syntax input. Two provenance
comment lines and a checksum comment were prepended; after removing those
comments and the following blank line, its upstream content has SHA-256:

```text
36981b79eccfffd78c6d863ed191b5d62fa2709435853105fd195d9a3712cb89
```

The upstream `fzn-spec.rst` has SHA-256:

```text
4f936fe0b05fbe8495cec2d34806a26a635906d15fb36f70e78f94017a42ba32
```

The prose is referenced through its immutable commit URL rather than copied,
because the repository contains `../flatzinc_specification.rst`. That
older local file has a different checksum and is retained only as background;
it is not the pinned normative source.

The Lean development implements the non-float subset of this pinned grammar.
Any later upgrade must use a new versioned directory and explicitly audit the
grammar, semantics, assumptions, parser, and correctness proofs.

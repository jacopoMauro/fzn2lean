# Pinned FlatZinc specification

This directory pins the formalization to **MiniZinc 2.10.1**:

- release: <https://github.com/MiniZinc/libminizinc/releases/tag/2.10.1>
- immutable commit: `c3448c48e7f05f13805616cfd1b9e94972eef58c`
- published handbook: <https://docs.minizinc.dev/en/2.10.1/fzn-spec.html>
- specification source: <https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/docs/en/fzn-spec.rst>
- grammar source: <https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/docs/en/fzn-grammar.mzn>

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

## Upgrade audit: 2.10.0 to 2.10.1 (2026-11-13)

Compared the upstream release trees at commits
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` and
`c3448c48e7f05f13805616cfd1b9e94972eef58c`:

- `docs/en/fzn-grammar.mzn` and `docs/en/fzn-spec.rst` are byte-for-byte
  identical; the upstream checksums above are unchanged.
- All FlatZinc builtins and global predicate decompositions in
  `share/minizinc/std/` are unchanged. Only `stdlib/stdlib_ann.mzn` and
  `stdlib/stdlib_array.mzn` differ: an internal integer `mzn_path` overload
  (rewritten or removed before output), and array concatenation/slicing
  return types generalized to `any $T`.
- The non-float syntax, predicate semantics, assumptions, parser and proof
  statements therefore require no definition changes. Their source references
  now identify the 2.10.1 release and immutable commit.
- HTML handbook copies were downloaded from the 2.10.1 URLs on 2026-11-13.
  `fzn-spec.md` is carried forward from the previous snapshot with versioned
  links updated, since its normative RST source is unchanged; it is a derived
  reading copy, not a verbatim download.

The installer and Docker build use the official
`MiniZincIDE-2.10.1-x86_64-linux-gnu.tgz` bundle, with SHA-256
`b63dd88491d47b05d0eb0ff4aa1112d1e6f77292c023800b20b98851458ce01c`.

Validation: rebuilt `leanfzn`, `tests_gecode`, `tests_stdlib`, `tests_globals`
and `tests_smoke`; all four test executables passed (64, 64, 52 and 41
checks respectively). All nine `minizinc-wrapper/test.sh` checks passed
against the 2.10.1 bundle and rebuilt solver. Rechecked all 3,353 profiles
in `audits/certified_axioms.lean`: only `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`. The Docker-style default solver registration
also produced the expected packing optimum of 51. Docker itself was unavailable,
so the image build was not run locally.

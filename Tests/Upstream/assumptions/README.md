# Upstream assumption checks (G2, G4, G5, G6)

Ground MiniZinc models that make **MiniZinc 2.10.1 evaluate**, not merely
assert, the operators and predicates whose non-literal reading is recorded as
a G-series assumption in `specification/flatzinc_specification_assumptions.md`
and implemented in `LeanFzn/Semantics/StdLib.lean`.

| Assumption | Case models | Lean definition |
| --- | --- | --- |
| G2 truncated `int_div`/`int_mod` | `int_div.mzn`, `int_mod.mzn`, `int_div_zero.mzn` | `stdInterp "int_div"`/`"int_mod"` (`Int.tdiv`/`Int.tmod`) |
| G4 `int_pow` corner exponents | `int_pow.mzn`, `int_pow_zero_negative.mzn` | `intPow`, `stdInterp "int_pow"`/`"int_pow_fixed"` |
| G5 lexicographic `set_le`/`set_lt` | `set_le_lt.mzn`, `set_le_lt_duplicates.mzn` | `IntSetValue.sortElems`, `listLexLe`/`listLexLt` |
| G6 `*_nonshifted` on `1..n` arrays | `element_nonshifted.mzn`, `element_nonshifted_shift.mzn` | `stdInterp "array_var_{int,bool,set}_element_nonshifted"` |

Each model is plain `.mzn` with `solve satisfy` and an `output` item that
prints the evaluated value, so MiniZinc's own decomposition decides it; none
of them is a constraint that merely tests a property.  The two
`*_zero*.mzn`/`*_shift.mzn` boundary models are expected to be an evaluation
error or unsatisfiable, and that recorded outcome is the evidence for the
"fails closed / only `1..n`" side of the assumptions.

`expected.txt` is the recorded output; `run.sh` and
`test_upstream_assumptions.py` replay it.  A missing oracle is `INCOMPLETE`
(non-zero) or a skip — never a pass.

```bash
eval "$(bash audits/install_oracles.sh --print-env)"   # PATH + LD_LIBRARY_PATH
bash Tests/Upstream/assumptions/run.sh
python3 -B -m unittest discover -s Tests/Upstream/assumptions -p 'test_*.py'
```

Alternatively pass `LEANFZN_ORACLE_LIB=<prefix>/lib`; both runners scope
`LD_LIBRARY_PATH` to their child process so the caller's shell is untouched.
`make_expected.py` re-records `expected.txt` from the pinned oracle (recorder,
not judge).

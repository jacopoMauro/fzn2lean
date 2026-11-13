# FlatZinc predicates and global constraints (MiniZinc 2.10.1)

This report inventories every FlatZinc built-in predicate and every global
constraint of the MiniZinc 2.10.1 standard library, as published in the
handbook. It is the input checklist for the Lean formalization of predicate
semantics (solution checking). The project formalizes the integer/Boolean
fragment (no floats), per
`specification/flatzinc_specification_assumptions.md`; float entries are
listed for completeness but marked out of scope.

## Sources (vendored copies)

All pages fetched from `https://docs.minizinc.dev/en/2.10.1/` on 2026-11-13
and copied verbatim into this directory (HTML). The Markdown specification
is a derived reading copy; see the upgrade audit in `README.md`:

| Page | Local copy | Content |
| --- | --- | --- |
| 4.3 Interfacing Solvers to Flatzinc | `fzn-spec.html` (HTML), `fzn-spec.md` (markdown) | FlatZinc syntax/semantics spec |
| 4.2.3 FlatZinc builtins | `lib-flatzinc.html` | Builtins index |
| 4.2.3.1–4.2.3.13 | `lib-flatzinc-int.html`, `lib-flatzinc-bool.html`, `lib-flatzinc-set.html`, `lib-flatzinc-float.html`, `lib-flatzinc-two.html`, `lib-flatzinc-twootwo.html`, `lib-flatzinc-twoone.html`, `lib-flatzinc-twooneone.html`, `lib-flatzinc-twotwoone.html`, `lib-flatzinc-twothreethree.html`, `lib-flatzinc-twofivetwo.html`, `lib-flatzinc-twosevenone.html`, `lib-flatzinc-deprecated.html` | Per-category builtin definitions |
| 4.2 The MiniZinc library | `lib.html` | Library index |
| 4.2.2 Global constraints | `lib-globals.html` + 15 category pages (`lib-globals-*.html`) | Global constraint definitions |

Checksums: `webpage-copies.sha256`.

## FlatZinc built-in predicates

The FlatZinc specification (Section 4.3.4.1) requires solvers to support
these (or redefine them). Counts below are per the handbook pages.

### Integer (25) — in scope

| # | Predicate |
| --- | --- |
| 1 | `array_int_element` |
| 2 | `array_var_int_element` |
| 3 | `int_abs` |
| 4 | `int_div` |
| 5 | `int_eq` |
| 6 | `int_eq_reif` |
| 7 | `int_le` |
| 8 | `int_le_reif` |
| 9 | `int_lin_eq` |
| 10 | `int_lin_eq_reif` |
| 11 | `int_lin_le` |
| 12 | `int_lin_le_reif` |
| 13 | `int_lin_ne` |
| 14 | `int_lin_ne_reif` |
| 15 | `int_lt` |
| 16 | `int_lt_reif` |
| 17 | `int_max` |
| 18 | `int_min` |
| 19 | `int_mod` |
| 20 | `int_ne` |
| 21 | `int_ne_reif` |
| 22 | `int_plus` |
| 23 | `int_pow` |
| 24 | `int_times` |
| 25 | `set_in` (integer domain membership) |

### Bool (18) — in scope

| # | Predicate |
| --- | --- |
| 1 | `array_bool_and` |
| 2 | `array_bool_element` |
| 3 | `array_bool_xor` |
| 4 | `array_var_bool_element` |
| 5 | `bool2int` |
| 6 | `bool_and` |
| 7 | `bool_clause` |
| 8 | `bool_eq` |
| 9 | `bool_eq_reif` |
| 10 | `bool_le` |
| 11 | `bool_le_reif` |
| 12 | `bool_lin_eq` |
| 13 | `bool_lin_le` |
| 14 | `bool_lt` |
| 15 | `bool_lt_reif` |
| 16 | `bool_not` |
| 17 | `bool_or` |
| 18 | `bool_xor` |

### Set (21) — in scope (set constraints over integer elements)

| # | Predicate |
| --- | --- |
| 1 | `array_set_element` |
| 2 | `array_var_set_element` |
| 3 | `set_card` |
| 4 | `set_diff` |
| 5 | `set_eq` |
| 6 | `set_eq_reif` |
| 7 | `set_in` |
| 8 | `set_in_reif` |
| 9 | `set_intersect` |
| 10 | `set_le` |
| 11 | `set_le_reif` |
| 12 | `set_lt` |
| 13 | `set_lt_reif` |
| 14 | `set_ne` |
| 15 | `set_ne_reif` |
| 16 | `set_subset` |
| 17 | `set_subset_reif` |
| 18 | `set_superset` |
| 19 | `set_superset_reif` |
| 20 | `set_symdiff` |
| 21 | `set_union` |

### Float (43) — OUT OF SCOPE (no floats in this project)

`array_float_element`, `array_var_float_element`, `float_abs`,
`float_acos`, `float_acosh`, `float_asin`, `float_asinh`, `float_atan`,
`float_atanh`, `float_cos`, `float_cosh`, `float_div`, `float_eq`,
`float_eq_reif`, `float_exp`, `float_le`, `float_le_reif`, `float_lin_eq`,
`float_lin_eq_reif`, `float_lin_le`, `float_lin_le_reif`, `float_lin_lt`,
`float_lin_lt_reif`, `float_lin_ne`, `float_lin_ne_reif`, `float_ln`,
`float_log10`, `float_log2`, `float_lt`, `float_lt_reif`, `float_max`,
`float_min`, `float_ne`, `float_ne_reif`, `float_plus`, `float_pow`,
`float_sin`, `float_sinh`, `float_sqrt`, `float_tan`, `float_tanh`,
`float_times`, `int2float`

### Added in MiniZinc 2.0.0 (5)

In scope (integer/bool): `array_int_maximum`, `array_int_minimum`,
`bool_clause_reif`.
Out of scope (float): `array_float_maximum`, `array_float_minimum`.

### Added in MiniZinc 2.0.2 (4)

In scope: `array_var_bool_element_nonshifted`,
`array_var_int_element_nonshifted`, `array_var_set_element_nonshifted`.
Out of scope: `array_var_float_element_nonshifted`.

### Added in MiniZinc 2.1.0 (2) — OUT OF SCOPE

`float_dom`, `float_in`.

### Added in MiniZinc 2.1.1 (2)

Functions (not constraints) over `var set of $$E`: `max`, `min` — set
maximum/minimum; in scope if set variables are supported.

### Added in MiniZinc 2.2.1 (1) — in scope

`int_pow_fixed`.

### Added in MiniZinc 2.3.3 (1) — OUT OF SCOPE

`float_set_in`.

### Added in MiniZinc 2.5.2 (4)

In scope: `array_var_bool_element2d_nonshifted`,
`array_var_int_element2d_nonshifted`,
`array_var_set_element2d_nonshifted`.
Out of scope: `array_var_float_element2d_nonshifted`.

### Added in MiniZinc 2.7.1 (3) — OUT OF SCOPE

`float_ceil`, `float_floor`, `float_round`.

### Deprecated (1)

`array_bool_or` (use `array_bool_and`/`bool_or` forms instead).

### Summary for the Lean formalization (integer/Boolean/set fragment)

- Integer: 25
- Bool: 18
- Set: 21
- 2.0.0 additions (int/bool): 3
- 2.0.2 additions (non-float): 3
- 2.1.1 additions: 2 (`max`/`min` set functions)
- 2.2.1 additions: 1 (`int_pow_fixed`)
- 2.5.2 additions (non-float): 3
- Deprecated: 1 (`array_bool_or`)

**Total in scope: 77 builtin entries** (75 predicates plus the 2.1.1 `max`/
`min` functions; some, like `set_in`, appear in two categories).

## Global constraints (MiniZinc standard library, Section 4.2.2)

Global constraints are higher-level library predicates (defined in
MiniZinc, decomposed by the compiler into FlatZinc builtins unless a solver
supports them natively). Their *fzn_* counterparts (e.g. `fzn_all_different_int`)
are what actually appear in FlatZinc output. Formalizing them is relevant
for checking solutions of models that use them.

### All-different and related (7)

`all_different`, `all_different_except`, `all_different_except_0`,
`all_disjoint`, `all_equal`, `nvalue`, `symmetric_all_different`

### Lexicographic (19)

`lex2`, `lex2_strict`, `lex_chain`, `lex_chain_greater`,
`lex_chain_greatereq`, `lex_chain_greatereq_orbitope`, `lex_chain_less`,
`lex_chain_lesseq`, `lex_chain_lesseq_orbitope`, `lex_greater`,
`lex_greatereq`, `lex_less`, `lex_lesseq`, `seq_precede_chain`,
`strict_lex2`, `value_precede`, `value_precede_chain`, `var_perm_sym`,
`var_sqr_sym`

### Sorting (6)

`arg_sort`, `decreasing`, `increasing`, `sort`, `strictly_decreasing`,
`strictly_increasing`

### Channeling (5)

`int_set_channel`, `inverse`, `inverse_in_range`, `inverse_set`,
`link_set_to_booleans`

### Counting (16)

`among`, `at_least`, `at_most`, `at_most1`, `count`, `count_eq`,
`count_geq`, `count_gt`, `count_leq`, `count_lt`, `count_neq`,
`distribute`, `exactly`, `global_cardinality`,
`global_cardinality_closed`, `sliding_among`

### Array-related (5)

`element`, `member`, `write`, `writes`, `writes_seq`

### Set-related (3)

`disjoint`, `partition_set`, `roots`

### Mathematical (9)

`maximum`, `maximum_arg`, `minimum`, `minimum_arg`, `piecewise_linear`,
`range`, `sliding_sum`, `sum_pred`, `sum_set`

### Packing (12)

`bin_packing`, `bin_packing_capa`, `bin_packing_load`, `diffn`, `diffn_k`,
`diffn_nonstrict`, `diffn_nonstrict_k`, `geost`, `geost_bb`,
`geost_nonoverlap_k`, `geost_smallest_bb`, `knapsack`

### Scheduling (6)

`alternative`, `cumulative`, `cumulatives`, `disjunctive`,
`disjunctive_strict`, `span`

### Graph (20)

`bounded_dpath`, `bounded_path`, `circuit`, `connected`,
`d_weighted_spanning_tree`, `dag`, `dconnected`, `dpath`, `dreachable`,
`dsteiner`, `dtree`, `network_flow`, `network_flow_cost`, `path`,
`reachable`, `steiner`, `subcircuit`, `subgraph`, `tree`,
`weighted_spanning_tree`

### Extensional (7)

`cost_mdd`, `cost_regular`, `mdd`, `mdd_nondet`, `regular`, `regular_nfa`,
`table`

### Machine learning (1)

`neural_net` (contains float weights — effectively out of scope)

### Deprecated (5)

`at_least`, `at_most`, `exactly`, `global_cardinality_low_up`,
`global_cardinality_low_up_closed`

**Total: 118 distinct global-constraint predicate names** (the deprecated
`at_least`, `at_most`, `exactly` duplicate names in the counting section).

## Notes for the Lean formalization

1. The `fzn-spec.md`/`fzn-spec.html` copy is the normative syntax
   reference; builtins semantics live in the `lib-flatzinc-*.html` pages.
2. Global constraints never appear in FlatZinc under their plain names;
   the compiler decomposes or maps them to `fzn_<name>_<type>` solver
   predicates. The signature environment (assumption A3) determines
   which are accepted.
3. For solution checking, each in-scope builtin needs a Lean definition
   of its denotation as a predicate on assignments, plus a correctness
   theorem relating it to the MiniZinc library definition.

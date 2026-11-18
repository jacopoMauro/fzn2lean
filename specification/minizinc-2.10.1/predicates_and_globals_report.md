# Reviewed FlatZinc semantic-conformance inventory

## Executive assessment

Review date: **16 November 2026**. Scope begins at FlatZinc and excludes the
MiniZinc translator. This is a source-contract review against the pinned
handbook and immutable libminizinc commit
`c3448c48e7f05f13805616cfd1b9e94972eef58c`. It is an agent review,
not an independent human sign-off or a formal proof of correspondence to prose.

Every active `stdSig`/`globalsSig` name has a row: **218 implemented names**,
plus published builtin/function exclusions and five explicitly unsupported
globals, for **281 rows**. The evidence records **149 immutable upstream source
file hashes** and **76 local source/reference/test hashes**. The machine-readable
[inventory](semantic_conformance.json) stores each contract, both signatures,
implementation location, edge cases, source link/hash and finding links.

**The inventory review is complete for this declared scope, with no open
recorded findings. Upstream semantic equivalence remains unproved, and the
13 restricted rows now have explicit public admission policies (eight gated,
five excluded). Independent upstream correspondence remains a T3 obligation.** All **15 findings** are
repaired and regression-tested. An inventory completion is not permission to call every entry
conformant. Unlisted globals, reified/float/optional overloads and other native
ABIs are unsupported unless explicitly inventoried; the 118 high-level global
names in the historical catalogue below are not 118 implemented native ABIs.

| Disposition | Rows | Meaning |
| --- | ---: | --- |
| `reviewed` | 183 | Source comparison found no discrepancy for well-typed, defined inputs within the stated fragment; not a kernel-checked upstream equivalence theorem. |
| `restricted` | 13 | Internal interpretations with explicit public source admission: eight gated families, five excluded native contracts; upstream correspondence remains unproved. |
| `extension` | 15 | Project-specific spelling or a signature extension; not strict native ABI conformance. |
| `nonconformant` | 0 | A concrete signature/semantic discrepancy or an unestablished representation contract remains; linked findings prevent a clean conformance gate. |
| `unsupported` | 70 | No implementation signature or explicitly excluded input family. |

Counts are predicates/functions, not proof obligations, supported input shapes,
or independently certified implementations. `reviewed` applies to well-typed,
defined inputs in the stated fragment; it is not a total native-input theorem.
`restricted` rows retain ABI/semantic restrictions; the public entry points now
enforce or exclude them. Their internal interpretations are not total native APIs.

## T2 admission review — 17 November 2026

The pinned source definitions for all thirteen restricted predicates and the
closed-cardinality wrapper dependencies were re-read for this change. The two
new wrapper evidence files were byte-checked against the immutable upstream commit. `Semantics/Admission.lean` defines `ConstraintAdmitted`
and `Admitted`; `admittedB_iff` and `firstFailure_none_iff` verify the executable
gates. `checkModelSolution`, its fast twin and prepared checking return
unsupported before evaluating a call outside the source fragment.
`compileModelFull_admitted` proves successful source compilation establishes
admission; the compiler and phase-statistics path check it **before literal
folding**. Thus a restricted ground call cannot be misreported as source UNSAT.

| Restricted inventory entry | Public admitted contract | Enforcement / reason |
| --- | --- | --- |
| `fzn_bin_packing` | Equal bin/weight lengths, nonnegative constant/parameter capacity and weights | Parameter-only evaluation, not shape-store dummy values. Nonnegative capacity makes checks of unoccupied declared bins harmless; empty bins are admitted only in this subset. |
| `fzn_cumulative` | Equal three task-array lengths, nonnegative constant/parameter durations and resources | Establishes the pinned wrapper's lower-bound premises. Variable durations/resources are explicitly unsupported even when a candidate solution supplies positive values. |
| `fzn_cumulatives` | Task-array length inequalities, constant machine entries within `1..bound.length`, `min_machine = 1` | Requires valid reads even when raw implications mask them. Original offset metadata is outside this normalized ABI. |
| `fzn_cumulatives_decomp` | Same length and machine-entry gates, without `min_machine` | Negative durations/resources retain the native event semantics; they are not silently required nonnegative. |
| `fzn_regular`, `fzn_regular_nfa`, `fzn_cost_regular` | Nonnegative dimensions, set-valued final states, flat row-major matrices of exactly `Q*S` entries | `Regular.regularDecodes` over statically known shapes/parameters; the interpreter checks actual word symbols and reached states. Empty-word semantics are preserved. |
| `fzn_global_cardinality_low_up_closed` | Equal cover/lower/upper lengths; for empty inputs all lower/upper bounds permit count zero | Checks the delegated wrapper assertions. Prop and Bool also implement the native `sum(low) <= length(xs) <= sum(up)`. The internal aggregate sums all entries; extra bound entries are outside public admission. Duplicate cover values show the aggregate is not redundant. |
| `fzn_geost`, `fzn_geost_bb`, `fzn_geost_smallest_bb` | No public native call admitted | Shape/rectangle index and domain metadata are not established by decoded flat values. Even empty/ground calls are unsupported. |
| `fzn_cost_mdd`, `fzn_mdd_nondet` | No public native call admitted | The internal canonical-cost/walk relations do not establish native activation contracts. The former canonical subset is not published as native checking support. |

Array lower indices are fixed to 1 by `Syntax.IndexSet` and the parser;
`WellFormed.parameterTypes`, `variableArrayLengths` and
`constraintsChecked/constraintsDecode` establish typing/declaration and decoder
conditions. Cross-argument restricted premises have the additional gate above.
No claim about arbitrary multidimensional MiniZinc lowering is inferred.

The internal `fullInterp`, `checkSolutionFull` and explicitly named
`checkSemanticModelSolution*` APIs retain project-relative semantics for proof
and research use. Their old correctness contract remains available; the public
`checkModelSolution_correct` now additionally requires `Admission.Admitted`.
`parameter_eval` and `nonnegativeArray_values` prove parameter-only values
persist in every parameter-honest candidate store. Checker admission and solver
compilation remain distinct: admitted globals with decision variables can still
be unsupported by the scalar solver compiler.

`Tests/Semantics/Admission.lean` kernel-checks gate boundaries;
`Tests/Cli/test_admission.py` checks positive, false and unsupported cases through
the actual checker/solver, phase-statistics and portfolio entries. The inventory
validator requires explicit checker/solver scope, gate and regression evidence
for each restricted row. This is a renewed review of admission obligations,
not an upstream-equivalence proof or a completion of T1/T3.

## Lexical certification — 18 November 2026

On the user's Lean 4.36.0 port, `Lexical.tokenize_sound`, `tokenize_complete`
and `tokenize_correct` now prove the actual lexer equivalent to the independent
whole-character `Lexes` relation. `parseModel_iff_sourceGrammar` composes it
with the existing token grammar and preserves the exact AST. The proof has no
successful-lexer or rendered-origin premise. The specification imports shared
token data only; the architecture audit checks this transitively. UTF-8 meaning
uses the encoder, with the decoder/encoder bridge proved constructively.

The raw-CR string discrepancy is resolved under the declared strict R11 policy;
raw LF/CR reject and escaped linebreaks remain valid. This is a chosen lexical
policy (the upstream grammar explicitly excludes LF), not an assertion that
upstream universally forbids raw CR. Tests cover 35 accepted and 27 rejected
boundary cases. Main proof endpoints are included in the axiom audit. This
closes the specified lexer proof task; T1 and T3's independent predicate
semantics and full upstream correspondence are not inferred from it.

## Reproduce and maintain the review

```bash
python3 -B audits/check_semantic_inventory.py
python3 -B -m unittest Tests.Audits.test_semantic_inventory
lake build LeanFzn.Semantics +Tests.Semantics.Conformance
# Optional: verify a fresh immutable libminizinc source download:
python3 -B audits/check_semantic_inventory.py --upstream-root PATH_TO_TREE
# Required review-freshness check; does not prove upstream equivalence:
python3 -B audits/check_semantic_inventory.py --require-clean
```

The default validator checks coverage and freshness. The clean check is
expected to pass on this revision. No automatic refresh/approval
command is provided: changes to a semantic helper, signature, interpretation
or pinned local reference require renewed review. Axiom hygiene and PGO/native
comparison gates cannot substitute for this check. Both acceptance and release
runners now invoke the clean check; the release
runner validates and preserves the frozen review evidence. A passing check
alone does not establish a conformance claim. MiniZinc is not needed to run
the checks above.


## Repairs and validation

| Finding | Repair | Regression evidence |
| --- | --- | --- |
| SC-01 | Both upstream overloads are registered; decoders use the native argument order and explicit N/E | Arity/order rejection, N/E length and isolated-node witnesses |
| SC-02 | Set-valued `F`, enforced state/symbol bounds and union-accumulating NFA frontier | Set/indicator `F`, empty word, bad transition and NFA union cases |
| SC-03 | Flat row-major matrix ABI with recovered dimensions, or explicit rejection where dimensions are not recoverable | Flat/nested shape, length and dimension-recovery witnesses |
| SC-04 | Per-read shape/partiality gates preserving raw three-valued masking; six residual rows are explicitly restricted | Mismatched-length, out-of-range, first-true and last-write witnesses (T10-W1..W4) |
| SC-05 | Graph relations transcribed with explicit node/edge validity, endpoint and degree conjuncts | DAG unselected-node, isolated node and path degree witnesses |
| SC-06 | Literal deterministic `fzn_mdd`; cost MDD gated to the canonical layered fragment; nondeterministic walk remains restricted | Reviewer self-loop counterexample, deterministic accept/reject, cost-total and canonical-gate witnesses |
| SC-07 | Negative widths rejected; zero-width windows check the window bounds; vacuous overlong windows kept | Zero-width, negative-width and overlong-window witnesses |
| SC-08 | Out-of-range coefficient references make the predicate false; the defined case is summed directly | Dropped-index and repeated-index witnesses |
| SC-09 | Empty-task and negative-resource behavior aligned with the raw native decomposition | Empty arrays with negative capacity, negative resources and positive task cases |
| SC-10 | The implied `sum(count) <= length(xs)` condition is enforced; duplicate cover values reproduced | Duplicate-cover and short-count witnesses |
| SC-11 | Both disjunctive variants enforce nonnegative durations in Prop and Bool | Negative singleton and zero-duration strict/nonstrict cases |
| SC-12 | Cumulatives uses the assigned machine bound; native machine ids retain `min_machine` offset | Asymmetric upper/lower bounds, offset and empty tasks |
| SC-13 | Conditional partiality leaves `b` unrestricted when no condition is true | All-false, selected-false and first-true cases |
| SC-14 | Knapsack enforces nonnegative counts and both totals | Negative count/totals and a positive solution |
| SC-15 | Set enumerations are deduplicated for intersection cardinality and sum indices | Duplicate intersection elements and repeated coefficient indices |

`LeanFzn.Semantics` and `Tests.Semantics.Conformance` compiled successfully with
Lean 4.35.0. This checks the edited Boolean/Prop agreement proofs and **472**
kernel-evaluated regression theorems. The inventory validator passed with all
147 downloaded source hashes checked, and its **12** failure-path tests passed.
The whole-project build passed (`LeanFzn`, `LeanFzn.Legacy`, `Tests`,
`Tests.Legacy`, `leanfzn` and the four semantic executables; 764 jobs). The
final Conformance leaf was rechecked after its last test edit. The native
suites passed **646** checks: globals 52, stdlib 64, coverage 466 and
Gecode-derived 64. The coverage suite exercised all 218 registered names;
a separate Lean dispatch-list query matched all 218 inventory rows exactly.
The eight repaired agreement-theorem axiom profiles used only `propext`,
`Classical.choice` and `Quot.sound`. These are finite test/build and scoped
axiom checks, not a passing full acceptance/release gate or upstream
equivalence proof.

### Concrete observations

Every defect observation from the review is now a kernel-checked
regression in `Tests/Semantics/Conformance.lean` with the upstream
expected value. No open observation remains.

## Theorem-by-theorem boundary audit

| Result | Statement complete? | Proof valid? | Dependencies checked? | Edge cases | Status | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| Edited disjunctive/knapsack/cumulatives/partiality Boolean-to-Prop bridges | Relative to local denotations | Kernel accepted | Semantic library rebuilt | 472 new regressions | verified-no-issue-found | Does not quantify over arbitrary upstream programs |
| Other per-name Boolean/Prop bridges | Relative to local denotations | Semantic library builds; no full line-by-line proof re-review | Local semantic dependency cone built | Listed per family/row | not-fully-checked | Neither shared definitions nor agreement prove upstream fidelity |
| Upstream-to-local semantic equivalence for every native input | Explicit total ABI/admissibility contracts for the repaired entries | No such complete proof established | Closed findings above | Repairs and regressions recorded | restricted | This inventory does not invent an equivalence theorem |

## Assumption and definition audit

| Rule | Contract | Disposition | Evidence and limitation |
| --- | --- | --- | --- |
| MR-01 | One ordered sequence of predicate, parameter, variable, constraint items and one solve item; full consumption. | reviewed | `LeanFzn/Parser/Grammar.lean:GrModel`. Independent grammar/parser correspondence exists; character-level lexer fidelity is a separate obligation, outside this inventory. |
| MR-02 | Unique predicate names, formal argument names, and a shared unique parameter/variable namespace. | reviewed | `LeanFzn/Semantics/Model.lean:WellFormed`. Names and expression types are statically checked; runtime checker does not trust user-declared predicate meanings. |
| MR-03 | Parameters are fixed by literal declarations and cannot be reassigned by a solution. | reviewed | `LeanFzn/Semantics/Model.lean:ParamHonest`. Satisfies alone omits this condition. Certification statements about instances must use Satisfies AND ParamHonest, or IsSolution. |
| MR-04 | Finite ranges are closed; set equality is extensional and duplicates do not change membership/cardinality. | reviewed | `LeanFzn/Semantics/Model.lean:BasicVarType.contains`. Reversed ranges denote empty sets; explicit empty-domain inputs can be unsupported by search without a false verdict. |
| MR-05 | All variable domain restrictions and initializer equalities hold simultaneously. | policy | `LeanFzn/Semantics/Model.lean:initializerHolds`. Forward references and alias cycles use the documented global-environment policy R5/R6; inconsistent initializers are unsatisfiable, not overwritten. |
| MR-06 | Arrays are flat, 1-based, have declared lengths and correctly typed elements. | restricted | `LeanFzn/Semantics/Model.lean:WellFormed`. Static lengths do not establish every cross-argument shape condition. Multidimensional native lowering needs SC-03; parallel lengths need SC-04. |
| MR-07 | Satisfaction requires all constraints, domains and initializers; optimization additionally attains an objective and compares all parameter-honest solutions. | reviewed | `LeanFzn/Semantics/Model.lean:IsSolution`. Integer objective only; supported solver objective shapes are narrower than typed AST objectives. Completion is required for optimality. |
| MR-08 | Search annotations may affect strategy but cannot alter satisfying assignments. | policy | `LeanFzn/Integration/Config/Annotations.lean`. Annotation grammar extensions R28 and escape rules R11 are documented. Verify strategy soundness separately from semantic interpretation. |
| MR-09 | Use exact mathematical integers and finite integer sets. | policy | `LeanFzn/Semantics/Model.lean:Value`. A1 explicitly chooses unbounded Lean Int. Machine-specific integer limits must be separate checks; floats/optional values are excluded. |
| MR-10 | Checker solutions assign declared variables once; omissions may be completed from evaluable declaration initializers. | policy | `LeanFzn/Checker/Runtime/Check.lean:checkModelSolution`. A7/A10 is a checker-interface policy, not a FlatZinc model-semantics ambiguity; projected output without an initializer extension can be rejected. |
| MR-11 | The documented language admits scalar parameters and selected annotation/index spelling extensions. | policy | `specification/flatzinc_specification_assumptions.md:R27/R28/R29`. These policies must remain distinguishable from exact BNF conformance; they are not evidence that MiniZinc translation is certified. |
| MR-12 | Registered native predicate names may be resolved from the external signature table without a model declaration. | policy | `LeanFzn/Semantics/Model.lean:Model.sigEnv`. The FlatZinc prose requires nonstandard predicate declarations. Accepting undeclared registered names is a project interface extension, not exact context-sensitive input conformance. Declared signatures take precedence for typing; dynamic meaning still comes from the fixed name table, not a user predicate body. |

The reference for model rules is the [pinned FlatZinc specification]
(https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/docs/en/fzn-spec.rst)
and the local [grammar](fzn-grammar.mzn). The [assumptions document]
(../flatzinc_specification_assumptions.md) records the deliberate policies;
they must not be confused with implementation discrepancies or checker-interface
choices. Lexical certification, compiler correctness, search correctness and
I/O trace refinement remain separate obligations.

## Additional issues

- **MODERATE:** old semantic module headers cite removed G-series assumptions
  and old filenames. Those references do not establish an upstream contract;
  the exact sources and findings in this inventory supersede them.
- **MODERATE:** name support in the solution checker is broader than compilation
  support in the solver. A row does not promise that all argument shapes compile.
- **MINOR:** the historical catalogue has duplicate category entries (notably
  `set_in`) and high-level names. Its totals are not the active signature totals.

## Unresolved proof obligations

- [x] Close SC-01 through SC-10 with an implementation repair or an explicit,
  verified admissibility/representation contract.
- [ ] Prove upstream-to-local correspondence on the admitted fragment; do not
  substitute Boolean/Prop agreement for that statement.
- [ ] Validate text-level inputs so that no unchecked shape/partiality premise
  is silently inherited from MiniZinc translation.
- [ ] Obtain independent human review of the reviewed formal specification.
- [ ] Run the clean semantic check and existing full/release gates on one
  complete committed revision before making an artifact-level claim.

## Per-name reviewed inventory

Detailed contracts, edge cases, exact signatures and hashes are in
[semantic_conformance.json](semantic_conformance.json). Every entry below was
assigned an explicit disposition. Source comparison does not automatically
approve a row because the implementation has a theorem named `_iff`.

| Name | Disposition | Implementation | Findings / source |
| --- | --- | --- | --- |
| `all_different` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1065) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_different_int.mzn) |
| `all_different_except_0` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1069) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_alldifferent_except_0.mzn) |
| `array_bool_and` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1176) | —; [reference](lib-flatzinc-bool.html#array-bool-and) |
| `array_bool_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1135) | —; [reference](lib-flatzinc-bool.html#array-bool-element) |
| `array_bool_or` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1184) | —; [reference](lib-flatzinc-deprecated.html#array-bool-or) |
| `array_bool_xor` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1180) | —; [reference](lib-flatzinc-bool.html#array-bool-xor) |
| `array_float_element` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#array-float-element) |
| `array_float_maximum` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-two.html#array-float-maximum) |
| `array_float_minimum` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-two.html#array-float-minimum) |
| `array_int_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1123) | —; [reference](lib-flatzinc-int.html#array-int-element) |
| `array_int_maximum` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1168) | —; [reference](lib-flatzinc-two.html#array-int-maximum) |
| `array_int_minimum` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1172) | —; [reference](lib-flatzinc-two.html#array-int-minimum) |
| `array_set_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1147) | —; [reference](lib-flatzinc-set.html#array-set-element) |
| `array_var_bool_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1139) | —; [reference](lib-flatzinc-bool.html#array-var-bool-element) |
| `array_var_bool_element2d_nonshifted` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twofivetwo.html#array-var-bool-element2d-nonshifted) |
| `array_var_bool_element_nonshifted` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1143) | —; [reference](lib-flatzinc-twootwo.html#array-var-bool-element-nonshifted) |
| `array_var_float_element` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#array-var-float-element) |
| `array_var_float_element2d_nonshifted` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twofivetwo.html#array-var-float-element2d-nonshifted) |
| `array_var_float_element_nonshifted` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twootwo.html#array-var-float-element-nonshifted) |
| `array_var_int_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1127) | —; [reference](lib-flatzinc-int.html#array-var-int-element) |
| `array_var_int_element2d_nonshifted` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twofivetwo.html#array-var-int-element2d-nonshifted) |
| `array_var_int_element_nonshifted` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1131) | —; [reference](lib-flatzinc-twootwo.html#array-var-int-element-nonshifted) |
| `array_var_set_element` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1154) | —; [reference](lib-flatzinc-set.html#array-var-set-element) |
| `array_var_set_element2d_nonshifted` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twofivetwo.html#array-var-set-element2d-nonshifted) |
| `array_var_set_element_nonshifted` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1161) | —; [reference](lib-flatzinc-twootwo.html#array-var-set-element-nonshifted) |
| `bool2int` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L924) | —; [reference](lib-flatzinc-bool.html#bool2int) |
| `bool_and` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L877) | —; [reference](lib-flatzinc-bool.html#bool-and) |
| `bool_clause` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L910) | —; [reference](lib-flatzinc-bool.html#bool-clause) |
| `bool_clause_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L916) | —; [reference](lib-flatzinc-two.html#bool-clause-reif) |
| `bool_eq` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L869) | —; [reference](lib-flatzinc-bool.html#bool-eq) |
| `bool_eq_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L897) | —; [reference](lib-flatzinc-bool.html#bool-eq-reif) |
| `bool_le` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L889) | —; [reference](lib-flatzinc-bool.html#bool-le) |
| `bool_le_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L901) | —; [reference](lib-flatzinc-bool.html#bool-le-reif) |
| `bool_lin_eq` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1115) | SC-04; [reference](lib-flatzinc-bool.html#bool-lin-eq) |
| `bool_lin_le` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1119) | SC-04; [reference](lib-flatzinc-bool.html#bool-lin-le) |
| `bool_lt` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L893) | —; [reference](lib-flatzinc-bool.html#bool-lt) |
| `bool_lt_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L905) | —; [reference](lib-flatzinc-bool.html#bool-lt-reif) |
| `bool_not` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L873) | —; [reference](lib-flatzinc-bool.html#bool-not) |
| `bool_or` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L881) | —; [reference](lib-flatzinc-bool.html#bool-or) |
| `bool_xor` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L885) | —; [reference](lib-flatzinc-bool.html#bool-xor) |
| `dom` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L977) | —; [reference](lib-flatzinc-set.html#set-in) |
| `float_abs` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-abs) |
| `float_acos` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-acos) |
| `float_acosh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-acosh) |
| `float_asin` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-asin) |
| `float_asinh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-asinh) |
| `float_atan` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-atan) |
| `float_atanh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-atanh) |
| `float_ceil` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twosevenone.html#float-ceil) |
| `float_cos` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-cos) |
| `float_cosh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-cosh) |
| `float_div` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-div) |
| `float_dom` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twoone.html#float-dom) |
| `float_eq` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-eq) |
| `float_eq_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-eq-reif) |
| `float_exp` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-exp) |
| `float_floor` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twosevenone.html#float-floor) |
| `float_in` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twoone.html#float-in) |
| `float_le` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-le) |
| `float_le_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-le-reif) |
| `float_lin_eq` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-eq) |
| `float_lin_eq_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-eq-reif) |
| `float_lin_le` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-le) |
| `float_lin_le_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-le-reif) |
| `float_lin_lt` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-lt) |
| `float_lin_lt_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-lt-reif) |
| `float_lin_ne` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-ne) |
| `float_lin_ne_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lin-ne-reif) |
| `float_ln` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-ln) |
| `float_log10` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-log10) |
| `float_log2` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-log2) |
| `float_lt` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lt) |
| `float_lt_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-lt-reif) |
| `float_max` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-max) |
| `float_min` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-min) |
| `float_ne` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-ne) |
| `float_ne_reif` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-ne-reif) |
| `float_plus` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-plus) |
| `float_pow` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-pow) |
| `float_round` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twosevenone.html#float-round) |
| `float_set_in` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twothreethree.html#float-set-in) |
| `float_sin` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-sin) |
| `float_sinh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-sinh) |
| `float_sqrt` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-sqrt) |
| `float_tan` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-tan) |
| `float_tanh` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-tanh) |
| `float_times` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#float-times) |
| `fzn_all_different_int` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L805) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_different_int.mzn) |
| `fzn_all_different_set` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L809) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_different_set.mzn) |
| `fzn_all_disjoint` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L813) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_disjoint.mzn) |
| `fzn_all_equal_int` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L817) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_equal_int.mzn) |
| `fzn_all_equal_set` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L821) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_all_equal_set.mzn) |
| `fzn_alldifferent_except` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L825) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_alldifferent_except.mzn) |
| `fzn_alldifferent_except_0` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L829) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_alldifferent_except_0.mzn) |
| `fzn_alternative` | unsupported | [Globals](../../LeanFzn/Semantics/Globals.lean) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_alternative.mzn) |
| `fzn_among` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L421) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_among.mzn) |
| `fzn_arg_sort_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L742) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_arg_sort_int.mzn) |
| `fzn_arg_val_bool` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L712) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_arg_val_bool.mzn) |
| `fzn_arg_val_int` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L708) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_arg_val_int.mzn) |
| `fzn_array_int_union` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1014) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_array_int_union.mzn) |
| `fzn_array_set_intersect` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1022) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_array_set_intersect.mzn) |
| `fzn_array_set_union` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1018) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_array_set_union.mzn) |
| `fzn_at_least_int` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L425) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_at_least_int.mzn) |
| `fzn_at_least_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L533) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_at_least_set.mzn) |
| `fzn_at_most1` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L994) | SC-15; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_at_most1.mzn) |
| `fzn_at_most_int` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L429) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_at_most_int.mzn) |
| `fzn_at_most_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L537) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_at_most_set.mzn) |
| `fzn_bin_packing` | restricted | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1201) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_bin_packing.mzn) |
| `fzn_bin_packing_capa` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1205) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_bin_packing_capa.mzn) |
| `fzn_bin_packing_load` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1209) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_bin_packing_load.mzn) |
| `fzn_bounded_dpath` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1309) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_bounded_dpath_int.mzn) |
| `fzn_bounded_path` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1302) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_bounded_path_int.mzn) |
| `fzn_circuit` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1247) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_circuit.mzn) |
| `fzn_connected` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1264) | SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_connected.mzn) |
| `fzn_cost_mdd` | restricted | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L966) | SC-04, SC-06; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_cost_mdd.mzn) |
| `fzn_cost_regular` | restricted | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L953) | SC-02; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_cost_regular.mzn) |
| `fzn_count_eq` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L437) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_eq.mzn) |
| `fzn_count_eq_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L441) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_eq_par.mzn) |
| `fzn_count_eq_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L505) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_eq_set.mzn) |
| `fzn_count_eq_set_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L509) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_eq_set_par.mzn) |
| `fzn_count_geq` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L445) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_geq.mzn) |
| `fzn_count_geq_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L449) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_geq_par.mzn) |
| `fzn_count_geq_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L513) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_geq_set.mzn) |
| `fzn_count_gt` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L453) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_gt.mzn) |
| `fzn_count_gt_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L457) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_gt_par.mzn) |
| `fzn_count_gt_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L517) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_gt_set.mzn) |
| `fzn_count_leq` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L461) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_leq.mzn) |
| `fzn_count_leq_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L465) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_leq_par.mzn) |
| `fzn_count_leq_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L521) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_leq_set.mzn) |
| `fzn_count_lt` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L469) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_lt.mzn) |
| `fzn_count_lt_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L473) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_lt_par.mzn) |
| `fzn_count_lt_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L525) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_lt_set.mzn) |
| `fzn_count_neq` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L477) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_neq.mzn) |
| `fzn_count_neq_par` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L481) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_neq_par.mzn) |
| `fzn_count_neq_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L529) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_count_neq_set.mzn) |
| `fzn_cumulative` | restricted | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1237) | SC-09; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_cumulative.mzn) |
| `fzn_cumulatives` | restricted | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L768) | SC-04, SC-12; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_cumulatives.mzn) |
| `fzn_cumulatives_decomp` | restricted | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L773) | SC-04, SC-12; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_cumulatives_decomp.mzn) |
| `fzn_dag` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1260) | SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dag.mzn) |
| `fzn_dconnected` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1268) | SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dconnected.mzn) |
| `fzn_diffn` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1217) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_diffn.mzn) |
| `fzn_diffn_k` | unsupported | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L796) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_diffn_k.mzn) |
| `fzn_diffn_nonoverlap_k` | reviewed | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L792) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_diffn_k.mzn) |
| `fzn_diffn_nonstrict` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1221) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_diffn_nonstrict.mzn) |
| `fzn_diffn_nonstrict_k` | unsupported | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L800) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_diffn_nonstrict_k.mzn) |
| `fzn_disjoint` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L982) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_disjoint.mzn) |
| `fzn_disjunctive` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1229) | SC-04, SC-11; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_disjunctive.mzn) |
| `fzn_disjunctive_strict` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1233) | SC-04, SC-11; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_disjunctive_strict.mzn) |
| `fzn_distribute` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L485) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_distribute.mzn) |
| `fzn_dpath` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1297) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dpath_int.mzn) |
| `fzn_dreachable` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1277) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dreachable_int.mzn) |
| `fzn_dsteiner` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1320) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dsteiner.mzn) |
| `fzn_dtree` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1287) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dtree_int.mzn) |
| `fzn_dwst` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1328) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_dwst.mzn) |
| `fzn_exactly_int` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L433) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_exactly_int.mzn) |
| `fzn_exactly_set` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L541) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_exactly_set.mzn) |
| `fzn_geost` | restricted | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L778) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_geost.mzn) |
| `fzn_geost_bb` | restricted | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L782) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_geost_bb.mzn) |
| `fzn_geost_nonoverlap_k` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1225) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_geost_nonoverlap_k.mzn) |
| `fzn_geost_smallest_bb` | restricted | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L787) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_geost_smallest_bb.mzn) |
| `fzn_global_cardinality` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L489) | SC-04, SC-10; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_global_cardinality.mzn) |
| `fzn_global_cardinality_closed` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L493) | SC-04, SC-10; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_global_cardinality_closed.mzn) |
| `fzn_global_cardinality_low_up` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L497) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_global_cardinality_low_up.mzn) |
| `fzn_global_cardinality_low_up_closed` | restricted | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L501) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_global_cardinality_low_up_closed.mzn) |
| `fzn_if_then_else_bool` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1249) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_bool.mzn) |
| `fzn_if_then_else_int` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1245) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_int.mzn) |
| `fzn_if_then_else_partiality` | reviewed | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L808) | SC-04, SC-13; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_partiality.mzn) |
| `fzn_if_then_else_set` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1253) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_set.mzn) |
| `fzn_if_then_else_var_bool` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1249) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_var_bool.mzn) |
| `fzn_if_then_else_var_int` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1245) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_var_int.mzn) |
| `fzn_if_then_else_var_set` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1253) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_if_then_else_var_set.mzn) |
| `fzn_increasing_bool` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L730) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_increasing_bool.mzn) |
| `fzn_increasing_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L726) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_increasing_int.mzn) |
| `fzn_int_set_channel` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L688) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_int_set_channel.mzn) |
| `fzn_inverse` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L680) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_inverse.mzn) |
| `fzn_inverse_in_range` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L684) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_inverse_in_range.mzn) |
| `fzn_knapsack` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1213) | SC-04, SC-14; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_knapsack.mzn) |
| `fzn_lex2` | unsupported | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L288) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex2.mzn) |
| `fzn_lex_chain_greater_int` | extension | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L300) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_less_int.mzn) |
| `fzn_lex_chain_greatereq_int` | extension | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L304) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_lesseq_int.mzn) |
| `fzn_lex_chain_greatereq_orbitope` | extension | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L308) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_lesseq_orbitope.mzn) |
| `fzn_lex_chain_less_int` | unsupported | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L280) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_less_int.mzn) |
| `fzn_lex_chain_lesseq_int` | unsupported | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L284) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_lesseq_int.mzn) |
| `fzn_lex_chain_lesseq_orbitope` | unsupported | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L296) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_chain_lesseq_orbitope.mzn) |
| `fzn_lex_greater_int` | extension | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L272) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_less_int.mzn) |
| `fzn_lex_greatereq_int` | extension | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L276) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_lesseq_int.mzn) |
| `fzn_lex_less_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L718) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_less_int.mzn) |
| `fzn_lex_lesseq_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L722) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_lex_lesseq_int.mzn) |
| `fzn_link_set_to_booleans` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L692) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_link_set_to_booleans.mzn) |
| `fzn_maximum_arg_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L746) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_arg_max_int.mzn) |
| `fzn_mdd` | reviewed | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L958) | SC-04, SC-06; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_mdd.mzn) |
| `fzn_mdd_nondet` | restricted | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L962) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_mdd_nondet.mzn) |
| `fzn_member_bool` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L700) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_member_bool.mzn) |
| `fzn_member_int` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L696) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_member_int.mzn) |
| `fzn_member_set` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L704) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_member_set.mzn) |
| `fzn_minimum_arg_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L753) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_arg_min_int.mzn) |
| `fzn_neural_net` | unsupported | [Globals](../../LeanFzn/Semantics/Globals.lean) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_neural_net.mzn) |
| `fzn_nvalue` | reviewed | [Counting](../../LeanFzn/Semantics/Globals/Counting.lean#L417) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_nvalue.mzn) |
| `fzn_partition_set` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L990) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_partition_set.mzn) |
| `fzn_path` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1292) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_path_int.mzn) |
| `fzn_piecewise_linear` | unsupported | [Globals](../../LeanFzn/Semantics/Globals.lean) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_piecewise_linear.mzn) |
| `fzn_piecewise_linear_non_continuous` | unsupported | [Globals](../../LeanFzn/Semantics/Globals.lean) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_piecewise_linear_non_continuous.mzn) |
| `fzn_range` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1006) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_range.mzn) |
| `fzn_reachable` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1272) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_reachable_int.mzn) |
| `fzn_regular` | restricted | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L945) | SC-02; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_regular.mzn) |
| `fzn_regular_nfa` | restricted | [Regular](../../LeanFzn/Semantics/Globals/Regular.lean#L949) | SC-02; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_regular_nfa.mzn) |
| `fzn_roots` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1010) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_roots.mzn) |
| `fzn_seq_precede_chain_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L768) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_seq_precede_chain_int.mzn) |
| `fzn_set_member` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L986) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_set_member.mzn) |
| `fzn_sliding_among_bool` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1034) | SC-07; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sliding_among_bool.mzn) |
| `fzn_sliding_among_int` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1030) | SC-07; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sliding_among_int.mzn) |
| `fzn_sliding_sum` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1026) | SC-07; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sliding_sum.mzn) |
| `fzn_sort` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L738) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sort.mzn) |
| `fzn_span` | unsupported | [Globals](../../LeanFzn/Semantics/Globals.lean) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_span.mzn) |
| `fzn_steiner` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1316) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_steiner.mzn) |
| `fzn_strict_lex2` | unsupported | [LexChain](../../LeanFzn/Semantics/Globals/LexChain.lean#L292) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_strict_lex2.mzn) |
| `fzn_strictly_increasing_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L734) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_strictly_increasing_int.mzn) |
| `fzn_subcircuit` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1251) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_subcircuit.mzn) |
| `fzn_subgraph` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1255) | SC-01; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_subgraph_int.mzn) |
| `fzn_sum_pred` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L1002) | SC-04, SC-08, SC-15; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sum_pred.mzn) |
| `fzn_sum_set` | reviewed | [SetMath](../../LeanFzn/Semantics/Globals/SetMath.lean#L998) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_sum_set.mzn) |
| `fzn_symmetric_all_different` | reviewed | [AllDiffCounting](../../LeanFzn/Semantics/Globals/AllDiffCounting.lean#L833) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_symmetric_all_different.mzn) |
| `fzn_table_int` | reviewed | [PackSched](../../LeanFzn/Semantics/Globals/PackSched.lean#L1241) | SC-03; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_table_int.mzn) |
| `fzn_tree` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1282) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_tree_int.mzn) |
| `fzn_value_precede_chain_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L764) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_value_precede_chain_int.mzn) |
| `fzn_value_precede_int` | reviewed | [LexSort](../../LeanFzn/Semantics/Globals/LexSort.lean#L760) | —; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_value_precede_int.mzn) |
| `fzn_write` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L716) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_write.mzn) |
| `fzn_writes` | reviewed | [Channeling](../../LeanFzn/Semantics/Globals/Channeling.lean#L720) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_writes.mzn) |
| `fzn_writes_seq` | reviewed | [Sched2](../../LeanFzn/Semantics/Globals/Sched2.lean#L804) | SC-04; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_writes_seq.mzn) |
| `fzn_wst` | reviewed | [Graph](../../LeanFzn/Semantics/Globals/Graph.lean#L1324) | SC-01, SC-05; [reference](https://github.com/MiniZinc/libminizinc/blob/c3448c48e7f05f13805616cfd1b9e94972eef58c/share/minizinc/std/fzn_wst.mzn) |
| `int2float` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-float.html#int2float) |
| `int_abs` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L956) | —; [reference](lib-flatzinc-int.html#int-abs) |
| `int_div` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L940) | —; [reference](lib-flatzinc-int.html#int-div) |
| `int_eq` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L821) | —; [reference](lib-flatzinc-int.html#int-eq) |
| `int_eq_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L845) | —; [reference](lib-flatzinc-int.html#int-eq-reif) |
| `int_ge` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L837) | —; [reference](lib-flatzinc-int.html#int-le) |
| `int_ge_reif` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L861) | —; [reference](lib-flatzinc-int.html#int-le-reif) |
| `int_gt` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L841) | —; [reference](lib-flatzinc-int.html#int-lt) |
| `int_gt_reif` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L865) | —; [reference](lib-flatzinc-int.html#int-lt-reif) |
| `int_le` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L829) | —; [reference](lib-flatzinc-int.html#int-le) |
| `int_le_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L853) | —; [reference](lib-flatzinc-int.html#int-le-reif) |
| `int_lin_eq` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1073) | SC-04; [reference](lib-flatzinc-int.html#int-lin-eq) |
| `int_lin_eq_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1085) | SC-04; [reference](lib-flatzinc-int.html#int-lin-eq-reif) |
| `int_lin_le` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1077) | SC-04; [reference](lib-flatzinc-int.html#int-lin-le) |
| `int_lin_le_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1097) | SC-04; [reference](lib-flatzinc-int.html#int-lin-le-reif) |
| `int_lin_ne` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1081) | SC-04; [reference](lib-flatzinc-int.html#int-lin-ne) |
| `int_lin_ne_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1106) | SC-04; [reference](lib-flatzinc-int.html#int-lin-ne-reif) |
| `int_lt` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L833) | —; [reference](lib-flatzinc-int.html#int-lt) |
| `int_lt_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L857) | —; [reference](lib-flatzinc-int.html#int-lt-reif) |
| `int_max` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L952) | —; [reference](lib-flatzinc-int.html#int-max) |
| `int_min` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L948) | —; [reference](lib-flatzinc-int.html#int-min) |
| `int_minus` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L932) | —; [reference](lib-flatzinc-int.html#int-plus) |
| `int_mod` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L944) | —; [reference](lib-flatzinc-int.html#int-mod) |
| `int_ne` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L825) | —; [reference](lib-flatzinc-int.html#int-ne) |
| `int_ne_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L849) | —; [reference](lib-flatzinc-int.html#int-ne-reif) |
| `int_plus` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L928) | —; [reference](lib-flatzinc-int.html#int-plus) |
| `int_pow` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L960) | —; [reference](lib-flatzinc-int.html#int-pow) |
| `int_pow_fixed` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L964) | —; [reference](lib-flatzinc-twotwoone.html#int-pow-fixed) |
| `int_times` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L936) | —; [reference](lib-flatzinc-int.html#int-times) |
| `max` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twooneone.html#max) |
| `min` | unsupported | [StdLib](../../LeanFzn/Semantics/StdLib.lean) | —; [reference](lib-flatzinc-twooneone.html#min) |
| `set_card` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L981) | —; [reference](lib-flatzinc-set.html#set-card) |
| `set_diff` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1055) | —; [reference](lib-flatzinc-set.html#set-diff) |
| `set_eq` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L985) | —; [reference](lib-flatzinc-set.html#set-eq) |
| `set_eq_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L989) | —; [reference](lib-flatzinc-set.html#set-eq-reif) |
| `set_in` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L968) | —; [reference](lib-flatzinc-set.html#set-in) |
| `set_in_reif` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L972) | —; [reference](lib-flatzinc-set.html#set-in-reif) |
| `set_intersect` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1050) | —; [reference](lib-flatzinc-set.html#set-intersect) |
| `set_le` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1005) | —; [reference](lib-flatzinc-set.html#set-le) |
| `set_le_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1009) | —; [reference](lib-flatzinc-set.html#set-le-reif) |
| `set_lt` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1015) | —; [reference](lib-flatzinc-set.html#set-lt) |
| `set_lt_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1019) | —; [reference](lib-flatzinc-set.html#set-lt-reif) |
| `set_ne` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L995) | —; [reference](lib-flatzinc-set.html#set-ne) |
| `set_ne_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L999) | —; [reference](lib-flatzinc-set.html#set-ne-reif) |
| `set_subset` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1025) | —; [reference](lib-flatzinc-set.html#set-subset) |
| `set_subset_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1029) | —; [reference](lib-flatzinc-set.html#set-subset-reif) |
| `set_superset` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1035) | —; [reference](lib-flatzinc-set.html#set-superset) |
| `set_superset_reif` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1039) | —; [reference](lib-flatzinc-set.html#set-superset-reif) |
| `set_symdiff` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1060) | —; [reference](lib-flatzinc-set.html#set-symdiff) |
| `set_union` | reviewed | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1045) | —; [reference](lib-flatzinc-set.html#set-union) |
| `true` | extension | [StdLib](../../LeanFzn/Semantics/StdLib.lean#L1188) | —; [reference](fzn-spec.html#constraints) |

## Historical reference catalogue

The following is the original upstream name catalogue, retained for discovery.
Its use of “in scope” expresses an intended language fragment, not reviewed
implementation support. Use the reviewed rows above for current claims.

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

1. The pinned `fzn-grammar.mzn` is the syntax reference. `fzn-spec.html`
   supplies prose; `fzn-spec.md` is a derived reading copy. Builtin contracts
   are in the `lib-flatzinc-*.html` pages.
2. Native global predicate names and signatures must be checked against
   their pinned declarations, not inferred from a high-level global name.
   Plain project aliases and reversed-lex names are separately classified
   as extensions. A3 is not a current specification assumption.
3. The historical in-scope count is a reference catalogue, not an
   implementation or conformance claim. The reviewed inventory above is
   authoritative for current support; Boolean/Prop agreement alone does not
   relate a definition to the upstream library.

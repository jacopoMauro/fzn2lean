# FlatZinc Float Support Specification

This document specifies the float extension to the LeanFzn formalization of
FlatZinc (fzn2lean).  It is the step-3 deliverable that precedes any Lean
changes: **Section 5 (the predicate inventory) and Section 9 (out of scope) are
the part that must be implemented later**; everything else pins the decisions
that implementation must conform to.

Scope constraints inherited from `PLAN.md` item 3:

* This is a **specification-only** task.  No `.lean` file is modified, and
  nothing here licenses adding executable float predicates yet.
* Float support is **checker-only** (phase 0).  The search layer (`solver/`)
  remains int/bool; float decision variables are never enumerated (see §9).
* The numerical model, the rounding/serialization rules, and the predicate
  inventory are all fixed here, so that a later implementation phase has no
  choices left open.

Companion document: `flatzinc_specification_assumptions.md` ("the assumption
spec").  Decision records there use the R/A/G series.  The decisions recorded
here use the **F series**, and where a float decision amends an earlier record
it says so explicitly.  The MiniZinc 2.10.0 sources are pinned at commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (vendored under
`specification/minizinc-2.10.0/`), as in the assumption spec.

Lean file:line references below point at the current corpus
(lean 4.33.1, core-only — the project has **no mathlib dependency**).

---

## 1. Numerical-model decision

**Resolution F1 (float value model is ℚ, not binary64).**  Float values are
rational numbers: value and literal representation `Value.float (r : Rat)`,
using **core Lean's** `Rat` (normalized numerator/denominator pairs;
`Rat.normalize`).  This amends A6/G33-family records that excluded floats.

Rationale: every `<float-literal>` (grammar lines 73–75) is a finite decimal,
hence a rational whose reduced denominator divides a power of 10, so whenever a
float value is *written down* it is exactly representable in ℚ; and core
`Rat` has decidable equality and decidable order (`decide (a = b)`,
`decide (a ≤ b)`, `decide (a < b)` all compute; `d = 2^a·5^b`), so the solution
checker stays exact and total — no rounding, no `NaN`/`inf`, no ulps.  Machine
`Float` is rejected: it is not a field, its arithmetic is approximate so the
equality and round-trip theorems could not hold, and an axiomatized `Float`
would pollute the `verify`-clean proof chain.  Exact `ℝ` is also rejected: the
fragment only ever names finite decimals, so ℝ gives nothing that ℚ does not
already give, and it is not representable finitely.

**Consequences of F1 (in-scope condition).**  A float builtin is in scope iff
its ℝ-realization is **guaranteed rational-valued on rational inputs** and its
truth is decidable.  This puts in scope: comparison, `abs`/`max`/`min`, `+`
`×` `÷` (with `y ≠ 0` guard, mirroring G2 for `int_div`), integer-coefficient
linear combinations, element access, `int2float`, `ceil`/`floor`/`round`, and
array maximum/minimum.  It puts out of scope every predicate that is
irrational-valued or transcendental even on rational inputs — `float_sqrt`
included, since `√q` is not in general rational — see §9.

**Resolution F2 (canonical float literal = serialization).**  Canonical
(write-out) form is the plain decimal alternative
`[-]?[0-9]+ '.' [0-9]+` of the `<float-literal>` grammar, with **no exponent**,
no trailing zeros, and **at least one digit on each side of the `.`**.  The
bijection between serializer and parser is:

1. `q = 0` → `0.0` (the floating point value of zero; `-0.0` parses to the same
   value and is never printed, since `q < 0` fails for `0`).
2. For `q ≠ 0`, take the reduced fraction `q = ±n/d` with `d = 2^a·5^b`
   (finite-decimal condition).  Let `k0 = max a b`, `k = max k0 1` (integers
   keep one fractional `0`), and `M = n·10^k / d` (an integer).
3. Strip **trailing** zeroes of `M` while `k > 1` (fractional part keeps at
   least one digit): repeatedly `(M, k) := (M/10, k−1)` while `k > 1` and
   `M mod 10 = 0`.
4. Emit `sign` if `n < 0`, then the decimal digits: integer part is the leading
   `len(M) − k` digits (zero-padded on the left to at least one digit), `.`,
   and the final `k` digits as the fractional part.

The four canonical examples, as required:

| value | reduced | k | printed |
|-------|---------|---|---------|
| `1/2`    | 1/2         | 1 | `0.5`    |
| `1/1000` (input `1e-3`) | 1/1000 | 3 | `0.001`  |
| `-1/2`   | −1/2        | 1 | `-0.5`   |
| `3/2` (input `1.50`) | 3/2 | 1 | `1.5`   |

Published/large cases: `5` prints `5.0` (not `5` — an int literal), `100000`
prints `100000.0`, `375/1000 = 3/8` prints `0.375`.  The printed string always
satisfies the grammar, needs no exponent, has no `+` sign, and re-tokenizes to a
`floatLit` whose value is propositionally equal to the original rational.

**Resolution F3 (serializable fragment).**  A float value is serializable iff
its reduced denominator shows only primes `2` and `5`.  Arithmetic stays total
and exact: `float_div` returns `1/3` as a rational, but `1/3` has **no**
canonical form and fails at the output boundary (documented "non-terminating
decimal"; the checker reports the attempt rather than guessing).  This is the
single rounding-related consequence of the ℚ model — there is no other
rounding anywhere.

---

## 2. Syntax and grammar changes

The pinned `.g4`/`.mzn` grammar already admits floats; the change is purely on
the lexical side plus token plumbing.  No grammar production is added.

**Facts pinned from `fzn-grammar.mzn` (MiniZinc 2.10.0):**

* `<float-literal>` (lines 73–75) — three alternatives:
  `[-]?[0-9]+.[0-9]+`, `[-]?[0-9]+.[0-9]+[Ee][-+]?[0-9]+`,
  `[-]?[0-9]+[Ee][-+]?[0-9]+`.  `.5` is **not** a literal (must be `0.5`);
  `[Ee]` exponent is optional and carries an optional sign.  No `NaN`/`inf` is
  expressible.
* `<basic-par-type>` includes `"float"` (line 22).
* `<basic-var-type>` includes `"var" <float-literal> ".." <float-literal>`
  (line 28).
* `<basic-pred-param-type>` includes `<float-literal> ".." <float-literal>`
  (line 39).
* `<basic-literal-expr>` includes `<float-literal>` (line 52), so floats occur
  as variable initializers, `par` declares, and `minimize`/`maximize` objects.
* `<set-literal>` includes `{<float-literal>,...}` and
  `<float-literal> ".." <float-literal>` (lines 80–81) — **dead syntax**, see
  F-gap-A1 in §5.

**Lexer (`LeanFzn/FznLexer.lean`):**

* `Token` (line 27; doc "non-float fragment" at line 26 is thereby outdated):
  add `floatLit (q : Rat)`.  Currently only `intLit (i : Int)` exists (line 44).
* `"float"` currently sits in `reservedNonFzn` (line 52); it must move to
  `keywordToken` (line 58) as `"float" => some .kwFloat`, with a new `kwFloat`
  token.  The word is reserved either way, so **no new reserved-word conflict
  arises** — this is why `"float"` was already reserved.
* Number scanning: `lexInt` (line 304) and the dispatch at `isDigit`/`'-'`
  (line 477) grow into a `lexNumber` that consumes the `<float-literal>`
  alternatives: after `[-]?digits`, if the next char is `.` followed by a
  digit, consume the fraction and an optional `[Ee][-+]?digits`; else if it is
  `[Ee][-+]?digits` directly, consume the exponent.  The current lone-`.` path
  (an error for any stray `.`) stays for isolated dots; the `..` token is
  unaffected.
* Value construction: mantissa digits → `M : Int`, fractional scale `f`, signed
  exponent `e ∈ ℤ`; `q = Rat.normalize (M div (10^f))` shifted by `10^e`,
  i.e. build `Rat.normalize m (10^d)` with sign folded, exactly as the grammar
  defines.  `1e-3` therefore lexes to the single token `floatLit (1/1000)`, not
  `intLit 1` + `ident "e"`... (today's failure), and `1.50` to `floatLit (3/2)`.

**Grammar relation (`LeanFzn/FznGrammar.lean`):** `GrBasicLiteral` gains the
`floatLit` case; the par/var/pred-param range productions map to the new AST
constructors of §3.  `GrIntAtom`/`GrBasicParType.deterministic` theorems gain
their float twins.

---

## 3. AST changes

All in `LeanFzn/FznAST.lean`:

* `BasicLiteral` (line 39): add constructor `float (q : Rat)`.
* `BasicParType` (line 64): add `float`.
* `BasicVarType` (line 71): add `floatRange (lo hi : Rat)` for
  `var <float-literal> ".." <float-literal>`.
* `BasicPredParamType` (line 91): add `floatRange (lo hi : Rat)`.
* `SetLiteral` (line 33): **unchanged** — stays `intSet | intRange`; float set
  literals are statically rejected (§5, F-gap-A1) and get no constructor.
* Pretty printer `FznPretty.lean`: `BasicLiteral.pp` gains the `float` case,
  printing with the F2 canonical form; all other pp cases unchanged.

---

## 4. Semantics changes

**`LeanFzn/FznSemantics.lean`:**

* `BaseType` (line 13): add `float`.
* `Value` (line 27): add `float (q : Rat)`.  Extend the instance line
  (currently `deriving Repr, Inhabited`, line 32) with `DecidableEq` — core
  `Rat` has decidable equality, so `Value` keeps it.
* `BasicLiteral.denote` (line 46) / `.type` (line 51):
  `| .float q => .float q`, `| .float q => .float`.
* `BasicParType.base` (line 56): `| .float => .float`.
* `BasicVarType.base` (line 76): `| .floatRange lo hi => .float`;
  `BasicVarType.contains` (line 81): `| .floatRange lo hi => lo ≤ q ∧ q ≤ hi`.
* `BasicPredParamType.baseType` / `isPar` / `accepts` (lines 167/176/182):
  add the `floatRange` cases (`isPar` = false).
* `SolveItem.objective` (line 98) currently returns `Option Int`.  The grammar
  allows any `<basic-literal-expr>` as the minimize/maximize object,
  `<float-literal>` included — so **R7 (int objective) is amended**:
  the objective becomes a float-compatible value, e.g. `Option (BasicLiteral)`
  (carrying a `.float` or `.int`) or `Option (MValue)` with a suitable
  well-formedness predicate `isNumericValue`.  `solveObjB_iff` (line 504)
  generalizes accordingly.  Optimality remains *out* of the checker's scope
  (§9), as before — the checker validates assignments and compares declared
  objectives for ties only insofar as existing behavior does.

**`LeanFzn/FznStdLib.lean`:**

* `Value.eqB` (line 77): add the `.float q₁ · float q₂` case = `q₁ = q₂`
  via `decide`.
* `stdSig` (line 588), `stdInterp` (line 801), `stdInterpB` (line ~1181) and
  their `wellFormedB_iff` / agreement layers gain exactly the predicates of
  §5's in-scope table.  The float element and array-maximum predicates reuse
  the `valuesGet1` (line 458) and `maxValue`/`minValue` (lines 1136–1143)
  scaffolding; float twins `maxFloatValue`/`minFloatValue` mirror the int ones.
* Type relation `HasType`/`contains`/`acceptedValues` for float types as in §4
  (semantics), with the float-range bounds comparisons decidable.

**Checker (`LeanFzn/FznSolution.lean`/`FznCheck.lean`):** `parseScalarEntry`
(line 244) and `parseArray1d` (line 223) accept a `floatLit` token, and the
solution grammar doc (lines 11, 55) mentions `x = 0.5;` /
`xs = array1d(1..n, [0.25, 1.5]);`.  `interpB` and the `stdInterpB_agree`
family (line ~1200) extend with the float cases, exactly as the int twins.

---

## 5. Standard-predicate inventory

Sources: handbook pages `lib-flatzinc-float.html` (base float builtins,
2.10.0) and `lib-flatzinc-2*.html` (versioned additions), cross-checked
against `predicates_and_globals_report.md` lines 110–161.  Signatures below
were copied from the vendored pages.

**Totals: 53 float family names documented by the report
(43 base + 10 versioned).  In scope here: 33.  Out of scope: 20.**

### 5.1 In scope — comparisons (8)

`float_eq x y`, `float_ne x y`, `float_le x y`, `float_lt x y`
(`x = y`, `x ≠ y`, `x ≤ y`, `x < y`), plus reified
`float_*_reif x y b` (`b ↔ x ⋈ y`).  Signatures:
`predicate float_{eq,ne,le,lt}(var float: x, var float: y)`,
`predicate float_{eq,ne,le,lt}_reif(var float: x, var float: y, var bool: b)`.

Note: there are **no** `float_ge`/`float_gt` builtins (only the int fragment
has `int_ge`/`int_gt`); MiniZinc normalizes float `>=`/`>` to `<=`/`<` by
swapping the operands.  Do not add them.

### 5.2 In scope — arithmetic (6)

* `float_abs(var float: x, var float: y)` — `y = |x|`.
* `float_max`/`float_min`(`var float: x, var float: y, var float: z`) — `z = max x y`.
* `float_plus`/`float_times`(`var float: x, var float: y, var float: z`) — `z = x + y`, `z = x · y`.
* `float_div`(`var float: x, var float: y, var float: z`) — `z = x / y ∧ y ≠ 0`
  (guard mirrors G2/`int_div`).

There is **no** `float_mod` builtin (`mod` is integer-only in FlatZinc; a
search of the vendored pages and the report for `float_mod` is empty).  **F4.**
A `.fzn` that names an unknown predicate is rejected by the closed signature
environment (A3 behavior), the same as for any non-inventoried name.

### 5.3 In scope — linear (8)

`float_lin_eq`, `float_lin_le`, `float_lin_lt`, `float_lin_ne`, each with a
`_reif` twin:

* `float_lin_eq(array [int] of float: as, array [int] of var float: xs, float: y)` — `Σᵢ as[i]·xs[i] = y`.
* `float_lin_eq_reif(... , float: y, var bool: b)` — `b ↔ Σ as[i]·xs[i] = y`.

Same shape for `le`/`lt`/`ne` (RHS is the **par float** `y`, both plain and
reified).  Length guard `length as = length xs` and 1-based indexing carry over
from the int twins; coefficients are par floats, matching the handbook (the int
analogue `int_lin_eq` differs: its plain form has a **var** RHS — do not
copy that detail to floats).

### 5.4 In scope — coercion (1)

* `int2float(var int: x, var float: y)` — `y = x` (the ℤ→ℚ embedding is exact).

`bool2float` is verified **not** a FlatZinc builtin (it exists only at
MiniZinc level, `stdlib.mzn`; the vendored builtin pages and report contain no
`bool2float`).  **F5.** It is not added; a `bool → float` conversion in `.fzn`
would surface as `int2float` after equal-valued rewriting.

### 5.5 In scope — element (2)

* `array_float_element(var int: idx, array [int] of float: xs, var float: y)` — `y = xs[idx]`.
* `array_var_float_element(var int: idx, array [int] of var float: xs, var float: y)` — `y = xs[idx]`.

Both use 1-based `valuesGet1` (index in `1..n`; out of range is false),
matching every existing element twin.

### 5.6 In scope — versioned additions (8)

* 2.0.0 (2): `array_float_maximum(var float: m, array [int] of var float: xs)`
  and `array_float_minimum` — `m = max/min xs`, mirroring the supported int
  twins `array_int_maximum`/`array_int_minimum` (`maxFloatValue xs = some m`).
* 2.0.2 (1): `array_var_float_element_nonshifted(var int: idx, array [int] of
  var float: xs, var float: y)` — coincides with `array_var_float_element`
  under the project's `1..n` index-sets convention (as the int `_nonshifted`
  twins already do, FznStdLib.lean lines 1166–1170).
* 2.1.0 (2): `float_in(var float: x, float: l, float: u)` — `l ≤ x ≤ u`;
  `float_dom(var float: x, array [int] of float: as)` — `x ∈ ⋃ᵢ [as[2i−1], as[2i]]`
  (pairs-of-ranges domain form; out-of-range/non-pair arguments are false).
* 2.7.1 (3): `float_ceil(var float: x, var int: y)` — `y = ⌈x⌉`;
  `float_floor(var float: x, var int: y)` — `y = ⌊x⌋`;
  `float_round(var float: x, var int: y)` — `y = round(x)`, **F6: ties round
  half away from zero** (matching standard `round` and Gecode float behavior).
  Note the outputs are `var int` per the handbook.

**Grand total in scope: 8 + 6 + 8 + 1 + 2 + 8 = 33.**

### 5.7 Out of scope — base float builtins (18)

`float_acos`, `float_acosh`, `float_asin`, `float_asinh`, `float_atan`,
`float_atanh`, `float_cos`, `float_cosh`, `float_exp`, `float_ln`,
`float_log10`, `float_log2`, `float_pow`, `float_sin`, `float_sinh`,
`float_sqrt`, `float_tan`, `float_tanh`.

Reason: irrational/transcendental even on rational inputs; their transformations
are not rational-exact and would violate F1/F3.  (`float_pow` additionally gets
an integer-exponent restriction if ever revisited; `float_sqrt` stays out
because `√q ∉ ℚ` in general.)

### 5.8 Out of scope — versioned additions (2)

* `float_set_in(var float: x, set of float: s)` (2.3.3).
* `array_var_float_element2d_nonshifted(var int: idx1, var int: idx2,
  array [int,int] of var float: xs, var float: y)` (2.5.2).

### 5.9 Decision records for the boundaries

**F-gap-A1 (`set of float` type gap).**  The grammar's
`<basic-pred-param-type>` has **no** `set of float` production (lines 36–42
offer only `set of int`, int sets, and float *ranges*), yet
`<set-literal>` (lines 80–81) admits `{1.5, 2.5}` and `1.5..2.5`.  So a value
can be *written* as a float set but no *type* can denote it.  Consequently
`float_set_in`'s declared argument type is not grammar-representable, and float
set literals are untypeable dead syntax.  **Decision:** `float_set_in` is out
of scope until the grammar is extended; float set literals are a static error.
The two grammar clauses are recorded here as an upstream inconsistency, not
implemented.

**F-gap-A2 (`_imp` half-reification).**  fzn-spec.md lines 887–910 define
`_imp` predicates (`float_eq_imp(x, y, b)`, etc.) as optional
*solver-provided* half-reified variants.  They are not part of the builtin
catalog (absent from `predicates_and_globals_report.md`); the project's closed
signature environment therefore does not admit them (A3).  **Decision:** out
of scope unless and until the fragment explicitly adopts half-reification.

**F7 (uninventoried names).**  Any float-family name in a `.fzn` that is not in
the 53-name catalog above (e.g. a hypothetical `float_mod`, `float_ge`,
`bool2float`, `*_imp`) is rejected at static-analysis time — the closed
environment behavior already used for the int/bool fragment.

---

## 6. Solution format

* `ParseTokens`/solution parser (`FznSolution.lean`): the solution grammar
  (lines 11, 51–57) gains `floatLit`.  `parseScalarEntry` (line 244)
  and `parseArray1d` (line 223) produce `Value.float b` entries.
* Entries still assign **variables** only (A7/A10 unchanged); a float entry is
  exactly `x = 0.5;` / `xs = array1d(1..n, [0.25, 1.5]);`.
* Round-trip: the F2 canonical printer is injective into the solution token
  stream and `parse(print q) = q` for every serializable rational — this is a
  theorem (§8), not an assumption.
* `interpB` / `stdInterpB_agree` extensions make float solution values compare
  by exact `Rat` equality.

---

## 7. Globals impact

`globalsUnsupported` (`FznGlobals.lean`, line 590) currently lists
`fzn_alternative`, `fzn_span`, `fzn_neural_net`, `fzn_piecewise_linear`,
`fzn_piecewise_linear_non_continuous`.  The float decision changes the status
of the three float-argument entries:

* `fzn_piecewise_linear` / `fzn_piecewise_linear_non_continuous` become
  **enumerable** in principle: piecewise-linear interpolation of rational
  breakpoints is rational-valued and its truth is decidable.  They migrate out
  of `globalsUnsupported` only when their pinned `fzn_*.mzn` decompositions are
  formalized — the report keeps them deferred for phase 0, **F8**, because
  their semantics are defined by the *decomposition files*, not by the core
  fragment (and must be implemented after the 33 inventory predicates exist).
* `fzn_neural_net` depends on its activation decomposition; ReLU-like layers
  are ℚ-exact, arbitrary activations are not.  Deferred with F8.
* `fzn_alternative` / `fzn_span` need optional types (`var opt`) — remain
  unsupported (unchanged).
* No `fzn_*float*` globals exist anywhere in the catalog (grep negative); the
  float extension adds none.

The `fzn_*` decomposition families in `LeanFzn/FznGlobals/` are untouched.

---

## 8. Proof plan

The theorems below are the ones a later phase must state and prove; each
mirrors an already-existing int/bool proof and reuses its scaffolding.

1. **Lexer.** `lexNumber`/`lexFloat` progress and totality;
   `floatLit_reparse`: the F2 canonical printer yields a token that the parser
   rewinds to the same `Rat`, and the canonical form is unique among
   exponent-free `[0-9]+\.[0-9]+` strings.
2. **Grammar.** `GrBasicLiteral`/`GrBasicParType.deterministic`-style
   uniqueness for the float alternatives.
3. **AST/semantics.** Type/denote/contains/acceptedValues cases for
   `BasicLiteral.float`, `BasicParType.float`, `BasicVarType.floatRange`,
   `BasicPredParamType.floatRange`; `solveObjB_iff` generalization for float
   objectives (amends R7).
4. **StdLib.** Per-name agreement `builtin_<name>_iff` for each of the 33
   inventory predicates (§5), then the full `stdInterpB_agree` /
   `checkSolutionFull_correct` extension for float solution values.
   Rat-specific facts needed (all decidable over core `Rat`): field laws for
   `+` `×` `÷` on normalized fractions, `|q|`, `max`/`min`, `⌈q⌉`/`⌊q⌋`,
   half-away-from-zero rounding.
5. **Domain guards.** `float_div` twin is false at `y = 0` (mirrors G2);
   element/maximum/minimum twins false outside `1..n` resp. empty arrays
   (mirror `valuesGet1`, `maxValue`).
6. **Round-trip.** F2 injectivity + `parse(print q) = q` over the serializable
   fragment (denominators `2^a·5^b`); the additional theorem that
   non-terminating values have no canonical form (F3).
7. **Tests.** Handbook float examples + Gecode float reference cases; extend
   `Tests/Coverage` for the new names.  The existing int/bool suites must stay
   green (no behavior change outside the new fragment).

---

## 9. Out of scope / deferred

* **20 float builtins** of §5.7–5.8 (transcendental/irrational `sin`-family,
  `exp`/`ln`/`log*`/`pow`/`sqrt`, and `float_set_in`, 2D element) — F1's
  rational-exactness condition excludes them.  Notably `float_sqrt` is excluded
  despite being elementary.
* **Machine `Float` / IEE-754 semantics**, and any rounding mode other than
  exact-with-mandatory-`0` fractional ("rounding" only exists in
  `float_round`'s *definition*, F6, and in the F2 output padding).
* **Non-terminating-decimal float values** (F3) — printable fragment only.
* **Float decision-variable search** (`solver/*.lean`): float domains are
  infinite; the solver stack remains int/bool.  Checker-only float support.
* **Optimality over float objectives** — the checker validates assignments,
  it does not decide optimality (unchanged from the int fragment).
* **`_imp` half-reified predicates** and **`bool2float`** (F5, F-gap-A2).
* **`set of float` types and float set literals** (F-gap-A1), **2D float
  arrays** (no 2D arrays in the fragment), **`float_mod`**/`float_ge`/
  `float_gt` (do not exist upstream; F7/F4).
* **`fzn_piecewise_linear*` / `fzn_neural_net`** reclassification (F8) — after
  the 33 inventory predicates land.

---

## Summary of decisions

| # | Question | Decision |
|---|----------|----------|
| F1 | numerical model | rationals `Rat` (core), `Value.float (q : Rat)`; exact, decidable |
| F2 | output form | canonical `[-]ddd.ddd`, no exponent, ≥1 digit each side, no trailing zeros |
| F3 | non-terminating decimals | not serializable; `float_div` still exact/total |
| F4 | `float_mod` | does not exist; absent from catalog (F7 applies) |
| F5 | `bool2float` | not a FlatZinc builtin; excluded |
| F6 | `float_round` | half away from zero |
| F7 | unknown float names | static rejection (closed env) |
| F8 | float globals | piecewise-linear/neural-net stay `unsupported` until inventory done |
| F-gap-A1 | `set of float` | grammar gap; `float_set_in` + float set literals out |
| F-gap-A2 | `_imp` half-reif | solver-optional, out of closed fragment |
| R7 (amended) | objective type | int *or* float, via §4 |
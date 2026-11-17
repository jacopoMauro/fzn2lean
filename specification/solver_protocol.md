# LeanFzn structured solver protocol v1 (`--report=jsonl-v1`)

Status: frozen in P0 of the certification-boundary wave (2026-11-14). The
schema, event order, terminal/exit table and cancellation rule in this file are
the contract for the Lean codec, the CLI driver and `minizinc-wrapper/fzn-leanfzn`.
Changes require a version bump (`jsonl-v2`) and a migration note to every
consumer.

The default output remains the FlatZinc text format (`--report=text`), byte for
byte. This protocol is opt-in and is a reporting/transport option; it selects no
search strategy and changes no solver answer, counter or exit code.

Implementation status (final): the Lean emitter is
`LeanFzn/Integration/Report/{Basic,Codec,Runtime}`, the pure proof layer is
`Report/Proofs` and the streaming correspondence is `Report/T8`; the wrapper
state machine is `minizinc-wrapper/fzn-leanfzn`. `Tests/Cli/test_protocol.py`
and `Tests/Audits/test_wrapper_protocol.py` exercise the emitted stream and the
shipped wrapper, including cancellation and inconsistent-terminal failures.

## 1. Selection and stream

- Flag: `leanfzn solve --report=jsonl-v1 [OPTIONS] FILE|-`
- `--report=text` (default) keeps the existing human/FlatZinc output, stderr
  diagnostics and exit codes.
- `--report=jsonl-v1` writes **UTF-8 JSON Lines** on stdout: exactly one JSON
  object per line, each line terminated by `\n`. No other bytes go to stdout.
- stderr is not part of the protocol. `leanfzn: stats: ...`,
  `leanfzn: timing: ...`, warnings and human diagnostics stay on stderr in both
  modes. Statistics never appear on stdout in JSON mode.
- `--phase-stats` is a text-mode-only development diagnostic. Combining it
  with `--report=jsonl-v1` is a typed usage error (`error` kind `usage`,
  exit 2) emitted after the handshake; no phase lines or solver run occur.
- Records are emitted with Lean core's `Json.compress`. JSON strings are escaped
  by that printer; no value is produced by string interpolation.
- If the token `--report=jsonl-v1` appears in `solve` arguments, the handshake
  line is the first stdout line, including when a later argument, file read or
  model parse fails. An invalid `--report` value is a plain text usage error
  (exit 2), because the protocol is not selected.

## 2. Numeric conventions

- Solver integers and objective values are **canonical decimal strings**
  (`"-3"`, `"0"`, `"12345678901234567890"`), never JSON numbers, so clients
  cannot round them through floating point.
- Sequence ids (`id`) and the protocol version are JSON numbers.
- Exit codes in events are JSON numbers.
- Booleans are JSON booleans. An absent optional member is omitted, not `null`,
  except where a member is listed as nullable below.

## 3. Events

Every line has an `"event"` member. Unknown members are ignored by readers;
unknown `"event"` values, wrong types, a missing mandatory member, an unknown
protocol version or two handshakes are protocol errors in the wrapper.
Member order inside an object is not significant: readers must decode JSON,
not compare bytes. Examples below show one valid order.

### 3.1 Handshake (first line, exactly once)

```json
{"event":"handshake","protocol":"leanfzn-report","version":1}
```

### 3.2 Model metadata (after a successful load, before any solution)

```json
{"event":"model","mode":"satisfy","outputs":["x","y"]}
{"event":"model","mode":"minimize","objective":"obj","outputs":["obj"]}
{"event":"model","mode":"maximize","objective":null,"outputs":[]}
```

- `mode`: `"satisfy"`, `"minimize"` or `"maximize"`, from the parsed AST's
  solve item.
- `objective`: for optimization, the objective variable name when the objective
  expression is a bare identifier (`BasicExpr.ident`), otherwise `null`. The
  member is omitted for satisfaction models. This is metadata only; the
  canonical objective value is the `objective` member of solution events.
- `outputs`: the declared variable names annotated with `output_var` or
  `output_array`, in declaration order, without duplicates. The list is derived
  from the parsed AST annotations, not from model text scanning.
- Multiline declarations, several declarations per line, comments, annotation
  arguments, arrays and names merely containing the text `output_var` do not
  affect this list (tested in B1.3).

A typed early error (section 3.5) may appear instead of `model`; model metadata
is required before any solution event but not before an early error.

### 3.3 Solution

```json
{"event":"solution","id":1,"entries":[{"name":"x","text":"x = 1;"}],"objective":"5"}
```

- `id`: 1-based, strictly increasing by one in emission order.
- `entries`: every declared variable, in declaration order, with the exact
  canonical assignment line the text driver prints for that declaration
  (`text` has no trailing newline and no separator). The name is repeated as
  `name` so the wrapper filters by structured names without parsing FlatZinc.
  An empty model has `"entries":[]`; it is still a real solution record.
- `objective`: present only for optimization models; canonical decimal string
  of the objective value of this solution.
- An optimization solution event is emitted exactly when the text driver prints
  that improving incumbent. A satisfaction run emits at most one solution
  event. Each event is written and flushed atomically at the record level
  before any later event.

### 3.4 Terminal

```json
{"event":"terminal","kind":"sat","exit":0}
{"event":"terminal","kind":"optimal","exit":0,"solution":2}
{"event":"terminal","kind":"unsat","exit":1}
{"event":"terminal","kind":"incomplete","exit":4,"reason":"conflict limit reached"}
{"event":"terminal","kind":"unsupported","exit":3,"reason":"..."}
```

- Exactly one terminal event is the last line of a normal run.
- `kind` and `exit` must match the table in section 4. A mismatch is a protocol
  error in the wrapper.
- `optimal` carries `solution`: the `id` of the last emitted solution, which
  must be the report's best (last) witness. `sat` carries no `solution` member:
  the single solution event is the witness.
- `reason` is optional human text for `incomplete`/`unsupported`; it is escaped
  JSON and never selects a verdict.
- No solution, model or handshake event may follow a terminal event. A second
  terminal event is a protocol error.

### 3.5 Typed error

An error that prevents a normal terminal is reported as the last line:

```json
{"event":"error","kind":"usage","exit":2,"message":"..."}
{"event":"error","kind":"io","exit":2,"message":"..."}
{"event":"error","kind":"model_parse","exit":2,"message":"..."}
{"event":"error","kind":"unsupported","exit":3,"message":"..."}
{"event":"error","kind":"compile","exit":3,"message":"..."}
{"event":"error","kind":"internal","exit":2,"message":"..."}
```

Error kinds are finer than exit codes:

| `kind` | Meaning | Exit |
| --- | --- | --- |
| `usage` | bad option, missing argument, unsupported flag combination | 2 |
| `io` | model file unreadable, stdout write failure | 2 |
| `model_parse` | FlatZinc syntax/preprocessing failure in LeanFzn's parser | 2 |
| `unsupported` | classified scope failure (for example floats or an unimplemented construct) | 3 |
| `compile` | certified compiler/domain rejection (for example nonempty finite domain gate) | 3 |
| `internal` | report construction, rendering or sink failure; a bug or I/O fault | 2 |

A `model_parse` error keeps CLI exit 2. The MiniZinc wrapper's documented
mapping of `model_parse` to `=====UNSUPPORTED=====` (section 6) is a wrapper
policy under the assumption that MiniZinc produced valid FlatZinc; it does not
change the CLI exit code.

## 4. Terminal/exit consistency table

| Outcome | Event kind | CLI exit | Text-mode proof marker |
| --- | --- | --- | --- |
| Satisfied | `sat` | 0 | the single solution's `----------`; no optimum claim |
| Proved optimal | `optimal` | 0 | `==========` after the last witness |
| Certified UNSAT | `unsat` | 1 | `=====UNSATISFIABLE=====` |
| Unknown/incomplete | `incomplete` | 4 | none |
| Unsupported | `unsupported` | 3 | none |
| Invalid/IO/internal error | `error` | 2 | none |

`sat`/`optimal` are never emitted for a give-up. `unsat` and `optimal` are
emitted only from a certified completed source result. Diagnostics and
statistics never choose an event kind or terminal outcome. A checker reject, a
report-sink failure, an internal worker exception, or an UNSAT/optimum
contradiction is an `internal` `error` (exit 2), even after incumbents were
streamed; it is never converted into `incomplete` (exit 4), which is reserved
for genuine search exhaustion.

## 5. EOF and buffering

- A well-formed run ends with exactly one `terminal` or `error` event, then EOF.
- A process that exits without a terminal/error is a **protocol error**: the
  wrapper reports `=====ERROR=====` unless a local cancellation rule applies
  (section 6).
- Solution records are streamed: the implementation holds at most the current
  record plus the last acknowledgement; it never requires solving to completion
  before writing. A record write failure produces an `internal` error and no
  terminal success.
- A partial JSON line (EOF mid-record) never becomes a partial solution block.

## 6. Wrapper cancellation and exit policy (frozen)

1. The wrapper requests `--report=jsonl-v1`; it does not fall back to regex or
   stderr inference when a stale `LEANFZN_BIN` rejects the flag. That is a
   protocol error.
2. The wrapper may cancel `leanfzn` locally on `-t` (time limit), `-n`
   (solution limit) or a signal.
3. **First committed event wins.** A terminal event is committed when its
   complete line was received and its `kind`/`exit` table is consistent. If a
   valid completion was committed before wrapper cancellation, it is retained.
   If cancellation wins first, no later completion is printed and no proof
   claim is made: an approved incumbent set is followed by `=====UNKNOWN=====`
   only when no solution was printed; otherwise the run ends with its solutions
   and no terminal marker.
4. A terminal marker is buffered until the process exit status is known to be
   consistent with the event; it is released only then. This prevents a later
   protocol error from retracting an already printed marker.
5. Reaching a solution limit does not prove optimality and never prints
   `==========`.
6. An abnormal exit or crash is `=====ERROR=====` with a nonzero wrapper exit,
   even if valid witnesses preceded it. It does not use the local-cancellation
   exception.
7. Mapping of structured events to MiniZinc status:
   - `sat`/`optimal`/`unsat` → pass through the corresponding solution blocks
     and marker(s), wrapper exit 0.
   - `incomplete` → incumbents, then `=====UNKNOWN=====` only if none.
   - `unsupported`/`compile` → `=====UNSUPPORTED=====`, wrapper exit 0.
   - `usage`/`io`/`internal` → `=====ERROR=====`, nonzero wrapper exit.
   - `model_parse` → `=====UNSUPPORTED=====` (P0 default; documented assumption
     that MiniZinc produced valid FlatZinc). This preserves the float smoke case
     and is a non-answer.
   - unknown `event`, wrong type, missing metadata, duplicate ids, unknown
     output names, post-terminal solutions, conflicting terminals, missing
     terminal at unexpected EOF → `=====ERROR=====`, nonzero wrapper exit.

## 7. Scope of guarantees

The pure layer proved in `LeanFzn/Integration/Report/` covers:

- classification from the actual certified source result (`solveModel`,
  `optimizeCore`, `optimizeCoreSeed`, `optimizeCoreLns`) to a terminal kind;
- terminal kind ↔ exit code and terminal kind ↔ text marker;
- event → `Json` shape, terminal tag/exit binding, and name/text binding of
  solution entries to the actual emitter.

Trusted, not proved: Lean core's `Json` parser/printer and byte output, the
operating system and file descriptors, the Python wrapper, and the Lean/C/LLVM
compiler pipeline. The JSON printer's escaping, integer-as-string convention,
large integers and truncation are covered by codec tests. No theorem is claimed
about arbitrary observed OS bytes.

## 8. Version history

| Version | Date | Change |
| --- | --- | --- |
| 1 | 2026-11-14 | Initial frozen schema, event order, exit table and cancellation rule |

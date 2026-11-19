"""Mock-process matrix for the MiniZinc wrapper's frozen jsonl-v1 state machine.

Every test drives `minizinc-wrapper/fzn-leanfzn` as a real subprocess against a
generated mock solver.  The mock writes exactly the bytes in its spec, so the
tests exercise the wrapper's protocol boundary rather than FlatZinc parsing.
The matrix follows PLAN.md section 7 (B3.1-B3.7): Normal, Inconsistent,
Corrupt, Rendering, Streaming and Compatibility.

No MiniZinc binary and no Lean build are needed.  Mock processes use
deterministic writes; sleeps are used only to keep a process alive for a
timeout test or to separate chunks, never to decide a result.
"""

import base64
import json
import os
from pathlib import Path
import runpy
import signal
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / "minizinc-wrapper/fzn-leanfzn"

MODULE = runpy.run_path(str(WRAPPER))
ProtocolState = MODULE["ProtocolState"]
ProtocolError = MODULE["ProtocolError"]
State = MODULE["State"]
TERMINAL_EXITS = MODULE["TERMINAL_EXITS"]
ERROR_EXITS = MODULE["ERROR_EXITS"]

MODEL = "var 0..1: x :: output_var;\nsolve satisfy;\n"
_MISSING = object()

# ---------------------------------------------------------------------------
# Event builders (the frozen schema, not a second schema)

def hs(**overrides):
    event = {"event": "handshake", "protocol": "leanfzn-report", "version": 1}
    event.update(overrides)
    return event


def model(mode, outputs, objective=_MISSING):
    event = {"event": "model", "mode": mode, "outputs": list(outputs)}
    if objective is not _MISSING:
        event["objective"] = objective
    return event


def model_sat(outputs):
    return model("satisfy", outputs)


def model_opt(mode, objective, outputs):
    return model(mode, outputs, objective=objective)


def ent(name, text):
    return {"name": name, "text": text}


def sol(sid, entries, objective=_MISSING):
    event = {"event": "solution", "id": sid, "entries": entries}
    if objective is not _MISSING:
        event["objective"] = objective
    return event


def term(kind, exit=None, **extra):
    event = {"event": "terminal", "kind": kind,
             "exit": TERMINAL_EXITS[kind] if exit is None else exit}
    event.update(extra)
    return event


def err(kind, message="boom", exit=None):
    return {"event": "error", "kind": kind,
            "exit": ERROR_EXITS[kind] if exit is None else exit,
            "message": message}


def line(event):
    return json.dumps(event, separators=(",", ":")) + "\n"


def stream(*events):
    return "".join(line(event) for event in events)


# Canonical emitter text ends with a space after the final token.
X1 = "x = 1 ; "
X2 = "x = 2 ; "
Y2 = "y = 2 ; "
OBJ10 = "obj = 10 ; "
OBJ7 = "obj = 7 ; "

MOCK_TEMPLATE = '''#!/usr/bin/env python3
import base64
import json
import os
import signal
import sys
import time

SPEC = __SPEC__

argv_file = SPEC.get("argv_file")
if argv_file:
    with open(argv_file, "w", encoding="utf-8") as f:
        json.dump(sys.argv, f)

if SPEC.get("require_flag") and "--report=jsonl-v1" not in sys.argv:
    sys.stderr.write("mock: --report=jsonl-v1 not requested\\n")
    sys.stderr.flush()
    sys.exit(97)

for chunk in SPEC.get("chunks", []):
    sleep = 0.0
    if isinstance(chunk, dict):
        sleep = chunk.get("sleep", 0.0)
        if "b64" in chunk:
            data = base64.b64decode(chunk["b64"])
        else:
            data = chunk.get("text", "").encode("utf-8")
    else:
        data = chunk.encode("utf-8")
    sys.stdout.buffer.write(data)
    sys.stdout.buffer.flush()
    if sleep:
        time.sleep(sleep)

for text in SPEC.get("stderr", []):
    sys.stderr.write(text)
    sys.stderr.flush()

delay = SPEC.get("sleep", 0)
if delay:
    time.sleep(delay)

sig = SPEC.get("signal")
if sig:
    os.kill(os.getpid(), sig)

sys.exit(SPEC.get("exit", 0))
'''


class WrapperCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def run_wrapper(self, spec, *args, model_text=MODEL, env=None,
                    timeout=20, save_dir=None):
        spec = dict(spec)
        spec.setdefault("require_flag", True)
        if "signal" in spec:
            spec["signal"] = int(spec["signal"])
        spec["argv_file"] = str(self.tmp / "argv.json")
        solver = self.tmp / "solver.py"
        solver.write_text("#!/usr/bin/env python3\n" +
                          MOCK_TEMPLATE.replace("__SPEC__", repr(spec)))
        solver.chmod(0o755)
        fzn = self.tmp / "model.fzn"
        fzn.write_text(model_text)
        full_env = {**os.environ, "LEANFZN_BIN": str(solver),
                    "FZN_LEANFZN_SAVE_DIR": ""}
        if save_dir is not None:
            full_env["FZN_LEANFZN_SAVE_DIR"] = str(save_dir)
        if env:
            full_env.update(env)
        return subprocess.run(
            [str(WRAPPER), *args, str(fzn)],
            cwd=self.tmp, env=full_env, text=True, capture_output=True,
            timeout=timeout)

    def popen_wrapper(self, spec, *args, model_text=MODEL, env=None):
        """Start the wrapper around a mock solver for signal tests."""
        spec = dict(spec)
        spec.setdefault("require_flag", True)
        spec["argv_file"] = str(self.tmp / "argv.json")
        solver = self.tmp / "solver.py"
        solver.write_text("#!/usr/bin/env python3\n" +
                          MOCK_TEMPLATE.replace("__SPEC__", repr(spec)))
        solver.chmod(0o755)
        fzn = self.tmp / "model.fzn"
        fzn.write_text(model_text)
        full_env = {**os.environ, "LEANFZN_BIN": str(solver),
                    "FZN_LEANFZN_SAVE_DIR": ""}
        if env:
            full_env.update(env)
        return subprocess.Popen(
            [str(WRAPPER), *args, str(fzn)],
            cwd=self.tmp, env=full_env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def argv(self):
        return json.loads((self.tmp / "argv.json").read_text(encoding="utf-8"))

    def assert_ok(self, result, expected_stdout):
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, expected_stdout)

    def assert_error(self, result, stderr_contains=None):
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertTrue(result.stdout.endswith("=====ERROR=====\n"),
                        result.stdout)
        for marker in ("=====SATISFIABLE=====", "=====UNSATISFIABLE=====",
                       "=====UNKNOWN=====", "=====UNSUPPORTED=====",
                       "=========="):
            self.assertNotIn(marker, result.stdout)
        if stderr_contains is not None:
            self.assertIn(stderr_contains, result.stderr)

    def assert_error_after_solutions(self, result, expected_prefix):
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertTrue(result.stdout.startswith(expected_prefix), result.stdout)
        self.assertTrue(result.stdout.endswith("=====ERROR=====\n"), result.stdout)
        self.assertNotIn("=====UNKNOWN=====", result.stdout)
        self.assertNotIn("==========", result.stdout)
        self.assertNotIn("=====UNSATISFIABLE=====", result.stdout)


# ---------------------------------------------------------------------------
# Pure state-machine tests

class ProtocolStateTests(unittest.TestCase):
    def test_frozen_tables_and_flag(self):
        self.assertEqual(MODULE["REPORT_FLAG"], "--report=jsonl-v1")
        self.assertEqual(TERMINAL_EXITS, {
            "sat": 0, "optimal": 0, "unsat": 1,
            "incomplete": 4, "unsupported": 3,
        })
        self.assertEqual(ERROR_EXITS, {
            "usage": 2, "io": 2, "model_parse": 2,
            "unsupported": 3, "compile": 3, "internal": 2,
        })

    def test_full_path(self):
        machine = ProtocolState()
        self.assertIs(machine.state, State.START)
        machine.accept(hs())
        self.assertIs(machine.state, State.HANDSHAKEN)
        machine.accept(model_sat(["x"]))
        self.assertIs(machine.state, State.MODE)
        machine.accept(sol(1, [ent("x", X1)]))
        self.assertIs(machine.state, State.STREAMING)
        machine.accept(term("sat"))
        self.assertIs(machine.state, State.TERMINAL)
        self.assertIs(machine.finish(), State.TERMINAL)

    def test_cancel_before_terminal(self):
        machine = ProtocolState()
        machine.accept(hs())
        machine.accept(model_sat([]))
        machine.mark_cancelled()
        self.assertIs(machine.state, State.CANCELLED)
        self.assertIs(machine.finish(), State.CANCELLED)

    def test_cancel_after_terminal_retains_completion(self):
        machine = ProtocolState()
        machine.accept(hs())
        machine.accept(model_sat(["x"]))
        machine.accept(sol(1, [ent("x", X1)]))
        machine.accept(term("sat"))
        machine.mark_cancelled()
        self.assertIs(machine.state, State.TERMINAL)

    def test_finish_rejects_missing_handshake_and_terminal(self):
        with self.assertRaises(ProtocolError):
            ProtocolState().finish()
        machine = ProtocolState()
        machine.accept(hs())
        with self.assertRaises(ProtocolError):
            machine.finish()

    def test_invalid_transitions(self):
        cases = []

        def case(name, events, bad):
            cases.append((name, events, bad))

        case("model before handshake", [], model_sat([]))
        case("solution before model", [hs()], sol(1, [ent("x", X1)]))
        case("duplicate handshake", [hs()], hs())
        case("duplicate model", [hs(), model_sat([])], model_sat([]))
        case("terminal before model", [hs()], term("sat"))
        case("unknown event", [hs()], {"event": "bogus"})
        case("unknown version", [], hs(version=2))
        case("wrong protocol", [], hs(protocol="other"))
        case("non-object event", [], [])
        case("post-terminal", [hs(), model_sat([]), term("unsat")],
             term("incomplete"))
        case("second terminal", [hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
                                 term("sat")], term("sat"))
        case("sat without witness", [hs(), model_sat([])], term("sat"))
        case("sat on optimization",
             [hs(), model_opt("minimize", "obj", ["obj"]),
              sol(1, [ent("obj", "obj = 1 ; ")], objective="1")],
             term("sat"))
        case("optimal without witness",
             [hs(), model_opt("minimize", "obj", ["obj"])],
             term("optimal", solution=1))
        case("optimal wrong witness",
             [hs(), model_opt("minimize", "obj", ["obj"]),
              sol(1, [ent("obj", "obj = 1 ; ")], objective="1")],
             term("optimal", solution=2))
        case("unsat after witness",
             [hs(), model_sat(["x"]), sol(1, [ent("x", X1)])], term("unsat"))
        case("duplicate solution id",
             [hs(), model_opt("minimize", "obj", ["obj"]),
              sol(1, [ent("obj", "obj = 1 ; ")], objective="1")],
             sol(1, [ent("obj", "obj = 2 ; ")], objective="2"))
        case("missing output",
             [hs(), model_sat(["x", "z"])], sol(1, [ent("x", X1)]))
        case("wrong exit table", [hs(), model_sat([])], term("sat", exit=1))
        case("wrong id type", [hs(), model_sat(["x"])],
             sol("1", [ent("x", X1)]))
        case("entry newline", [hs(), model_sat(["x"])],
             sol(1, [ent("x", "x = 1 ; \n==========")]))
        for name, events, bad in cases:
            with self.subTest(name=name):
                machine = ProtocolState()
                for event in events:
                    machine.accept(event)
                with self.assertRaises(ProtocolError):
                    machine.accept(bad)


# ---------------------------------------------------------------------------
# Normal outcomes

class NormalFamily(WrapperCase):
    def test_normal_sat_filters_hidden_entries(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", X1), ent("y", Y2)]),
            term("sat"))]})
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertIn("--report=jsonl-v1", self.argv())

    def test_normal_unsat(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]), term("unsat"))], "exit": 1})
        self.assert_ok(result, "=====UNSATISFIABLE=====\n")

    def test_normal_completed_minimize(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x", "obj"]),
            sol(1, [ent("x", X1), ent("obj", OBJ10)], objective="10"),
            sol(2, [ent("x", X2), ent("obj", OBJ7)], objective="7"),
            term("optimal", solution=2))]})
        self.assert_ok(result,
                       f"{X1}\n{OBJ10}\n----------\n"
                       f"{X2}\n{OBJ7}\n----------\n==========\n")

    def test_normal_completed_maximize_with_null_objective(self):
        # objective:null is metadata only; hidden variables still carry the
        # canonical values and the outputs list filters everything out.
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("maximize", None, []),
            sol(1, [ent("h", "h = -5 ; ")], objective="-5"),
            sol(2, [ent("h", "h = -2 ; ")], objective="-2"),
            term("optimal", solution=2))]})
        self.assert_ok(result, "----------\n----------\n==========\n")

    def test_normal_incomplete_with_incumbent(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1), ent("obj", OBJ10)], objective="10"),
            term("incomplete", reason="conflict limit"))], "exit": 4})
        self.assert_ok(result, f"{X1}\n----------\n")

    def test_normal_incomplete_without_incumbent(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), term("incomplete", reason="limit"))],
            "exit": 4})
        self.assert_ok(result, "=====UNKNOWN=====\n")

    def test_normal_unsupported_terminal(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), term("unsupported", reason="floats"))],
            "exit": 3})
        self.assert_ok(result, "=====UNSUPPORTED=====\n")

    def test_inconsistent_unsupported_before_model(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), term("unsupported", reason="floats"))], "exit": 3})
        self.assert_error(result, "before model metadata")
        self.assertNotIn("=====UNSUPPORTED=====", result.stdout)

    def test_normal_empty_model_sat(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]), sol(1, []), term("sat"))]})
        self.assert_ok(result, "----------\n")

    def test_normal_typed_errors(self):
        for kind, process_exit in (("model_parse", 2), ("unsupported", 3),
                                   ("compile", 3)):
            with self.subTest(kind=kind):
                result = self.run_wrapper({"chunks": [stream(
                    hs(), err(kind))], "exit": process_exit})
                self.assert_ok(result, "=====UNSUPPORTED=====\n")
                self.assertIn("boom", result.stderr)
        for kind in ("usage", "io", "internal"):
            with self.subTest(kind=kind):
                result = self.run_wrapper({"chunks": [stream(
                    hs(), err(kind))], "exit": 2})
                self.assert_error(result)
                self.assertIn("boom", result.stderr)


# ---------------------------------------------------------------------------
# Inconsistent streams

class InconsistentFamily(WrapperCase):
    def test_inconsistent_exit_zero_without_result(self):
        result = self.run_wrapper({"chunks": [stream(hs(), model_sat([]))],
                                   "exit": 0})
        self.assert_error(result, "without a terminal event")

    def test_inconsistent_exit_one_without_result(self):
        result = self.run_wrapper({"chunks": [stream(hs(), model_sat([]))],
                                   "exit": 1})
        self.assert_error(result)
        self.assertNotIn("=====UNSATISFIABLE=====", result.stdout)

    def test_inconsistent_terminal_exit_table_mismatch(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("sat", exit=1))], "exit": 1})
        self.assert_error(result, "requires exit 0")

    def test_inconsistent_process_exit_mismatch(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]), term("unsat"))], "exit": 0})
        self.assert_error(result, "declares exit 1")
        self.assertNotIn("=====UNSATISFIABLE=====", result.stdout)

    def test_inconsistent_optimal_without_witness(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["obj"]),
            term("optimal", solution=1))]})
        self.assert_error(result, "without a referenced witness")

    def test_inconsistent_optimal_wrong_witness(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["obj"]),
            sol(1, [ent("obj", "obj = 1 ; ")], objective="1"),
            term("optimal", solution=2))]})
        self.assert_error(result, "references solution 2")

    def test_inconsistent_unsat_after_witness(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("unsat"))]})
        self.assert_error_after_solutions(result, f"{X1}\n----------\n")
        self.assertIn("after a witness", result.stderr)

    def test_inconsistent_duplicate_terminal(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("sat"), term("sat"))]})
        self.assert_error(result, "after terminal outcome")

    def test_inconsistent_conflicting_terminals(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), term("unsupported"), term("unsat"))]})
        self.assert_error(result)
        self.assertNotIn("=====UNSUPPORTED=====", result.stdout)
        self.assertNotIn("=====UNSATISFIABLE=====", result.stdout)

    def test_inconsistent_sat_without_witness(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]), term("sat"))]})
        self.assert_error(result, "exactly one solution")

    def test_inconsistent_sat_on_optimization(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["obj"]),
            sol(1, [ent("obj", "obj = 1 ; ")], objective="1"),
            term("sat"))]})
        self.assert_error(result, "optimization model")

    def test_unsupported_after_witness_keeps_incumbents_and_non_answer(self):
        # Compatibility: a portfolio worker can classify the model as
        # unsupported after another worker streamed a checked incumbent.  The
        # old text wrapper printed the incumbent followed by
        # `=====UNSUPPORTED=====`; keep that non-answer and add no proof claim.
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("unsupported"))], "exit": 3})
        self.assert_ok(result, f"{X1}\n----------\n=====UNSUPPORTED=====\n")

    def test_inconsistent_terminal_then_error(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("sat"), err("internal"))]})
        self.assert_error(result, "after terminal outcome")

    def test_inconsistent_error_exit_mismatch(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), err("usage"))], "exit": 0})
        self.assert_error(result, "declares exit 2")


# ---------------------------------------------------------------------------
# Corrupt streams

class CorruptFamily(WrapperCase):
    def test_corrupt_invalid_json(self):
        result = self.run_wrapper({"chunks": [
            stream(hs()), "this is not json\n"]})
        self.assert_error(result, "invalid JSON")

    def test_corrupt_truncated_json(self):
        result = self.run_wrapper({"chunks": [
            stream(hs(), model_sat([])), '{"event":"solution","id":1']},
            )
        self.assert_error(result, "truncated protocol record")

    def test_corrupt_missing_metadata(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), sol(1, [ent("x", X1)]), term("sat"))]})
        self.assert_error(result, "solution event in state HANDSHAKEN")

    def test_corrupt_unknown_version(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(version=2), model_sat([]))]})
        self.assert_error(result, "unsupported report protocol version")

    def test_corrupt_unknown_protocol(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(protocol="other"), model_sat([]))]})
        self.assert_error(result, "unsupported report protocol")

    def test_corrupt_unknown_event(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), {"event": "surprise"})]})
        self.assert_error(result, "unknown event")

    def test_corrupt_unknown_terminal_kind(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]),
            {"event": "terminal", "kind": "maybe", "exit": 0})]})
        self.assert_error(result, "unknown kind")

    def test_corrupt_unknown_error_kind(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), {"event": "error", "kind": "surprise", "exit": 2,
                   "message": "x"})]})
        self.assert_error(result, "unknown kind")

    def test_corrupt_wrong_types(self):
        base = stream(hs())
        cases = {
            "handshake version string": stream(hs(version="1")),
            "handshake version bool": stream(hs(version=True)),
            "handshake protocol number": stream(hs(protocol=1)),
            "model outputs string": stream(
                hs(), {"event": "model", "mode": "satisfy", "outputs": "x"}),
            "model mode number": stream(
                hs(), {"event": "model", "mode": 1, "outputs": []}),
            "model objective number": stream(
                hs(), model_opt("minimize", 5, [])),
            "solution id string": base + stream(
                model_sat(["x"]), sol("1", [ent("x", X1)])),
            "solution entries object": base + stream(
                model_sat(["x"]), sol(1, {"x": X1})),
            "entry name number": base + stream(
                model_sat(["x"]), sol(1, [{"name": 1, "text": X1}])),
            "entry text number": base + stream(
                model_sat(["x"]), sol(1, [{"name": "x", "text": 1}])),
            "terminal exit string": base + stream(
                model_sat([]), sol(1, []), term("sat", exit="0")),
            "terminal kind number": base + stream(
                model_sat([]), {"event": "terminal", "kind": 1, "exit": 0}),
            "optimal reference string": base + stream(
                model_opt("minimize", "obj", ["obj"]),
                sol(1, [ent("obj", "obj = 1 ; ")], objective="1"),
                term("optimal", solution="1")),
            "error message missing": base + stream(
                {"event": "error", "kind": "usage", "exit": 2}),
            "error exit float": base + stream(err("usage", exit=2.0)),
            "output name number": base + stream(
                {"event": "model", "mode": "satisfy", "outputs": [1]}),
            "objective not canonical": base + stream(
                model_opt("minimize", "obj", ["obj"]),
                sol(1, [ent("obj", "obj = 1 ; ")], objective="05")),
            "objective is a number": base + stream(
                model_opt("minimize", "obj", ["obj"]),
                sol(1, [ent("obj", "obj = 1 ; ")], objective=5)),
            "reason number": base + stream(
                model_sat([]), term("incomplete", reason=5)),
            "satisfy model has objective": base + stream(
                model("satisfy", [], objective=None)),
            "satisfaction solution has objective": base + stream(
                model_sat(["x"]), sol(1, [ent("x", X1)], objective="1")),
        }
        for name, chunks in cases.items():
            with self.subTest(name=name):
                result = self.run_wrapper({"chunks": [chunks]})
                self.assert_error(result)

    def test_corrupt_duplicate_solution_ids(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["obj"]),
            sol(1, [ent("obj", "obj = 1 ; ")], objective="1"),
            sol(1, [ent("obj", "obj = 2 ; ")], objective="2"),
            term("optimal", solution=1))]})
        self.assert_error(result, "does not follow")

    def test_corrupt_out_of_order_solution_ids(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["obj"]),
            sol(1, [ent("obj", "obj = 1 ; ")], objective="1"),
            sol(3, [ent("obj", "obj = 2 ; ")], objective="2"),
            term("optimal", solution=3))]})
        self.assert_error(result, "does not follow")

    def test_corrupt_missing_output_name(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x", "z"]), sol(1, [ent("x", X1)]),
            term("sat"))]})
        self.assert_error(result, "missing output entries: z")

    def test_corrupt_unknown_output_name(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["z"]),
            sol(1, [ent("x", X1), ent("y", Y2)]), term("sat"))]})
        self.assert_error(result, "missing output entries: z")

    def test_corrupt_duplicate_output_name(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x", "x"]))]})
        self.assert_error(result, "duplicate output name")

    def test_corrupt_duplicate_entry_name(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", X1), ent("x", X2)]))]})
        self.assert_error(result, "duplicate name")

    def test_corrupt_two_handshakes(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), hs(), model_sat([]))]})
        self.assert_error(result, "duplicate handshake")

    def test_corrupt_missing_handshake(self):
        result = self.run_wrapper({"chunks": [stream(
            model_sat([]), sol(1, []), term("sat"))]})
        self.assert_error(result, "expected handshake")

    def test_corrupt_post_terminal_solution(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
            term("sat"), sol(2, [ent("x", X2)]))]})
        self.assert_error(result, "after terminal outcome")

    def test_corrupt_empty_line(self):
        result = self.run_wrapper({"chunks": [
            stream(hs()), "\n", stream(model_sat([]))]})
        self.assert_error(result, "empty protocol line")

    def test_corrupt_invalid_utf8(self):
        bad = base64.b64encode(b"\xff\xfe\n").decode("ascii")
        result = self.run_wrapper({"chunks": [
            stream(hs()), {"b64": bad}]})
        self.assert_error(result, "not valid UTF-8")

    def test_corrupt_entry_newline_cannot_inject_marker(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", "x = 1 ; \n==========")]), term("sat"))]})
        self.assert_error(result, "line break")
        self.assertNotIn("==========", result.stdout)

    def test_corrupt_entry_text_rejects_nonprintable_separators(self):
        for label, text in (
                ("unicode line separator", "x = 1 ; \u2028=========="),
                ("unicode paragraph separator", "x = 1 ; \u2029=========="),
                ("DEL", "x = 1 ; \x7f=========="),
                ("C1 control", "x = 1 ; \x85==========")):
            with self.subTest(label=label):
                result = self.run_wrapper({"chunks": [stream(
                    hs(), model_sat(["x"]),
                    sol(1, [ent("x", text)]), term("sat"))]})
                self.assert_error(result, "control or separator")
                self.assertNotIn("==========", result.stdout)

    def test_corrupt_entry_text_must_name_its_variable(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", "y = 1 ; ")]), term("sat"))]})
        self.assert_error(result, "does not start with")

    def test_corrupt_entry_text_cannot_be_a_marker(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", "==========")]), term("sat"))]})
        self.assert_error(result, "does not start with")
        self.assertNotIn("==========", result.stdout)

    def test_corrupt_terminal_without_model(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), term("unsat"))], "exit": 1})
        self.assert_error(result, "before model metadata")

    def test_corrupt_non_object_line(self):
        result = self.run_wrapper({"chunks": [
            stream(hs()), "[]\n"]})
        self.assert_error(result, "not a JSON object")


# ---------------------------------------------------------------------------
# Rendering: wrapper must not parse FlatZinc values

class RenderingFamily(WrapperCase):
    def test_rendering_sets_before_arrays(self):
        set_text = "s = { 1 , 2 , 3 } ; "
        array_text = "a = array1d ( 1 .. 2 , [ 4 , 5 ] ) ; "
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["s", "a"]),
            sol(1, [ent("s", set_text), ent("a", array_text)]),
            term("sat"))]})
        self.assert_ok(result, f"{set_text}\n{array_text}\n----------\n")

    def test_rendering_empty_arrays(self):
        array_text = "a = array1d ( 1 .. 0 , [ ] ) ; "
        set_text = "b = { } ; "
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["a", "b"]),
            sol(1, [ent("a", array_text), ent("b", set_text)]),
            term("sat"))]})
        self.assert_ok(result, f"{array_text}\n{set_text}\n----------\n")

    def test_rendering_large_signed_integers(self):
        big = "big = -123456789012345678901234567890 ; "
        pos = "pos = 123456789012345678901234567890 ; "
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["big", "pos"]),
            sol(1, [ent("big", big), ent("pos", pos)]),
            term("sat"))]})
        self.assert_ok(result, f"{big}\n{pos}\n----------\n")

    def test_rendering_entry_text_cannot_select_an_output(self):
        # y is hidden.  Its text mentions x and output_var, but only the
        # structured names decide what is printed.
        y_text = "y = 7 ; % x = 999 ; output_var"
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", X1), ent("y", y_text)]),
            term("sat"))]})
        self.assert_ok(result, f"{X1}\n----------\n")

    def test_rendering_model_text_cannot_select_an_output(self):
        # The wrapper never scans the FlatZinc: only the model event's outputs
        # list selects entries, even when model comments and annotations mimic
        # output_var / solve declarations.
        model_text = '''% var 0..1: fake :: output_var;
% solve maximize fake;
var 0..1: x :: output_var;
var 0..1: y :: ann("output_var; solve maximize y;");
solve satisfy;
'''
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", X1), ent("y", Y2)]),
            term("sat"))]}, model_text=model_text)
        self.assert_ok(result, f"{X1}\n----------\n")


# ---------------------------------------------------------------------------
# Streaming and cancellation

class StreamingFamily(WrapperCase):
    def test_streaming_chunked_writes(self):
        text = stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1)], objective="10"),
            sol(2, [ent("x", X2)], objective="7"),
            term("optimal", solution=2))
        chunks = [
            {"text": text[:7], "sleep": 0.02},
            {"text": text[7:31], "sleep": 0.02},
            {"text": text[31:]}]
        result = self.run_wrapper({"chunks": chunks})
        self.assert_ok(result,
                       f"{X1}\n----------\n{X2}\n----------\n==========\n")

    def test_streaming_delayed_solutions(self):
        first = stream(hs(), model_sat(["x"]))
        result = self.run_wrapper({"chunks": [
            {"text": first, "sleep": 0.05},
            stream(sol(1, [ent("x", X1)]), term("sat"))]})
        self.assert_ok(result, f"{X1}\n----------\n")

    def test_streaming_eof_mid_record(self):
        result = self.run_wrapper({"chunks": [
            stream(hs(), model_sat(["x"])),
            '{"event":"solution","id":1,"entries":']})
        self.assert_error(result, "truncated protocol record")
        self.assertNotIn("----------", result.stdout)

    def test_streaming_timeout_before_completion(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]))], "sleep": 30}, "-t", "1000")
        self.assert_ok(result, "=====UNKNOWN=====\n")

    def test_streaming_timeout_with_incumbent(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]))],
            "sleep": 30}, "-t", "1000")
        self.assert_ok(result, f"{X1}\n----------\n")

    def test_streaming_timeout_after_completion_retains_terminal(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1)], objective="10"),
            term("optimal", solution=1))], "sleep": 30}, "-t", "1000")
        self.assert_ok(result, f"{X1}\n----------\n==========\n")

    def test_streaming_timeout_after_completion_saved_raw_has_marker(self):
        save = self.tmp / "saved-timeout-opt"
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1), ent("obj", OBJ10)], objective="10"),
            term("optimal", solution=1))], "sleep": 30}, "-t", "1000",
            save_dir=save)
        self.assert_ok(result,
                       f"{X1}\n----------\n==========\n")
        self.assertEqual((save / "raw.sol").read_text(),
                         f"{X1}\n{OBJ10}\n----------\n==========\n")

    def test_closed_stdout_is_controlled_error(self):
        proc = self.popen_wrapper({"chunks": [{
            "sleep": 0.5,
            "text": stream(hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
                           term("sat"))}]})
        proc.stdout.close()
        err = proc.stderr.read()
        proc.stderr.close()
        proc.wait(timeout=10)
        self.assertEqual(proc.returncode, 2, err)
        self.assertIn("cannot write wrapper output", err)
        self.assertNotIn("Traceback", err)

    def test_signal_after_committed_terminal_retains_it(self):
        proc = self.popen_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), term("unsat"))], "sleep": 30})
        try:
            time.sleep(1.0)
            proc.send_signal(signal.SIGTERM)
            out, err = proc.communicate(timeout=10)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.communicate()
        self.assertEqual(proc.returncode, 0, err)
        self.assertEqual(out, "=====UNSATISFIABLE=====\n")

    def test_signal_before_verdict_is_unknown(self):
        proc = self.popen_wrapper({"sleep": 30})
        try:
            time.sleep(1.0)
            proc.send_signal(signal.SIGTERM)
            out, err = proc.communicate(timeout=10)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.communicate()
        self.assertEqual(proc.returncode, 0, err)
        self.assertEqual(out, "=====UNKNOWN=====\n")

    def test_streaming_partial_record_then_timeout(self):
        # A killed partial record is discarded; it must not become a block.
        result = self.run_wrapper({"chunks": [
            stream(hs(), model_sat(["x"])),
            '{"event":"solution","id":1'], "sleep": 30}, "-t", "1000")
        self.assert_ok(result, "=====UNKNOWN=====\n")
        self.assertNotIn("----------", result.stdout)

    def test_streaming_solution_limit_race(self):
        text = stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1)], objective="10"),
            sol(2, [ent("x", X2)], objective="7"),
            term("optimal", solution=2))
        for limit, expected in (
                ("1", f"{X1}\n----------\n"),
                ("2", f"{X1}\n----------\n{X2}\n----------\n")):
            with self.subTest(limit=limit):
                result = self.run_wrapper({"chunks": [text], "sleep": 30},
                                          "-n", limit)
                self.assert_ok(result, expected)
                self.assertNotIn("==========", result.stdout)

    def test_streaming_crash_after_partial_progress(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]))],
            "signal": signal.SIGKILL})
        self.assert_error_after_solutions(result, f"{X1}\n----------\n")

    def test_streaming_crash_before_any_solution(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]))], "signal": signal.SIGKILL})
        self.assert_error(result)

    def test_streaming_terminal_then_crash_is_error(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1)], objective="10"),
            term("optimal", solution=1))], "signal": signal.SIGKILL})
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertTrue(result.stdout.endswith("=====ERROR=====\n"),
                        result.stdout)
        self.assertNotIn("==========", result.stdout)


# ---------------------------------------------------------------------------
# Compatibility: flags, stats, saved artefacts, stderr independence

class CompatibilityFamily(WrapperCase):
    def test_compatibility_parallel_portfolio(self):
        sat = {"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))]}
        result = self.run_wrapper(sat, "-p", "4")
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertIn("--threads=4", self.argv())
        self.assertNotIn("-p is ignored", result.stderr)

        result = self.run_wrapper(sat, "-p", "20")
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertIn("--threads=8", self.argv())

    def test_compatibility_parallel_strategy_conflict_note(self):
        sat = {"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))]}
        for extra in (["--var", "wdeg"], ["--strategy=annot"],
                      ["--opt=seeded"]):
            with self.subTest(extra=extra):
                result = self.run_wrapper(sat, "-p", "4", *extra)
                self.assert_ok(result, f"{X1}\n----------\n")
                self.assertIn("-p is ignored", result.stderr)
                self.assertNotIn("--threads=4", self.argv())

    def test_compatibility_time_and_solution_limits_stay_local(self):
        sat = {"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))]}
        result = self.run_wrapper(sat, "-t", "5000", "-n", "2")
        self.assert_ok(result, f"{X1}\n----------\n")
        argv = self.argv()
        self.assertNotIn("-t", argv)
        self.assertNotIn("--time-limit", argv)
        self.assertNotIn("-n", argv)
        self.assertNotIn("--num-solutions", argv)

    def test_compatibility_all_solutions_note_preserved(self):
        sat = {"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))]}
        result = self.run_wrapper(sat, "-a")
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertIn("-a: leanfzn reports one solution per satisfaction model",
                      result.stderr)

        opt = {"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1)], objective="10"),
            term("optimal", solution=1))]}
        result = self.run_wrapper(opt, "-a")
        self.assert_ok(result, f"{X1}\n----------\n==========\n")
        self.assertNotIn("-a: leanfzn reports", result.stderr)

    def test_compatibility_ignored_standard_flags(self):
        sat = {"chunks": [stream(
            hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))]}
        result = self.run_wrapper(sat, "-i", "-f", "-r", "7")
        self.assert_ok(result, f"{X1}\n----------\n")
        argv = self.argv()
        for ignored in ("-i", "--intermediate", "-f", "--free-search",
                        "-r", "--seed", "--random-seed"):
            self.assertNotIn(ignored, argv)

    def test_compatibility_statistics_translation(self):
        spec = {
            "chunks": [stream(
                hs(), model_sat(["x"]), sol(1, [ent("x", X1)]), term("sat"))],
            "stderr": [
                "leanfzn: stats: decisions=12 conflicts=3 propagations=40 "
                "steps=99 x=-\n",
                "leanfzn: timing: search_ms=5\n",
            ],
        }
        result = self.run_wrapper(spec, "-s")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith(f"{X1}\n----------\n"))
        self.assertRegex(result.stdout, r"%%%mzn-stat: solveTime=\d+\.\d+\n")
        self.assertIn("%%%mzn-stat: nodes=12\n", result.stdout)
        self.assertIn("%%%mzn-stat: failures=3\n", result.stdout)
        self.assertIn("%%%mzn-stat: propagations=40\n", result.stdout)
        self.assertIn("%%%mzn-stat: search_ms=5\n", result.stdout)
        self.assertNotIn("steps=99", result.stdout)
        self.assertNotIn("x=-\n", result.stdout)
        self.assertTrue(result.stdout.endswith("%%%mzn-stat-end\n"))
        self.assertNotIn("leanfzn: stats:", result.stderr)
        self.assertNotIn("leanfzn: timing:", result.stderr)

        plain = self.run_wrapper(spec)
        self.assert_ok(plain, f"{X1}\n----------\n")
        self.assertNotIn("%%%mzn-stat:", plain.stdout)
        self.assertNotIn("leanfzn: stats:", plain.stderr)
        # Without -s the timing line is ordinary diagnostic text.
        self.assertIn("leanfzn: timing:", plain.stderr)

    def test_compatibility_verbose_command_line(self):
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat([]), term("unsat"))], "exit": 1}, "-v")
        self.assert_ok(result, "=====UNSATISFIABLE=====\n")
        self.assertIn("running ", result.stderr)
        self.assertIn("--report=jsonl-v1", result.stderr)
        self.assertIn(str(self.tmp / "model.fzn"), result.stderr)

    def test_compatibility_extra_options_forwarded(self):
        result = self.run_wrapper(
            {"chunks": [stream(hs(), model_sat([]), term("unsat"))],
             "exit": 1},
            "--var", "wdeg", "--restart=luby", "--heur-obj-prio",
            "--primal-time", "5", "--presolve=dedup")
        self.assert_ok(result, "=====UNSATISFIABLE=====\n")
        argv = self.argv()
        for expected in ("--var=wdeg", "--restart=luby", "--heur-obj-prio",
                         "--primal-time=5", "--presolve=dedup"):
            self.assertIn(expected, argv)

    def test_compatibility_save_dir_sat_and_model(self):
        save = self.tmp / "saved-sat"
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_sat(["x"]),
            sol(1, [ent("x", X1), ent("y", Y2)]), term("sat"))]},
            save_dir=save)
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertEqual((save / "model.fzn").read_text(), MODEL)
        self.assertEqual((save / "raw.sol").read_text(),
                         f"{X1}\n{Y2}\n----------\n")

    def test_compatibility_save_dir_optimal(self):
        save = self.tmp / "saved-opt"
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1), ent("obj", OBJ10)], objective="10"),
            sol(2, [ent("x", X2), ent("obj", OBJ7)], objective="7"),
            term("optimal", solution=2))]}, save_dir=save)
        self.assert_ok(result,
                       f"{X1}\n----------\n{X2}\n----------\n==========\n")
        self.assertEqual((save / "raw.sol").read_text(),
                         f"{X1}\n{OBJ10}\n----------\n"
                         f"{X2}\n{OBJ7}\n----------\n==========\n")

    def test_compatibility_save_dir_incomplete_has_no_optimal_marker(self):
        save = self.tmp / "saved-incomplete"
        result = self.run_wrapper({"chunks": [stream(
            hs(), model_opt("minimize", "obj", ["x"]),
            sol(1, [ent("x", X1), ent("obj", OBJ10)], objective="10"),
            term("incomplete"))], "exit": 4}, save_dir=save)
        self.assert_ok(result, f"{X1}\n----------\n")
        self.assertEqual((save / "raw.sol").read_text(),
                         f"{X1}\n{OBJ10}\n----------\n")

    def test_compatibility_stderr_text_has_no_effect(self):
        sat = stream(hs(), model_sat(["x"]), sol(1, [ent("x", X1)]),
                     term("sat"))
        quiet = self.run_wrapper({"chunks": [sat],
                                  "stderr": ["diagnostic one\n"]})
        noisy = self.run_wrapper({"chunks": [sat], "stderr": [
            "leanfzn: parse error: pretend\n",
            "=====UNSATISFIABLE=====\n",
            "==========\n",
            "x = 999 ; \n",
        ]})
        self.assert_ok(quiet, f"{X1}\n----------\n")
        self.assert_ok(noisy, f"{X1}\n----------\n")
        self.assertNotEqual(quiet.stderr, noisy.stderr)
        self.assertIn("diagnostic one", quiet.stderr)
        self.assertIn("parse error: pretend", noisy.stderr)

    def test_compatibility_stale_text_output_is_an_error(self):
        result = self.run_wrapper({"chunks": [
            "x = 1 ; \n----------\n"], "exit": 0})
        self.assert_error(result)
        self.assertNotIn("----------", result.stdout)

    def test_compatibility_binary_rejecting_report_flag_is_an_error(self):
        result = self.run_wrapper({
            "chunks": [],
            "stderr": ["unknown option --report=jsonl-v1\n"],
            "exit": 2,
        })
        self.assert_error(result)

    def test_compatibility_missing_binary_is_an_error(self):
        result = self.run_wrapper(
            {"chunks": []},
            env={"LEANFZN_BIN": str(self.tmp / "does-not-exist")})
        self.assert_error(result, "binary not found")

    def test_compatibility_unknown_option_is_an_error(self):
        result = self.run_wrapper({"chunks": []}, "--not-a-real-option")
        self.assert_error(result, "unsupported option")


if __name__ == "__main__":
    unittest.main()

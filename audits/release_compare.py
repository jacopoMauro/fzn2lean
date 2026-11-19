#!/usr/bin/env python3
"""Fail-closed PGO / non-PGO release comparison for LeanFzn (PLAN C1-C3).

``audits/run_release_gates.sh`` creates the frozen source snapshot, builds the
two variants serially in separate build trees, and then invokes this script
with the prebuilt binaries and the two snapshot directories.  This script can
also be called directly with prebuilt binaries, which is how the negative
tests exercise it.

It writes:

* ``manifest.json``: source path+sha256, package flags, git head/status,
  compiler/linker/LLVM/target versions, MiniZinc pin, PGO profile checksum,
  cohort hashes, both binary hashes and the exact one-line non-PGO diff.
* ``comparison.json``: the hardened ``fixed_k.py`` report joined with the
  manifest compatibility decision and explicit oracle-check counts.
* ``summary.txt``: one terminal line per case and ``RELEASE GATE: PASS`` only
  when every check actually ran and passed.

The exit status is 0 only on a complete pass, 1 when a required comparison or
case failed (including a fixed-k timeout or a missing fixed-k report), and 2
on setup/cohort/manifest incompatibility.  A skipped mandatory check is never
a pass; there is no option to disable witness checking, and a missing or
malformed stats line is a case failure inside ``fixed_k.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fixed_k  # noqa: E402  (same-directory audit tool, no package install)

SCHEMA_VERSION = 1
DEFAULT_LIMIT = 10
DEFAULT_CAP = 60
DEFAULT_FIXED_K_TIMEOUT = 3600
DEFAULT_MEASURE_LOCK = "/tmp/fzn2lean-measure.lock"
EXCLUDE_DIRS = {".lake", ".git", "tmp", "__pycache__", ".ruff_cache"}
EXCLUDE_SUFFIXES = {".pyc", ".profraw", ".log", ".trace", ".rsp", ".hash"}


class ReleaseError(Exception):
    """A setup or compatibility error (exit 2)."""


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--pgo-binary", required=True,
                   help="prebuilt PGO leanfzn binary")
    p.add_argument("--nopgo-binary", required=True,
                   help="prebuilt non-PGO leanfzn binary")
    p.add_argument("--snapshot-pgo", required=True,
                   help="frozen source tree used for the PGO build")
    p.add_argument("--snapshot-nopgo", required=True,
                   help="frozen source tree used for the non-PGO build")
    p.add_argument("--cohort", required=True,
                   help="committed release cohort TSV")
    p.add_argument("--limit", type=int, default=None,
                   help="conflict limit (default: frozen # conflict_limit "
                        "comment in the cohort)")
    p.add_argument("--allow-limit-override", action="store_true",
                   help="permit a limit different from the frozen cohort")
    p.add_argument("--cap", type=int, default=DEFAULT_CAP,
                   help=f"external wall cap per run (default {DEFAULT_CAP}s)")
    p.add_argument("--out", required=True,
                   help="output directory for manifest/comparison/logs")
    p.add_argument("--manifest", default=None,
                   help="manifest path (default OUT/manifest.json)")
    p.add_argument("--comparison", default=None,
                   help="comparison path (default OUT/comparison.json)")
    p.add_argument("--expected-manifest", default=None,
                   help="optional frozen manifest to compare provenance against")
    p.add_argument("--fixed-k", default=str(ROOT / "audits/fixed_k.py"),
                   help="fixed_k.py path")
    p.add_argument("--git-root", default=str(ROOT),
                   help="repository root for git provenance (default: this "
                        "script's repository); set explicitly when running a "
                        "snapshot copy of the comparator")
    p.add_argument("--require-snapshot-harness", action="store_true",
                   help="require this comparator, the imported fixed_k module "
                        "and --fixed-k to be byte-identical to the frozen "
                        "snapshot copies under audits/")
    p.add_argument("--measure-lock", default=DEFAULT_MEASURE_LOCK,
                   help="fixed_k measurement lock path")
    p.add_argument("--fixed-k-timeout", type=int,
                   default=DEFAULT_FIXED_K_TIMEOUT,
                   help="total seconds allowed for fixed_k.py")
    p.add_argument("--taskset", action="store_true",
                   help="let fixed_k pin to --limit's default core (rarely "
                        "needed; counters are deterministic without it)")
    p.add_argument("--require-oracle", action="store_true",
                   help="require minizinc and fzn-gecode on PATH and record "
                        "their version/hash provenance in the manifest; a "
                        "missing or unrunnable oracle is a setup error (exit 2)")
    p.add_argument("--quiet", action="store_true")
    args = p.parse_args()
    if args.limit is not None and args.limit < 1:
        p.error("--limit must be >= 1")
    if args.cap < 1:
        p.error("--cap must be >= 1")
    if args.fixed_k_timeout < 1:
        p.error("--fixed-k-timeout must be >= 1")
    return args


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def frozen_limit(cohort_text: str) -> int | None:
    m = re.search(r"(?m)^\s*#\s*conflict_limit:\s*(\d+)\s*$", cohort_text)
    return int(m.group(1)) if m else None


def hash_tree(root: Path) -> dict[str, dict[str, object]]:
    """Hash every source file in a snapshot, excluding build/scratch trees."""
    files: dict[str, dict[str, object]] = {}
    root = root.resolve()
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        for name in sorted(filenames):
            p = Path(dirpath) / name
            if p.suffix in EXCLUDE_SUFFIXES:
                continue
            if p.is_symlink():
                target = p.resolve()
                try:
                    target.relative_to(root)
                except ValueError as exc:
                    raise ReleaseError(
                        f"source snapshot contains an escaping symlink: {p} -> "
                        f"{target}") from exc
            if not p.is_file():
                continue
            rel = p.relative_to(root).as_posix()
            files[rel] = {
                "sha256": sha256_file(p),
                "size": p.stat().st_size,
            }
    if not files:
        raise ReleaseError(f"source snapshot is empty: {root}")
    return files


def read_lakefile(snapshot: Path) -> tuple[str, list[int], list[str]]:
    path = snapshot / "lakefile.toml"
    if not path.is_file():
        raise ReleaseError(f"missing lakefile.toml in {snapshot}")
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    idx = [i for i, line in enumerate(lines)
           if re.match(r"^\s*moreLeancArgs\s*=", line)]
    if len(idx) > 1:
        raise ReleaseError(f"{path}: multiple moreLeancArgs lines")
    flags: list[str] = []
    if idx:
        m = re.search(r"\[(.*?)\]", lines[idx[0]])
        if not m:
            raise ReleaseError(f"{path}: malformed moreLeancArgs array")
        flags = re.findall(r'"([^"]*)"', m.group(1))
    return text, idx, flags


def one_line_diff(pgo_snapshot: Path, nopgo_snapshot: Path) -> str:
    """Return the removed line, or raise if the two lakefiles differ otherwise."""
    pgo_text, pgo_idx, pgo_flags = read_lakefile(pgo_snapshot)
    nopgo_text, nopgo_idx, nopgo_flags = read_lakefile(nopgo_snapshot)
    if len(pgo_idx) != 1:
        raise ReleaseError(
            "PGO lakefile.toml must contain exactly one package moreLeancArgs "
            "line")
    if nopgo_idx:
        raise ReleaseError(
            "non-PGO lakefile.toml still contains a package moreLeancArgs line")
    pgo_lines = pgo_text.splitlines(keepends=True)
    i = pgo_idx[0]
    expected = "".join(pgo_lines[:i] + pgo_lines[i + 1:])
    if nopgo_text != expected:
        raise ReleaseError(
            "incompatible manifests: non-PGO lakefile.toml is not the PGO "
            "lakefile with exactly one package moreLeancArgs line removed")
    if not any("fprofile-use" in f for f in pgo_flags):
        raise ReleaseError(
            "PGO lakefile.toml moreLeancArgs does not select -fprofile-use")
    if any("fprofile-use" in f for f in nopgo_flags):
        raise ReleaseError("non-PGO selection still requests -fprofile-use")
    return pgo_lines[i].rstrip("\n")


def run_probe(cwd: Path, argv: list[str], timeout: int = 60,
              optional: bool = False) -> dict:
    try:
        p = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, text=True,
                           encoding="utf-8", errors="replace", timeout=timeout)
        status = "ok" if p.returncode == 0 else "failed"
        return {
            "argv": argv, "status": status, "returncode": p.returncode,
            "stdout": (p.stdout or "")[:4000],
            "stderr": (p.stderr or "")[:4000],
        }
    except FileNotFoundError:
        if optional:
            return {"argv": argv, "status": "unavailable", "returncode": None,
                    "stdout": "", "stderr": ""}
        raise ReleaseError(f"missing required command: {argv[0]}")
    except subprocess.TimeoutExpired:
        return {"argv": argv, "status": "timeout", "returncode": None,
                "stdout": "", "stderr": f"probe timed out after {timeout}s"}
    except OSError as exc:
        if optional:
            return {"argv": argv, "status": "unavailable", "returncode": None,
                    "stdout": "", "stderr": str(exc)}
        raise ReleaseError(f"cannot run {argv[0]}: {exc}") from exc


def first_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()
    return ""


def probe_toolchain(snapshot: Path) -> dict:
    probes = {
        "lake_version": run_probe(snapshot, ["lake", "--version"]),
        "lean_version": run_probe(snapshot, ["lake", "env", "lean", "--version"]),
        "llvm_version": run_probe(snapshot, ["lake", "env", "clang", "--version"]),
        "linker_version": run_probe(snapshot, ["ld", "--version"]),
        "target_machine": run_probe(snapshot, ["uname", "-m"]),
        "llvm_profdata": run_probe(
            snapshot, ["llvm-profdata", "--version"], optional=True),
    }
    for key in ("lake_version", "lean_version", "llvm_version",
                "linker_version", "target_machine"):
        if probes[key]["status"] != "ok":
            raise ReleaseError(
                f"toolchain probe {key} failed in {snapshot}: "
                f"{probes[key]['status']} {probes[key]['stderr'][:300]}")
    lean_out = probes["lean_version"]["stdout"] + probes["lean_version"]["stderr"]
    llvm_out = probes["llvm_version"]["stdout"] + probes["llvm_version"]["stderr"]
    lean_m = re.search(r"Lean \(version ([^,]+), ([^,]+)", lean_out)
    if not lean_m:
        raise ReleaseError(f"cannot parse Lean version from: {lean_out[:300]}")
    llvm_m = re.search(r"clang version ([0-9][^\s]*)", llvm_out)
    if not llvm_m:
        raise ReleaseError(f"cannot parse LLVM version from: {llvm_out[:300]}")
    target_m = re.search(r"(?m)^Target:\s*(\S+)", llvm_out)
    parsed = {
        "lean_version": lean_m.group(1),
        "lean_target": lean_m.group(2),
        "llvm_version": llvm_m.group(1),
        "llvm_target": target_m.group(1) if target_m else None,
        "linker": first_line(probes["linker_version"]["stdout"] +
                             probes["linker_version"]["stderr"]),
        "machine": first_line(probes["target_machine"]["stdout"] +
                              probes["target_machine"]["stderr"]),
        "llvm_profdata": first_line(probes["llvm_profdata"]["stdout"] +
                                    probes["llvm_profdata"]["stderr"])
        if probes["llvm_profdata"]["status"] == "ok" else "unavailable",
    }
    probes["parsed"] = parsed
    return probes


def toolchain_key(toolchain: dict) -> dict:
    return {
        "lean_version": toolchain["parsed"]["lean_version"],
        "lean_target": toolchain["parsed"]["lean_target"],
        "llvm_version": toolchain["parsed"]["llvm_version"],
        "llvm_target": toolchain["parsed"]["llvm_target"],
        "linker": toolchain["parsed"]["linker"],
        "machine": toolchain["parsed"]["machine"],
    }


def minizinc_pin(snapshot: Path) -> dict:
    dockerfile = snapshot / "minizinc-wrapper/Dockerfile"
    if not dockerfile.is_file():
        raise ReleaseError(
            f"missing MiniZinc pin {dockerfile}; the release manifest needs "
            f"the packaged solver version and checksum")
    text = dockerfile.read_text(encoding="utf-8")
    ver = re.search(r"(?m)^ARG\s+MZN_VERSION=(\S+)", text)
    sha = re.search(r"(?m)^ARG\s+MZN_SHA256=(\S+)", text)
    if not ver or not sha:
        raise ReleaseError(
            f"{dockerfile}: MZN_VERSION/MZN_SHA256 ARG pins not found")
    return {
        "source": "minizinc-wrapper/Dockerfile",
        "version": ver.group(1),
        "sha256": sha.group(1),
        "dockerfile_sha256": sha256_file(dockerfile),
    }


def git_provenance(root: Path) -> dict:
    def run(*argv: str) -> dict:
        p = subprocess.run(list(argv), cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, text=True,
                           encoding="utf-8", errors="replace", timeout=120)
        if p.returncode != 0:
            raise ReleaseError(
                f"git provenance command failed: {' '.join(argv)}: "
                f"{(p.stderr or '').strip()[:300]}")
        return {"stdout": p.stdout, "stderr": p.stderr, "returncode": p.returncode}

    head = run("git", "rev-parse", "HEAD")["stdout"].strip()
    status = run("git", "status", "--porcelain=v1", "--untracked-files=normal")
    status_text = status["stdout"]
    return {
        "head": head,
        "worktree_status": status_text.splitlines(),
        "worktree_status_sha256": hashlib.sha256(status_text.encode()).hexdigest(),
        "status_command": "git status --porcelain=v1 --untracked-files=normal",
    }


def oracle_provenance(required: bool) -> dict:
    """Version and hash of the independent oracles on PATH.

    A missing or unrunnable oracle is a setup error when ``required`` (the
    release gate always requires it): a skipped oracle is not evidence.
    """
    found = {name: shutil.which(name) for name in ("minizinc", "fzn-gecode")}
    missing = sorted(name for name, path in found.items() if path is None)
    if missing:
        if required:
            raise ReleaseError(
                "required oracles not found on PATH: " + ", ".join(missing)
                + " (install with audits/install_oracles.sh)")
        return {"required": False, "present": False, "missing": missing}
    info: dict = {"required": required, "present": True}
    try:
        probes = {}
        for name, flag in (("minizinc", "--version"),
                           ("fzn-gecode", "-help")):
            # fzn-gecode has no --version flag: it parses that as a file name
            # and exits 1, so the version banner of -help is the record.
            p = subprocess.run([found[name], flag], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=60)
            probes[name] = ((p.stdout or b"").decode("utf-8", "replace")
                            + (p.stderr or b"").decode("utf-8", "replace"))
    except (OSError, subprocess.SubprocessError) as exc:
        if required:
            raise ReleaseError(f"cannot run oracle: {exc}") from exc
        return {"required": False, "present": False, "error": str(exc)}
    mv = re.search(r"version (\S+?),", probes["minizinc"])
    gv = re.search(r"(?m)^ - Version: (\S+)$", probes["fzn-gecode"])
    info.update({
        "minizinc": {
            "path": found["minizinc"],
            "sha256": sha256_file(Path(found["minizinc"])),
            "version": mv.group(1) if mv else None,
        },
        "fzn_gecode": {
            "path": found["fzn-gecode"],
            "sha256": sha256_file(Path(found["fzn-gecode"])),
            "version": gv.group(1) if gv else None,
        },
    })
    if required and (info["minizinc"]["version"] is None
                     or info["fzn_gecode"]["version"] is None):
        raise ReleaseError(
            "oracle version probe failed; refusing to report oracle evidence")
    return info


def binary_info(path: str) -> dict:
    p = Path(path)
    if not p.is_file():
        raise ReleaseError(f"binary not found: {path}")
    if not os.access(path, os.X_OK):
        raise ReleaseError(f"binary is not executable: {path}")
    return {
        "path": str(p.resolve()),
        "sha256": sha256_file(p),
        "size": p.stat().st_size,
    }


def variant_manifest(snapshot: Path, binary: dict, variant: str) -> dict:
    text, idx, flags = read_lakefile(snapshot)
    source = hash_tree(snapshot)
    for required in ("lean-toolchain", "lake-manifest.json",
                     "pgo/default.profdata"):
        if required not in source:
            raise ReleaseError(
                f"{snapshot}: missing required frozen file {required}")
    toolchain = probe_toolchain(snapshot)
    pin = minizinc_pin(snapshot)
    return {
        "variant": variant,
        "source_root": str(snapshot.resolve()),
        "source_sha256": source,
        "lakefile_sha256": source["lakefile.toml"]["sha256"],
        "lakefile_moreLeancArgs": flags,
        "lean_toolchain_sha256": source["lean-toolchain"]["sha256"],
        "lake_manifest_sha256": source["lake-manifest.json"]["sha256"],
        "pgo_profile_sha256": source["pgo/default.profdata"]["sha256"],
        "toolchain": toolchain,
        "minizinc": pin,
        "binary": binary,
    }


def compare_variants(pgo: dict, nopgo: dict) -> dict:
    """Fail closed unless the only source difference is the PGO selection."""
    pgo_src = pgo["source_sha256"]
    nopgo_src = nopgo["source_sha256"]
    if set(pgo_src) != set(nopgo_src):
        only_p = sorted(set(pgo_src) - set(nopgo_src))
        only_n = sorted(set(nopgo_src) - set(pgo_src))
        raise ReleaseError(
            "incompatible manifests: source file sets differ; "
            f"only in PGO={only_p[:10]}, only in non-PGO={only_n[:10]}")
    differing = [path for path in sorted(pgo_src)
                 if path != "lakefile.toml" and
                 pgo_src[path]["sha256"] != nopgo_src[path]["sha256"]]
    if differing:
        raise ReleaseError(
            "incompatible manifests: source differs outside lakefile.toml: "
            + ", ".join(differing[:10]))
    removed = one_line_diff(Path(pgo["source_root"]),
                            Path(nopgo["source_root"]))
    if pgo["lean_toolchain_sha256"] != nopgo["lean_toolchain_sha256"]:
        raise ReleaseError("incompatible manifests: lean-toolchain differs")
    if pgo["lake_manifest_sha256"] != nopgo["lake_manifest_sha256"]:
        raise ReleaseError("incompatible manifests: lake-manifest.json differs")
    if pgo["pgo_profile_sha256"] != nopgo["pgo_profile_sha256"]:
        raise ReleaseError("incompatible manifests: PGO profile differs")
    if toolchain_key(pgo["toolchain"]) != toolchain_key(nopgo["toolchain"]):
        raise ReleaseError(
            "incompatible manifests: compiler/linker/target versions differ")
    if pgo["minizinc"] != nopgo["minizinc"]:
        raise ReleaseError("incompatible manifests: MiniZinc pin differs")
    if pgo["binary"]["sha256"] == nopgo["binary"]["sha256"]:
        raise ReleaseError(
            "PGO selection is ineffective: both variants produced the same "
            "binary hash")
    if not pgo["lakefile_moreLeancArgs"]:
        raise ReleaseError("PGO variant has no package moreLeancArgs flags")
    return {
        "ok": True,
        "lakefile_one_line_diff": removed,
        "non_pgo_removed_line": removed,
        "source_files_equal_except_lakefile": True,
        "toolchain_equal": True,
        "minizinc_equal": True,
        "pgo_profile_equal": True,
        "binaries_differ": True,
    }


def verify_expected_manifest(expected_path: str, manifest: dict) -> None:
    p = Path(expected_path)
    if not p.is_file():
        raise ReleaseError(f"expected manifest not found: {expected_path}")
    try:
        expected = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReleaseError(f"cannot parse expected manifest {p}: {exc}") from exc
    if not isinstance(expected, dict):
        raise ReleaseError(f"expected manifest {p} is not a JSON object")

    def expected_get(*keys: str):
        value = expected
        for key in keys:
            if not isinstance(value, dict):
                return None
            value = value.get(key)
        return value

    checks = [
        ("cohort.sha256", manifest["cohort"]["sha256"],
         expected_get("cohort", "sha256")),
        ("cohort.limit", manifest["cohort"]["limit"],
         expected_get("cohort", "limit")),
        ("variants.pgo.lakefile_sha256", manifest["variants"]["pgo"]["lakefile_sha256"],
         expected_get("variants", "pgo", "lakefile_sha256")),
        ("variants.nopgo.lakefile_sha256",
         manifest["variants"]["nopgo"]["lakefile_sha256"],
         expected_get("variants", "nopgo", "lakefile_sha256")),
        ("variants.pgo.pgo_profile_sha256",
         manifest["variants"]["pgo"]["pgo_profile_sha256"],
         expected_get("variants", "pgo", "pgo_profile_sha256")),
        ("variants.pgo.lean_toolchain_sha256",
         manifest["variants"]["pgo"]["lean_toolchain_sha256"],
         expected_get("variants", "pgo", "lean_toolchain_sha256")),
        ("variants.pgo.source_sha256", manifest["variants"]["pgo"]["source_sha256"],
         expected_get("variants", "pgo", "source_sha256")),
        ("variants.nopgo.source_sha256",
         manifest["variants"]["nopgo"]["source_sha256"],
         expected_get("variants", "nopgo", "source_sha256")),
        ("variants.pgo.minizinc", manifest["variants"]["pgo"]["minizinc"],
         expected_get("variants", "pgo", "minizinc")),
        ("tooling.fixed_k.sha256", manifest["tooling"]["fixed_k"]["sha256"],
         expected_get("tooling", "fixed_k", "sha256")),
        ("tooling.release_compare.sha256",
         manifest["tooling"]["release_compare"]["sha256"],
         expected_get("tooling", "release_compare", "sha256")),
    ]
    expected_toolchain = expected_get("variants", "pgo", "toolchain")
    if isinstance(expected_toolchain, dict) and expected_toolchain:
        checks.append((
            "variants.pgo.toolchain",
            toolchain_key(manifest["variants"]["pgo"]["toolchain"]),
            toolchain_key(expected_toolchain)))
    present = [check for check in checks if check[2] is not None]
    if not present:
        raise ReleaseError(
            f"expected manifest {p} contains no recognized provenance pins")
    mismatches = []
    for name, got, want in present:
        if got != want:
            mismatches.append(name)
    if mismatches:
        raise ReleaseError(
            "incompatible manifests: expected provenance differs for "
            + ", ".join(mismatches))


def require_snapshot_harness(args: argparse.Namespace, snapshot_pgo: Path,
                             snapshot_nopgo: Path) -> None:
    """Fail unless every executed harness byte is the frozen snapshot copy.

    ``run_release_gates.sh`` runs the comparator *from* the snapshot and passes
    the snapshot's ``fixed_k.py``.  Pinning the bytes (not the paths) also
    rejects a same-named local override and a ``sys.path`` import that resolved
    to a different module.
    """
    comparator = Path(__file__).resolve()
    comparator_sha = sha256_file(comparator)
    fixed_k_path = Path(args.fixed_k).resolve()
    fixed_k_sha = sha256_file(fixed_k_path)
    module_path = Path(fixed_k.__file__).resolve()
    module_sha = sha256_file(module_path)
    for snapshot in (snapshot_pgo, snapshot_nopgo):
        snapshot_compare = snapshot / "audits/release_compare.py"
        snapshot_fixed = snapshot / "audits/fixed_k.py"
        if not snapshot_compare.is_file():
            raise ReleaseError(
                f"snapshot harness is missing {snapshot_compare}; the release "
                f"gate must run the frozen snapshot comparator")
        if not snapshot_fixed.is_file():
            raise ReleaseError(
                f"snapshot harness is missing {snapshot_fixed}; the release "
                f"gate must run the frozen snapshot fixed-k driver")
        if sha256_file(snapshot_compare) != comparator_sha:
            raise ReleaseError(
                f"harness mismatch: running comparator {comparator} does not "
                f"match the frozen snapshot copy {snapshot_compare}")
        if sha256_file(snapshot_fixed) != fixed_k_sha:
            raise ReleaseError(
                f"harness mismatch: --fixed-k {fixed_k_path} does not match "
                f"the frozen snapshot copy {snapshot_fixed}")
    if module_sha != fixed_k_sha:
        raise ReleaseError(
            f"harness mismatch: imported fixed_k module {module_path} does "
            f"not match --fixed-k {fixed_k_path}")


def load_cohort(cohort: Path) -> tuple[list[fixed_k.CaseSpec], int]:
    try:
        specs = fixed_k.load_cohort_tsv(str(cohort))
        text = cohort.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError, fixed_k.SetupError) as exc:
        raise ReleaseError(str(exc)) from exc
    frozen = frozen_limit(text)
    if frozen is None:
        raise ReleaseError(
            f"{cohort}: no frozen '# conflict_limit: N' comment")
    return specs, frozen


def check_cohort_policy(specs: list[fixed_k.CaseSpec], cohort: Path,
                        limit: int, frozen: int,
                        snapshot_pgo: Path, snapshot_nopgo: Path,
                        cohort_sha: str,
                        allow_limit_override: bool = False) -> dict:
    classes = {s.expected_class for s in specs}
    missing = {"sat", "unsat", "optimal", "incomplete"} - classes
    if missing:
        raise ReleaseError(
            f"{cohort}: release cohort must cover sat, unsat, optimal and "
            f"incomplete; missing {sorted(missing)}")
    modes = {s.mode for s in specs}
    if "satisfy" not in modes or "minimize" not in modes or "maximize" not in modes:
        raise ReleaseError(
            f"{cohort}: release cohort must cover satisfy, minimize and "
            f"maximize")
    if not any(s.exact_counters for s in specs):
        raise ReleaseError(f"{cohort}: no deterministic counter case")
    if not all(s.exact_counters for s in specs):
        raise ReleaseError(
            f"{cohort}: this gate has no portfolio-semantics validator; every "
            f"case must declare exact_counters=true")
    if limit != frozen and not allow_limit_override:
        raise ReleaseError(
            f"{cohort}: frozen conflict limit is {frozen}, requested {limit}")
    models: dict[str, dict] = {}
    for spec in specs:
        rel = Path(spec.model)
        pgo_model = rel if rel.is_absolute() else snapshot_pgo / rel
        nopgo_model = rel if rel.is_absolute() else snapshot_nopgo / rel
        if not pgo_model.is_file():
            raise ReleaseError(f"missing fixture in PGO snapshot: {pgo_model}")
        if not nopgo_model.is_file():
            raise ReleaseError(f"missing fixture in non-PGO snapshot: {nopgo_model}")
        h_pgo = sha256_file(pgo_model)
        h_nopgo = sha256_file(nopgo_model)
        if h_pgo != h_nopgo:
            raise ReleaseError(
                f"incompatible manifests: fixture differs between snapshots: "
                f"{spec.model}")
        models[spec.case_id] = {
            "case_id": spec.case_id,
            "model": spec.model,
            "sha256": h_pgo,
            "mode": spec.mode,
            "expected_class": spec.expected_class,
            "known_answer": spec.known_answer,
            "exact_counters": spec.exact_counters,
            "known_answer_source": spec.known_answer_source,
        }
    snapshot_cohort = snapshot_pgo / "audits/release_cohort.tsv"
    if not snapshot_cohort.is_file():
        raise ReleaseError(
            f"release snapshot is missing audits/release_cohort.tsv: "
            f"{snapshot_cohort}")
    if sha256_file(snapshot_cohort) != cohort_sha:
        raise ReleaseError(
            "incompatible manifests: the cohort passed to the comparator "
            "differs from the frozen snapshot cohort")
    return models


def run_fixed_k(args: argparse.Namespace, cohort: Path, limit: int,
                snapshot_pgo: Path, out: Path) -> dict:
    exe = Path(args.fixed_k).resolve()
    if not exe.is_file():
        raise ReleaseError(f"fixed_k.py not found: {exe}")
    if not os.access(exe, os.R_OK):
        raise ReleaseError(f"fixed_k.py is unreadable: {exe}")
    out.mkdir(parents=True, exist_ok=True)
    log_path = out / "fixed_k.log"
    json_path = out / "fixed_k" / "fixed_k.json"
    # A stale report from an earlier run in the same output directory must
    # never be mistaken for this run's comparison.
    try:
        json_path.unlink()
    except FileNotFoundError:
        pass
    cmd = [
        sys.executable, "-B", str(exe),
        "--cohort-tsv", str(cohort),
        "--limit", str(limit),
        "--binary-a", args.pgo_binary,
        "--binary-b", args.nopgo_binary,
        "--checker-a", args.pgo_binary,
        "--checker-b", args.nopgo_binary,
        "--out", str(out / "fixed_k"),
        "--json", str(json_path),
        "--cap", str(args.cap),
        "--root", str(snapshot_pgo),
        "--lock", args.measure_lock,
        "--require-equal-flags",
    ]
    if not args.taskset:
        cmd.append("--no-taskset")
    start = time.monotonic()
    timed_out = False
    rc: int | None = None
    with log_path.open("w", encoding="utf-8") as log:
        try:
            proc = subprocess.Popen(
                cmd, cwd=snapshot_pgo, stdout=log, stderr=subprocess.STDOUT,
                text=True, start_new_session=True)
        except OSError as exc:
            raise ReleaseError(f"cannot execute fixed_k.py: {exc}") from exc
        try:
            rc = proc.wait(timeout=args.fixed_k_timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except OSError:
                proc.kill()
            rc = proc.wait()
    wall = time.monotonic() - start
    report = None
    report_error = None
    if json_path.is_file():
        try:
            report = json.loads(json_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            report_error = f"cannot parse {json_path}: {exc}"
    else:
        report_error = f"fixed_k.py did not write {json_path}"
    return {
        "command": cmd,
        "exit": rc,
        "timed_out": timed_out,
        "wall_s": wall,
        "log": str(log_path),
        "json_path": str(json_path),
        "report": report,
        "report_error": report_error,
    }


def fixed_k_failures(report: dict | None) -> list[dict]:
    if not report:
        return []
    failures: list[dict] = []
    for case in report.get("cases", []):
        for f in case.get("failures", []):
            failures.append({
                "case_id": case.get("case_id"),
                "class": f.get("class", "unknown"),
                "detail": f.get("detail", ""),
            })
    return failures


def validate_fixed_k(report: dict | None, run: dict, args: argparse.Namespace,
                     pgo: dict, nopgo: dict, specs: list[fixed_k.CaseSpec],
                     models: dict[str, dict], limit: int) -> list[dict]:
    problems: list[dict] = []
    if run["timed_out"]:
        problems.append({"case_id": None, "class": "gate_timeout",
                         "detail": f"fixed_k.py exceeded {args.fixed_k_timeout}s"})
    if run["report_error"]:
        problems.append({"case_id": None, "class": "missing_comparison",
                         "detail": run["report_error"]})
    if run["exit"] != 0:
        problems.append({"case_id": None, "class": "fixed_k_failed",
                         "detail": f"fixed_k.py exit {run['exit']} "
                                   f"(log: {run['log']})"})
    if report is None:
        return problems
    if report.get("status") != "pass":
        problems.append({"case_id": None, "class": "comparison_status",
                         "detail": f"fixed_k status {report.get('status')!r}"})
    if report.get("sha256_a") != pgo["binary"]["sha256"]:
        problems.append({"case_id": None, "class": "stale_comparison",
                         "detail": "fixed_k side A hash does not match the "
                                   "manifest PGO binary"})
    if report.get("sha256_b") != nopgo["binary"]["sha256"]:
        problems.append({"case_id": None, "class": "stale_comparison",
                         "detail": "fixed_k side B hash does not match the "
                                   "manifest non-PGO binary"})
    if report.get("limit") != limit:
        problems.append({"case_id": None, "class": "stale_comparison",
                         "detail": f"fixed_k limit {report.get('limit')} != "
                                   f"{limit}"})
    if report.get("flags_a") != report.get("flags_b"):
        problems.append({"case_id": None, "class": "flags_mismatch",
                         "detail": f"fixed_k used different flags: "
                                   f"{report.get('flags_a')!r} vs "
                                   f"{report.get('flags_b')!r}"})
    cases = report.get("cases", [])
    if len(cases) != len(specs):
        problems.append({"case_id": None, "class": "missing_comparison",
                         "detail": f"fixed_k compared {len(cases)} cases, "
                                   f"cohort has {len(specs)}"})
    ids = {c.get("case_id") for c in cases}
    expected_ids = {s.case_id for s in specs}
    if ids != expected_ids:
        problems.append({"case_id": None, "class": "missing_comparison",
                         "detail": f"fixed_k case ids differ; missing="
                                   f"{sorted(expected_ids - ids)}, "
                                   f"extra={sorted(ids - expected_ids)}"})
    spec_by_id = {s.case_id: s for s in specs}
    for case in cases:
        spec = spec_by_id.get(case.get("case_id"))
        if spec is None:
            continue
        expected_meta = {
            "model": spec.model,
            "mode": spec.mode,
            "expected_class": spec.expected_class,
            "known_answer": spec.known_answer,
            "exact_counters": spec.exact_counters,
        }
        for key, want in expected_meta.items():
            if case.get(key) != want:
                problems.append({
                    "case_id": spec.case_id,
                    "class": "stale_comparison",
                    "detail": f"fixed_k {key}={case.get(key)!r} != cohort "
                              f"{want!r}",
                })
        expected_model_sha = models.get(spec.case_id, {}).get("sha256")
        if case.get("model_sha256") != expected_model_sha:
            problems.append({
                "case_id": spec.case_id,
                "class": "stale_comparison",
                "detail": f"fixed_k model_sha256={case.get('model_sha256')!r} "
                          f"!= frozen fixture {expected_model_sha!r}",
            })
    summary = report.get("summary", {})
    if summary.get("failed", 0) != 0:
        problems.append({"case_id": None, "class": "case_failures",
                         "detail": f"{summary.get('failed')} case(s) failed"})
    if summary.get("cases") != len(specs):
        problems.append({"case_id": None, "class": "missing_comparison",
                         "detail": f"fixed_k summary cases="
                                   f"{summary.get('cases')}"})
    witness_sum = sum(int(c.get("witnesses_checked", 0)) for c in cases)
    if summary.get("witnesses_checked") != witness_sum:
        problems.append({
            "case_id": None, "class": "missing_witness_check",
            "detail": f"fixed_k summary witnesses_checked="
                      f"{summary.get('witnesses_checked')} but cases sum to "
                      f"{witness_sum}",
        })
    # No skipped witness check: every emitted block must have been covered.
    for case in cases:
        emitted = int(case.get("a", {}).get("solutions", 0)) + \
            int(case.get("b", {}).get("solutions", 0))
        if emitted and int(case.get("witnesses_checked", 0)) < emitted:
            problems.append({
                "case_id": case.get("case_id"),
                "class": "missing_witness_check",
                "detail": f"{emitted} emitted solution(s) but only "
                          f"{case.get('witnesses_checked')} checked",
            })
        if case.get("expected_class") in {"sat", "optimal"} and \
                emitted < 2:
            problems.append({
                "case_id": case.get("case_id"),
                "class": "missing_solution",
                "detail": f"{case.get('expected_class')} case emitted "
                          f"{emitted} total solution(s) from both sides",
            })
    return problems


def _oracle_summary(provenance: dict | None) -> str:
    if not provenance:
        return "not recorded"
    if not provenance.get("present"):
        return "MISSING" + ("" if provenance.get("required")
                            else " (not required)")
    mzn = provenance.get("minizinc") or {}
    gec = provenance.get("fzn_gecode") or {}
    return (f"minizinc {mzn.get('version')} ({mzn.get('sha256')}), "
            f"fzn-gecode {gec.get('version')} ({gec.get('sha256')})")


def write_outputs(out: Path, manifest: dict | None, run: dict | None,
                  report: dict | None, problems: list[dict],
                  args: argparse.Namespace, cohort: Path, limit: int,
                  specs: list[fixed_k.CaseSpec], manifest_path: Path,
                  comparison_path: Path) -> int:
    status = "pass" if not problems else "fail"
    cohort_sha = sha256_file(cohort) if cohort.is_file() else None
    comparison = {
        "schema_version": SCHEMA_VERSION,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "status": status,
        "cohort": {
            "path": str(cohort),
            "sha256": cohort_sha,
            "cases": len(specs),
            "limit": limit,
        },
        "manifest": str(manifest_path),
        "manifest_sha256": manifest.get("manifest_sha256") if manifest else None,
        "pgo": {
            "binary": args.pgo_binary,
            "sha256": manifest["variants"]["pgo"]["binary"]["sha256"]
            if manifest else None,
        },
        "nopgo": {
            "binary": args.nopgo_binary,
            "sha256": manifest["variants"]["nopgo"]["binary"]["sha256"]
            if manifest else None,
        },
        "fixed_k": {
            "exit": run["exit"] if run else None,
            "timed_out": run["timed_out"] if run else None,
            "wall_s": run["wall_s"] if run else None,
            "log": run["log"] if run else None,
            "json": run["json_path"] if run else None,
        },
        "cases": report.get("cases", []) if report else [],
        "failures": problems,
        "summary": {
            "cases": len(specs),
            "passed": sum(1 for c in (report or {}).get("cases", [])
                          if c.get("passed")),
            "failed": sum(1 for c in (report or {}).get("cases", [])
                          if not c.get("passed")),
            "witnesses_checked": (report or {}).get("summary", {}).get(
                "witnesses_checked", 0),
            "known_answer_checks": sum(
                2 for s in specs if s.known_answer is not None),
            "unsat_known_answers": sum(
                1 for s in specs if s.expected_class == "unsat"),
            "optimal_known_answers": sum(
                1 for s in specs if s.expected_class == "optimal"),
        },
        "oracles": {
            "witness_checks": (report or {}).get("summary", {}).get(
                "witnesses_checked", 0),
            "checker_policy": "every emitted block from both binaries checked "
                              "by both leanfzn check front doors",
            "known_answer_checks": sum(
                2 for s in specs if s.known_answer is not None),
            "required": bool(getattr(args, "require_oracle", False)),
            "provenance": (manifest or {}).get("oracles"),
        },
    }
    comparison_path.parent.mkdir(parents=True, exist_ok=True)
    comparison_path.write_text(
        json.dumps(comparison, indent=2) + "\n", encoding="utf-8")

    lines = [
        f"RELEASE GATE: {'PASS' if status == 'pass' else 'FAIL'}",
        f"cohort: {cohort} ({len(specs)} cases, limit {limit})",
        f"pgo:   {args.pgo_binary} "
        f"{comparison['pgo']['sha256'] or 'unknown'}",
        f"nopgo: {args.nopgo_binary} "
        f"{comparison['nopgo']['sha256'] or 'unknown'}",
        "oracle: " + _oracle_summary(comparison["oracles"]["provenance"]),
    ]
    if report:
        for case in report.get("cases", []):
            tag = "PASS" if case.get("passed") else "FAIL"
            classes = ",".join(
                f"{f.get('class')}: {f.get('detail')}"
                for f in case.get("failures", [])) or "-"
            lines.append(
                f"[{tag}] {case.get('case_id')} "
                f"outcome={case.get('a', {}).get('outcome')}/"
                f"{case.get('b', {}).get('outcome')} "
                f"expected={case.get('expected_class')} "
                f"objective={case.get('a', {}).get('objective')}/"
                f"{case.get('b', {}).get('objective')} "
                f"witnesses={case.get('witnesses_checked')} "
                f"failures={classes}")
    if problems:
        lines.append("failures:")
        for problem in problems:
            lines.append(
                f"  - {problem.get('case_id') or 'gate'}: "
                f"{problem.get('class')}: {problem.get('detail')}")
    lines.append(f"manifest: {manifest_path}")
    lines.append(f"comparison: {comparison_path}")
    summary_path = out / "summary.txt"
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if not args.quiet:
        print("\n".join(lines))
    elif problems:
        # Quiet means quiet on success only; a failed gate must still explain
        # itself on the console (CI logs otherwise show an empty failure).
        print("\n".join(lines), file=sys.stderr)
    return 0 if status == "pass" else 1


def main() -> int:
    args = parse_args()
    # Resolve path-valued options once: fixed_k.py runs with its cwd set to the
    # snapshot, so relative binary/checker/lock paths from the caller would
    # otherwise be interpreted against the wrong directory.
    for attr in ("pgo_binary", "nopgo_binary", "fixed_k", "measure_lock",
                 "manifest", "comparison", "expected_manifest"):
        value = getattr(args, attr)
        if value is not None:
            setattr(args, attr, str(Path(value).resolve()))
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest_path = Path(args.manifest) if args.manifest else out / "manifest.json"
    comparison_path = (Path(args.comparison) if args.comparison
                       else out / "comparison.json")
    cohort = Path(args.cohort)
    if not cohort.is_absolute():
        cohort = (Path.cwd() / cohort).resolve()
    snapshot_pgo = Path(args.snapshot_pgo).resolve()
    snapshot_nopgo = Path(args.snapshot_nopgo).resolve()
    specs: list[fixed_k.CaseSpec] = []
    limit = args.limit or DEFAULT_LIMIT

    try:
        if not cohort.is_file():
            raise ReleaseError(f"cohort not found: {cohort}")
        if not snapshot_pgo.is_dir():
            raise ReleaseError(f"PGO snapshot not found: {snapshot_pgo}")
        if not snapshot_nopgo.is_dir():
            raise ReleaseError(f"non-PGO snapshot not found: {snapshot_nopgo}")
        if args.require_snapshot_harness:
            require_snapshot_harness(args, snapshot_pgo, snapshot_nopgo)
        specs, frozen = load_cohort(cohort)
        if args.limit is not None and args.limit != frozen:
            if not args.allow_limit_override:
                raise ReleaseError(
                    f"{cohort}: frozen conflict limit is {frozen}; refusing "
                    f"override {args.limit} without --allow-limit-override")
            limit = args.limit
        else:
            limit = frozen
        pgo_binary = binary_info(args.pgo_binary)
        nopgo_binary = binary_info(args.nopgo_binary)
        pgo = variant_manifest(snapshot_pgo, pgo_binary, "pgo")
        nopgo = variant_manifest(snapshot_nopgo, nopgo_binary, "nopgo")
        # Validate every cohort fixture before the general source-set
        # comparison: a deleted fixture must be reported as such rather than
        # as an anonymous snapshot difference.
        cohort_sha = sha256_file(cohort)
        models = check_cohort_policy(
            specs, cohort, limit, frozen, snapshot_pgo, snapshot_nopgo,
            cohort_sha, allow_limit_override=args.allow_limit_override)
        compatibility = compare_variants(pgo, nopgo)
        manifest = {
            "schema_version": SCHEMA_VERSION,
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "release_id": os.environ.get("RELEASE_ID", out.name),
            "git": git_provenance(Path(args.git_root)),
            "environment": {
                "python": sys.version.split()[0],
                "platform": platform.platform(),
                "machine": platform.machine(),
            },
            "tooling": {
                "fixed_k": {
                    "path": str(Path(args.fixed_k).resolve()),
                    "sha256": sha256_file(Path(args.fixed_k)),
                },
                "release_compare": {
                    "path": str(Path(__file__).resolve()),
                    "sha256": sha256_file(Path(__file__)),
                },
            },
            "cohort": {
                "path": str(cohort),
                "sha256": cohort_sha,
                "limit": limit,
                "frozen_limit": frozen,
                "limit_override": limit != frozen,
                "cases": models,
            },
            "solver": {
                "flags": [],
                "cap": args.cap,
                "taskset": bool(args.taskset),
                "checker_policy": "both binaries' check front doors",
                "stats_schema": fixed_k.MANDATORY_STATS,
                "exact_action_keys": fixed_k.ACTION_KEYS,
                "exact_aux_keys": fixed_k.AUX_KEYS,
            },
            "oracles": oracle_provenance(args.require_oracle),
            "variants": {"pgo": pgo, "nopgo": nopgo},
            "compatibility": compatibility,
        }
        manifest["manifest_sha256"] = canonical_sha256(manifest)
        if args.expected_manifest:
            verify_expected_manifest(args.expected_manifest, manifest)
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    except ReleaseError as exc:
        print(f"error: {exc}", file=sys.stderr)
        write_outputs(out, None, None, None,
                      [{"case_id": None, "class": "setup_error",
                        "detail": str(exc)}],
                      args, cohort, limit, specs, manifest_path,
                      comparison_path)
        return 2

    try:
        run = run_fixed_k(args, cohort, limit, snapshot_pgo, out)
    except ReleaseError as exc:
        print(f"error: {exc}", file=sys.stderr)
        write_outputs(out, manifest, None, None,
                      [{"case_id": None, "class": "setup_error",
                        "detail": str(exc)}],
                      args, cohort, limit, specs, manifest_path,
                      comparison_path)
        return 2
    report = run["report"]
    problems = fixed_k_failures(report)
    problems.extend(validate_fixed_k(report, run, args, pgo, nopgo, specs,
                                     models, limit))
    # De-duplicate the fixed-k failures that validate_fixed_k already turns
    # into a summary item; keep the detailed per-case entries.
    seen: set[tuple] = set()
    unique: list[dict] = []
    for problem in problems:
        key = (problem.get("case_id"), problem.get("class"),
               problem.get("detail"))
        if key not in seen:
            seen.add(key)
            unique.append(problem)
    return write_outputs(out, manifest, run, report, unique, args, cohort,
                         limit, specs, manifest_path, comparison_path)


if __name__ == "__main__":
    sys.exit(main())

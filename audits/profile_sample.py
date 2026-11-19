#!/usr/bin/env python3
"""Sampling profiler for the leanfzn binary (dev-only; Linux x86_64).

The devcontainer has no perf/gdb/valgrind. This samples the instruction
pointer of the busiest thread with ptrace and maps it to symbols with `nm`.
Self counts are exact samples; "inclusive" counts come from a heuristic scan
of the top 4 KiB of the stack for return addresses and contain some noise
(stale frames). Use it to rank hotspots, not to quote precise percentages.

Usage:
  python3 audits/profile_sample.py [--seconds 8] [--top 30] -- \
      .lake/build/bin/leanfzn solve [FLAGS] MODEL.fzn
"""
import argparse
import bisect
import collections
import ctypes
import os
import signal
import subprocess
import sys
import time

PTRACE_PEEKDATA, PTRACE_GETREGS, PTRACE_CONT = 2, 12, 7
PTRACE_SEIZE, PTRACE_INTERRUPT = 0x4206, 0x4207
WALL = 0x40000000  # __WALL: wait for non-leader threads too


class Regs(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulonglong) for n in (
        "r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax "
        "rip cs eflags rsp ss fs_base gs_base ds es fs gs").split()]


def load_symbols(binary):
    out = subprocess.run(["nm", "-n", "-C", "--defined-only", binary],
                         capture_output=True, text=True, check=True).stdout
    syms = []
    for line in out.splitlines():
        parts = line.split(" ", 2)
        if len(parts) == 3 and parts[1] in "tTwW":
            syms.append((int(parts[0], 16), parts[2]))
    return syms


def thread_cpu(pid, tid):
    fields = open(f"/proc/{pid}/task/{tid}/stat").read().rsplit(")", 1)[1].split()
    return int(fields[11]) + int(fields[12])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=8.0)
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument("--interval", type=float, default=0.004)
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    if not cmd:
        ap.error("missing command")
    binary = os.path.realpath(cmd[0])
    syms = load_symbols(binary)
    addrs = [s for s, _ in syms]
    lo, hi = addrs[0], addrs[-1]

    def name(off):
        i = bisect.bisect_right(addrs, off) - 1
        return syms[i][1] if i >= 0 else "?"

    libc = ctypes.CDLL(None, use_errno=True)
    libc.ptrace.restype = ctypes.c_long
    libc.ptrace.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p]

    pid = os.fork()
    if pid == 0:
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.execv(binary, [binary] + cmd[1:])
    time.sleep(1.2)  # let the Lean worker thread start, even under load
    base = None
    for line in open(f"/proc/{pid}/maps"):
        if line.rstrip().endswith(binary):
            base = int(line.split("-")[0], 16) - int(line.split()[2], 16)
            break
    tids = [int(t) for t in os.listdir(f"/proc/{pid}/task")]
    tid = max(tids, key=lambda t: thread_cpu(pid, t))
    # Non-binary PCs are resolved against the shared objects that the process
    # has mapped.  Without this every libc/runtime PC would map to `_fini`
    # (the last binary symbol), which hid the allocation hot spots.
    shlibs = []
    for line in open(f"/proc/{pid}/maps"):
        q = line.split()
        if len(q) >= 6 and "x" in q[1] and not q[5].endswith(os.path.basename(binary)):
            a0, a1 = (int(x, 16) for x in q[0].split("-"))
            shlibs.append((a0, a1, int(q[2], 16), q[5]))
    dyn = {}

    def extern(rip):
        for a0, a1, off, path in shlibs:
            if a0 <= rip < a1:
                if path not in dyn and path.startswith("/"):
                    try:
                        out = subprocess.run(["nm", "-D", "-n", "--defined-only", path],
                                             capture_output=True, text=True).stdout
                        t = [(int(l.split()[0], 16), l.split()[-1]) for l in out.splitlines()
                             if len(l.split()) == 3 and l.split()[1] in "tTwWi"]
                    except Exception:
                        t = []
                    dyn[path] = t
                t = dyn.get(path) or []
                o = rip - a0 + off
                i = bisect.bisect_right([x for x, _ in t], o) - 1
                return f"[{os.path.basename(path)}]" + (t[i][1] if i >= 0 else "?")
        return "[anon]"
    if libc.ptrace(PTRACE_SEIZE, tid, None, None) != 0:
        sys.exit(f"ptrace seize failed: errno {ctypes.get_errno()}")

    self_c, incl_c, n = collections.Counter(), collections.Counter(), 0
    ext_c = collections.Counter()
    regs = Regs()
    deadline = time.time() + a.seconds
    while time.time() < deadline:
        if libc.ptrace(PTRACE_INTERRUPT, tid, None, None) != 0:
            break
        _, status = os.waitpid(tid, WALL)
        if os.WIFEXITED(status) or os.WIFSIGNALED(status):
            break
        if libc.ptrace(PTRACE_GETREGS, tid, None, ctypes.byref(regs)) == 0:
            n += 1
            inbin = lo <= regs.rip - base <= hi
            leaf = name(regs.rip - base) if inbin else extern(regs.rip)
            if not inbin:
                # Attribute an external leaf to the first in-binary caller on
                # the stack (allocation, refcount and hash-table entries).
                for k in range(0, 256, 8):
                    v = libc.ptrace(PTRACE_PEEKDATA, tid, ctypes.c_void_p(regs.rsp + k), None)
                    v = (v & ((1 << 64) - 1)) - base
                    if lo <= v <= hi:
                        ext_c[name(v)] += 1
                        break
            self_c[leaf] += 1
            seen = {leaf}
            for k in range(0, 4096, 8):
                v = libc.ptrace(PTRACE_PEEKDATA, tid, ctypes.c_void_p(regs.rsp + k), None)
                v = (v & ((1 << 64) - 1)) - base
                if lo <= v <= hi:
                    g = name(v)
                    if g not in seen:
                        seen.add(g)
                        incl_c[g] += 1
            incl_c[leaf] += 1
        libc.ptrace(PTRACE_CONT, tid, None, None)
        time.sleep(a.interval)
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    print(f"samples={n} cmd={' '.join(cmd)}")
    if n == 0:
        return
    print("== self ==")
    for f, c in self_c.most_common(a.top):
        print(f"{100 * c / n:5.1f}% {f[:160]}")
    print("== extern-callers ==")
    for f, c in ext_c.most_common(12):
        print(f"{100 * c / n:5.1f}% {f[:160]}")
    print("== inclusive (HEURISTIC stack scan; approximate, stale frames possible) ==")
    for f, c in incl_c.most_common(2 * a.top):
        print(f"{100 * c / n:5.1f}% {f[:160]}")


if __name__ == "__main__":
    main()

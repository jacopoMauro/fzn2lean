# LeanFzn for MiniZinc

This directory lets MiniZinc use LeanFzn as a solver:

```bash
minizinc --solver leanfzn model.mzn data.dzn
```

MiniZinc compiles the model to FlatZinc. Globals listed in `mznlib/` are kept
as single constraints; every other global uses MiniZinc's standard
decomposition. MiniZinc then calls `fzn-leanfzn`, which runs `leanfzn solve`,
and MiniZinc prints the solutions in the model's own output format.

There are two ways to set it up:

- **Docker (recommended):** an image with MiniZinc 2.10.1 and LeanFzn as its
  default solver. It needs nothing on the host except Docker.
- **An existing MiniZinc installation:** add LeanFzn to a MiniZinc you already
  have, either with `install.sh` or by hand.

## Docker (recommended)

Build the image from the **repository root**, which is the build context:

```bash
docker build -f minizinc-wrapper/Dockerfile -t leanfzn-minizinc .
```

The build has three stages:

1. It compiles `leanfzn` with the Lean toolchain pinned in `lean-toolchain`.
   It builds the verified library from scratch. On 8 cores this takes about
   10 minutes and peaks at about 11 GB of memory. Docker Desktop's default
   memory limit may be lower, so raise it if the build is killed.
2. It downloads the official MiniZinc 2.10.1 bundle, checks it against the
   same pinned SHA-256 as `install.sh`, and keeps only the command-line tools.
3. It assembles the runtime image. LeanFzn is registered in MiniZinc's own
   solver directory and set as the **default solver**, and the image runs
   `test.sh`. A broken image therefore fails the build.

The image's entry point is `minizinc`. Mount the directory that holds your
model and run it like `minizinc`:

```bash
docker run --rm -v "$PWD:/work" leanfzn-minizinc model.mzn data.dzn
docker run --rm -v "$PWD:/work" leanfzn-minizinc model.mzn data.dzn -t 60000 -s
docker run --rm -v "$PWD:/work" leanfzn-minizinc model.mzn --var wdeg --restart luby
docker run --rm leanfzn-minizinc --solvers          # also the default command
```

- `--solver leanfzn` is optional, because LeanFzn is the default.
- MiniZinc's bundled solvers are available too, for example
  `--solver gecode`, `chuffed` or `cp-sat`, which is handy for comparing
  results.
- Every flag in [Usage](#usage) works the same way.
- Paths are relative to `/work`, the mounted directory.
- Ctrl-C stops the run; `tini` forwards the signal and the wrapper kills
  `leanfzn`.
- Files written into `/work` (`--fzn`, `-o`) are owned by root. Add
  `--user "$(id -u):$(id -g)"` to keep your ownership.

For a shell inside the image:

```bash
docker run --rm -it -v "$PWD:/work" --entrypoint bash leanfzn-minizinc
```

Inside the image, the files are laid out as follows:

| Path | Contents |
| --- | --- |
| `/opt/minizinc/` | MiniZinc 2.10.1 (`bin/` is on `PATH`) |
| `/opt/minizinc/share/minizinc/solvers/leanfzn.msc` | Solver registration |
| `/opt/minizinc/share/minizinc/Preferences.json` | Makes LeanFzn the default solver |
| `/opt/leanfzn/minizinc-wrapper/` | This directory |
| `/opt/leanfzn/.lake/build/bin/leanfzn` | Solver binary, where the wrapper looks by default |

Rebuild the image after changing the solver: `docker build` reuses the cached
toolchain and MiniZinc layers.

## Adding LeanFzn to an existing MiniZinc installation

Use this when MiniZinc is already installed, for example with the IDE or
other solvers, and LeanFzn should appear next to them. Use MiniZinc 2.10.1:
LeanFzn's FlatZinc semantics are pinned to its standard library
(`specification/`).

### With `install.sh`

From the repository root:

```bash
minizinc-wrapper/install.sh                  # also installs MiniZinc 2.10.1 if needed
minizinc-wrapper/install.sh --skip-minizinc  # keep the minizinc you already have
```

This does three things, all inside your home directory (no root):

1. Updates `leanfzn` with `lake build leanfzn`, using the incremental build
   to ensure that an existing binary matches the source.
2. Installs **MiniZinc 2.10.1** if the `minizinc` on your `PATH` is another
   version. LeanFzn's FlatZinc semantics are pinned to the MiniZinc 2.10.1
   standard library (`specification/`), so use that version. The official
   release bundle is downloaded, verified against a pinned SHA-256, unpacked
   into `~/.local/opt/MiniZincIDE-2.10.1-x86_64-linux-gnu/`, and linked as
   `~/.local/bin/minizinc`. That directory must come before `/usr/bin` on your
   `PATH`; the script tells you if it does not.
3. Registers the solver by writing `~/.minizinc/solvers/leanfzn.msc` with
   absolute paths to this directory. MiniZinc reads every `.msc` file in that
   directory automatically, from the command line and from the MiniZinc IDE.

Check it:

```bash
minizinc --version                  # ... version 2.10.1
minizinc --solvers | grep LeanFzn   # LeanFzn 0.1.0 (org.leanfzn.leanfzn, leanfzn, int)
minizinc --solver leanfzn minizinc-wrapper/examples/queens.mzn
minizinc-wrapper/test.sh            # smoke test, see below
```

Options:

| Command | Effect |
| --- | --- |
| `install.sh --skip-minizinc` | Only build and register; keep the `minizinc` you already have |
| `install.sh --uninstall` | Remove the registration and the `~/.local/bin/minizinc` link (the unpacked MiniZinc stays in `~/.local/opt`) |

Rerun `install.sh` after moving the repository; the registration stores
absolute paths. The wrapper always runs the current build at
`.lake/build/bin/leanfzn`, so rebuilding needs no reinstall.

### By hand

A MiniZinc solver is a `.msc` file (a JSON solver configuration) in a
directory that MiniZinc searches. To register LeanFzn yourself:

1. **Build the solver:** run `lake build leanfzn` in the repository.
   `leanfzn` needs only the C library at run time, and the wrapper needs
   `python3`. To keep the binary somewhere other than
   `<repo>/.lake/build/bin/leanfzn`, set `LEANFZN_BIN=/path/to/leanfzn` in
   the environment MiniZinc runs in.
2. **Write the configuration:** copy `leanfzn.msc` and make `executable` and
   `mznlib` absolute paths. MiniZinc 2.10.1 does not resolve a relative
   `executable`. With the repository at `/path/to/fzn2lean`:

   ```json
   {
     "id": "org.leanfzn.leanfzn",
     "name": "LeanFzn",
     "version": "0.1.0",
     "executable": "/path/to/fzn2lean/minizinc-wrapper/fzn-leanfzn",
     "mznlib": "/path/to/fzn2lean/minizinc-wrapper/mznlib",
     "tags": ["leanfzn", "int"],
     "stdFlags": ["-a", "-i", "-n", "-f", "-p", "-r", "-s", "-t", "-v"],
     "supportsFzn": true,
     "needsSolns2Out": true
   }
   ```

   Keep the `extraFlags` list from the in-tree `leanfzn.msc` so that
   `--var`, `--restart` and the other LeanFzn flags work on the `minizinc`
   command line. Without it, they can still be given through `--fzn-flags`.
3. **Put the file where MiniZinc looks.** Use one of these:

   | Location | Scope |
   | --- | --- |
   | `~/.minizinc/solvers/leanfzn.msc` | The current user (what `install.sh` does) |
   | `<minizinc>/share/minizinc/solvers/leanfzn.msc` | Every user of that installation (what the Docker image does) |
   | Any directory listed in `MZN_SOLVER_PATH` (`:`-separated) | Per shell or per job, for example on a cluster |

   `minizinc --config-dirs` prints the directories this installation reads.
4. **Check it:** `minizinc --solvers` should list
   `LeanFzn 0.1.0 (org.leanfzn.leanfzn, leanfzn, int)`. Then run
   `minizinc --solver leanfzn minizinc-wrapper/examples/queens.mzn`.
5. **Optional: make LeanFzn the default solver,** so that `minizinc model.mzn`
   uses it. Set `tagDefaults` in `~/.minizinc/Preferences.json`, or in
   `<minizinc>/share/minizinc/Preferences.json` for every user:

   ```json
   { "tagDefaults": [["", "org.leanfzn.leanfzn"]] }
   ```

   If the file already exists, change only the `tagDefaults` entry.

**MiniZinc IDE:** the IDE reads the same solver directories. After you
restart it, LeanFzn appears in the solver list, and its flags appear under
the solver configuration's extra options.

### Without installing

The in-tree `leanfzn.msc` uses paths relative to itself. MiniZinc 2.9.3
resolves them, but **2.10.1 does not resolve a relative `executable`** (with
`--solver path/to/leanfzn.msc` or `MZN_SOLVER_PATH`, it fails with "Error
occurred when executing FZN solver"). On 2.10.1, use `install.sh
--skip-minizinc`, which writes a copy with absolute paths, or put the
wrapper directory on `PATH`:

```bash
PATH="$PWD/minizinc-wrapper:$PATH" minizinc --solver minizinc-wrapper/leanfzn.msc model.mzn
```

## Usage

```bash
minizinc --solver leanfzn model.mzn data.dzn          # solve
minizinc --solver leanfzn model.mzn -t 60000          # 60 s solver time limit
minizinc --solver leanfzn model.mzn --time-limit 60000  # 60 s including compilation
minizinc --solver leanfzn model.mzn -s                # with statistics
minizinc --solver leanfzn model.mzn -p 4              # 4-worker portfolio
minizinc --solver leanfzn model.mzn --var wdeg --restart luby
minizinc --solver leanfzn model.mzn --fzn-flags "--opt=seeded --presolve=dedup"
```

### MiniZinc flags

| Flag | Behaviour |
| --- | --- |
| `-t MS` | Enforced by the wrapper, because the Core engine has no wall-clock limit. Solutions are streamed, so every incumbent found before the limit is kept. If none was found, the status is `=====UNKNOWN=====`. |
| `-a`, `-i` | Optimization always streams each improving solution. For a satisfaction model LeanFzn reports one solution and cannot enumerate all of them; `-a` prints a note to stderr and never claims the search was exhaustive. |
| `-n N` | Stop after `N` solutions. MiniZinc passes it only for satisfaction models. |
| `-s` | Statistics as `%%%mzn-stat:` lines: `nodes` (decisions), `failures` (conflicts), `propagations`, `learned`, `incumbents`, `complete`, `compile_ms`, `search_ms` and the other `leanfzn --stats` counters. |
| `-p N` | `--threads=min(N,8)` portfolio for satisfaction or optimization models. It is ignored with a note when a strategy flag is set. |
| `-f` | Accepted. LeanFzn's default search already ignores search annotations; use `--strategy annot` to follow them. |
| `-r SEED` | Accepted and ignored: Core search is deterministic and has no seed. |
| `-v` | Print the `leanfzn` command line to stderr. |

### LeanFzn flags

These are listed in `leanfzn.msc`, so `minizinc --help leanfzn` shows
them, and they can be given directly:
`--var`, `--val`, `--opt`, `--restart`, `--restart-base`, `--presolve`,
`--conflict-limit` and `--strategy`. Any of these, plus `--primal`,
`--primal-time`, `--prop`, `--engine` and the `--heur-*` switches, can also be
passed as `--fzn-flags "--name=value ..."`. The repository `README.md` documents
each option. An option the wrapper does not know is an error, never silently
dropped.

### Results and exit status

The wrapper only passes on verdicts that `leanfzn` printed itself:
`==========` (optimum proved) and `=====UNSATISFIABLE=====` are certified by
the verified engine. Everything else is reported honestly:

| `leanfzn solve` outcome | MiniZinc sees |
| --- | --- |
| Solution / proved optimum (exit 0) | Solutions, then `==========` for a proved optimum |
| Certified UNSAT (exit 1) | `=====UNSATISFIABLE=====` |
| Unsupported model (exit 3), or FlatZinc that `leanfzn` cannot parse (e.g. floats) | `=====UNSUPPORTED=====`, with the reason on stderr. MiniZinc 2.9.3 displays this as `=====UNKNOWN=====`. |
| Unknown / incomplete (exit 4), time limit, or solution limit | The incumbents found so far; `=====UNKNOWN=====` if there were none |
| Bad option or malformed input (exit 2), or a crash | `=====ERROR=====` and a non-zero exit |

If the wrapper is killed (for example by MiniZinc's `--time-limit`), the
`leanfzn` process is killed with it.

### What the guarantees cover

LeanFzn's theorems are stated on the FlatZinc model. With the standard
library, the step from `.mzn` to `.fzn` is MiniZinc's own compiler, exactly as
for every other FlatZinc solver. `test.sh` also re-checks the solutions of the
example models with `leanfzn check` on the generated FlatZinc. To verify a run
yourself:

```bash
minizinc -c --solver leanfzn model.mzn data.dzn --fzn model.fzn --ozn model.ozn
.lake/build/bin/leanfzn solve model.fzn > model.sol
.lake/build/bin/leanfzn check model.fzn model.sol
minizinc --ozn-file model.ozn < model.sol    # only if the model has no
                                             # non-output variables; otherwise
                                             # use the wrapper, which filters them
```

## Challenge test

`challenge_test.py` runs every challenge instance (`.mzn` + data) through
`minizinc --solver leanfzn` and checks each run:

- **Witness:** every solution `leanfzn` printed is re-verified by
  `leanfzn check` against the FlatZinc that MiniZinc generated. It uses the
  wrapper's `FZN_LEANFZN_SAVE_DIR` hook, which saves `model.fzn` and the
  unfiltered output `raw.sol`.
- **Challenge oracle** (`challengeResults<year>.csv`): a claimed UNSAT must not
  contradict a solver that found a solution, and a proved optimum must equal
  every complete result and must not be beaten by any found objective.
- **End to end:** the `_objective` MiniZinc prints equals the objective in
  `leanfzn`'s own last solution.

```bash
minizinc-wrapper/challenge_test.py                       # all 200 instances, -t 20000
minizinc-wrapper/challenge_test.py --years 2025 --only is mondoku --time-limit 10000
```

Runs use systemd user scopes as memory caps (`--mem`, default 5G; instances
whose pre-compiled FlatZinc is over `--big-mb` run one at a time under
`--big-mem`, default 18G; an instance without a pre-compiled `.fzn` that
fails under `--mem` is rerun the same way). Results go to `tmp/minizinc-wrapper/challenge/`
(`results.jsonl`, `summary.txt`, and per-run `stdout.txt`/`stderr.txt`/`raw.sol`).

## Keeping globals intact (`mznlib/`)

`mznlib/` is the solver-specific global library, which MiniZinc searches
before its standard library. A file `mznlib/fzn_<global>.mzn` with a bodiless
declaration keeps that global as one FlatZinc constraint, for example:

```minizinc
% mznlib/fzn_all_different_int.mzn
predicate fzn_all_different_int(array [int] of var int: x);
```

The directory is **empty on purpose**. `leanfzn solve` does not yet compile any
`fzn_*` global. It also rejects the `predicate` declaration MiniZinc emits for
a kept global, so the file above would turn every model using
`all_different` into `=====UNSUPPORTED=====`. LeanFzn's semantics and checker
already define the 138 `fzn_*` globals of the 2.10.1 library
(`LeanFzn/Semantics/Globals.lean`), but solving one needs, per global:

1. acceptance of the matching bodiless `predicate` item in the compiler;
2. a translation into Core proved in both directions, preserving source
   satisfaction and compiled solutions;
3. ideally a dedicated propagator with a soundness proof. Without one, the
   global is only checked, and pruning is weaker than the decomposition MiniZinc
   would otherwise emit.

Add a global's file here only once those exist. Do not put hand-written
decompositions in `mznlib/`: they would sit unverified between the model and
the certified FlatZinc.

## Files

| File | Purpose |
| --- | --- |
| `fzn-leanfzn` | The wrapper MiniZinc calls (Python 3, standard library only) |
| `leanfzn.msc` | Solver configuration with paths relative to this directory |
| `Dockerfile` | Image with MiniZinc 2.10.1 and LeanFzn as default solver (build from the repository root) |
| `Dockerfile.dockerignore` | Keeps `.git`, `.lake`, `tmp/` and the challenge files out of the build context |
| `install.sh` | Build, MiniZinc 2.10.1 install and solver registration |
| `test.sh` | Smoke test: `./test.sh [path/to/minizinc]` |
| `challenge_test.py` | End-to-end run over `minizinc-challenge/<year>mzn` with witness and challenge-oracle checks (dev tool; see below) |
| `mznlib/` | Solver-specific global library (currently empty) |
| `examples/` | `queens` (SAT), `packing` (optimization), `unsat`, `golomb` (hard, use `-t`), `float` (unsupported) |

## Troubleshooting

- **`Solver 'leanfzn' not found`:** run `install.sh`, or check that
  `~/.minizinc/solvers/leanfzn.msc` exists (`minizinc --config-dirs` shows the
  directory MiniZinc reads).
- **`leanfzn binary not found`:** run `lake build leanfzn` in the repository,
  or set `LEANFZN_BIN=/path/to/leanfzn`.
- **Wrong MiniZinc version:** `which minizinc` should be
  `~/.local/bin/minizinc`. Put `~/.local/bin` first on `PATH`, or call
  `~/.local/opt/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc` directly.
- **`=====UNSUPPORTED=====`:** the model needs a construct outside LeanFzn's
  certified fragment (floats, general set constraints and so on; see "Supported
  FlatZinc" in the repository `README.md`). The reason is on stderr.

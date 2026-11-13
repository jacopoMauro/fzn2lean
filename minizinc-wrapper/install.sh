#!/usr/bin/env bash
# Register LeanFzn as a MiniZinc solver, and install the pinned MiniZinc
# 2.10.1 if the `minizinc` on PATH is a different version.
#
#   ./install.sh                 update leanfzn, install MiniZinc
#                                2.10.1 if needed, register the solver
#   ./install.sh --skip-minizinc register only; keep whatever minizinc is on PATH
#   ./install.sh --uninstall     remove the solver registration and, if this
#                                script installed it, the MiniZinc 2.10.1 link
#
# Everything goes into the user's home directory; nothing needs root:
#   ~/.minizinc/solvers/leanfzn.msc          solver registration
#   ~/.local/opt/MiniZincIDE-2.10.1-x86_64-linux-gnu/   MiniZinc 2.10.1
#   ~/.local/bin/minizinc -> .../bin/minizinc                 (symlink)
set -euo pipefail

MZN_VERSION=2.10.1
MZN_BUNDLE="MiniZincIDE-${MZN_VERSION}-x86_64-linux-gnu"
MZN_URL="https://github.com/MiniZinc/MiniZincIDE/releases/download/${MZN_VERSION}/${MZN_BUNDLE}.tgz"
MZN_SHA256=b63dd88491d47b05d0eb0ff4aa1112d1e6f77292c023800b20b98851458ce01c

WRAPPER_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$WRAPPER_DIR/.." && pwd)"
SOLVER_DIR="$HOME/.minizinc/solvers"
OPT_DIR="$HOME/.local/opt"
BIN_DIR="$HOME/.local/bin"
MZN_HOME="$OPT_DIR/$MZN_BUNDLE"
MZN_LINK="$BIN_DIR/minizinc"

skip_minizinc=0
uninstall=0
for arg in "$@"; do
  case "$arg" in
    --skip-minizinc) skip_minizinc=1 ;;
    --uninstall) uninstall=1 ;;
    -h|--help) sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "install.sh: unknown option '$arg'" >&2; exit 2 ;;
  esac
done

say() { echo "install.sh: $*"; }

if [ "$uninstall" = 1 ]; then
  rm -f "$SOLVER_DIR/leanfzn.msc" && say "removed $SOLVER_DIR/leanfzn.msc"
  if [ -L "$MZN_LINK" ] && [ "$(readlink "$MZN_LINK")" = "$MZN_HOME/bin/minizinc" ]; then
    rm -f "$MZN_LINK" && say "removed $MZN_LINK (MiniZinc itself stays in $MZN_HOME)"
  fi
  exit 0
fi

# 1. The solver binary.
say "updating leanfzn (lake build leanfzn)"
(cd "$REPO_DIR" && lake build leanfzn)

# 2. MiniZinc 2.10.1, the version LeanFzn's FlatZinc semantics are pinned to.
current_version() { "$1" --version 2>/dev/null | sed -n 's/.*version \([0-9.]*\).*/\1/p' | head -1; }
if [ "$skip_minizinc" = 0 ]; then
  have=""
  command -v minizinc >/dev/null && have="$(current_version minizinc)"
  if [ "$have" = "$MZN_VERSION" ]; then
    say "minizinc $MZN_VERSION already on PATH ($(command -v minizinc))"
  else
    if [ ! -x "$MZN_HOME/bin/minizinc" ]; then
      tmp="$(mktemp -d)"
      trap 'rm -rf "$tmp"' EXIT
      say "downloading MiniZinc $MZN_VERSION (about 80 MB)"
      curl -fSL --progress-bar -o "$tmp/mzn.tgz" "$MZN_URL"
      echo "$MZN_SHA256  $tmp/mzn.tgz" | sha256sum -c --quiet - \
        || { say "checksum mismatch for $MZN_URL; not installing"; exit 1; }
      mkdir -p "$OPT_DIR"
      tar xzf "$tmp/mzn.tgz" -C "$OPT_DIR"
      say "installed MiniZinc $MZN_VERSION in $MZN_HOME"
    fi
    mkdir -p "$BIN_DIR"
    if [ -e "$MZN_LINK" ] && ! [ -L "$MZN_LINK" ]; then
      say "$MZN_LINK exists and is not a symlink; leaving it alone."
      say "use $MZN_HOME/bin/minizinc directly, or put $MZN_HOME/bin first on PATH"
    else
      ln -sfn "$MZN_HOME/bin/minizinc" "$MZN_LINK"
      say "linked $MZN_LINK -> $MZN_HOME/bin/minizinc"
      case ":$PATH:" in
        *":$BIN_DIR:"*) ;;
        *) say "add $BIN_DIR to PATH:  export PATH=\"$BIN_DIR:\$PATH\"" ;;
      esac
      hash -r 2>/dev/null || true
      first="$(command -v minizinc || true)"
      if [ -n "$first" ] && [ "$first" != "$MZN_LINK" ]; then
        say "note: '$first' comes before $MZN_LINK on PATH; put $BIN_DIR first"
      fi
    fi
  fi
fi

# 3. Register the solver. MiniZinc reads every .msc in ~/.minizinc/solvers;
#    the copy gets absolute paths so it works from any directory.
mkdir -p "$SOLVER_DIR"
python3 - "$WRAPPER_DIR" "$SOLVER_DIR/leanfzn.msc" <<'EOF'
import json, os, sys
wrapper_dir, target = sys.argv[1], sys.argv[2]
with open(os.path.join(wrapper_dir, "leanfzn.msc")) as f:
    msc = json.load(f)
msc["executable"] = os.path.join(wrapper_dir, msc["executable"])
msc["mznlib"] = os.path.join(wrapper_dir, msc["mznlib"])
with open(target, "w") as f:
    json.dump(msc, f, indent=2)
    f.write("\n")
EOF
chmod +x "$WRAPPER_DIR/fzn-leanfzn"
say "registered solver: $SOLVER_DIR/leanfzn.msc"
say "try:  minizinc --solver leanfzn $WRAPPER_DIR/examples/queens.mzn"

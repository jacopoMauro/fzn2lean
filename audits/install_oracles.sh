#!/usr/bin/env bash
# audits/install_oracles.sh — install the pinned independent oracles.
#
# Usage:
#   bash audits/install_oracles.sh            # install (download if needed)
#   bash audits/install_oracles.sh --check    # verify an existing install only
#   bash audits/install_oracles.sh --print-env
#
# Installs the official MiniZinc 2.10.1 command-line bundle (the release tag
# matching libminizinc commit c3448c48e7f05f13805616cfd1b9e94972eef58c) with
# its bundled Gecode FlatZinc interpreter into a gitignored prefix:
#
#   tmp/oracles/minizinc/bin/minizinc      (MiniZinc to FlatZinc converter)
#   tmp/oracles/minizinc/bin/fzn-gecode    (Gecode 6.4.0 FlatZinc interpreter)
#   tmp/oracles/minizinc/lib/              (bundled Qt + GL runtime)
#   tmp/oracles/minizinc/share/minizinc/   (std library and solver registrations)
#
# The `fzn-gecode` binary in this bundle links the Qt6/GL runtime that the
# bundle ships in `lib/`, and `libEGL.so.1`, `libGL*.so.1/0` are pulled from the
# Ubuntu 24.04 `libglvnd` binary packages because the bundle does not ship
# them.  Both are fetched as pinned `.deb`/`.tgz` files and verified by
# SHA-256, so no root access and no `apt` metadata are required.  Running the
# oracles therefore needs `LD_LIBRARY_PATH=<prefix>/lib` (and `PATH` containing
# `<prefix>/bin`); use `--print-env` to obtain that in shell form.
#
# Anything that does not verify (hash mismatch, unreadable archive, missing
# library, wrong `minizinc --version`, wrong Gecode version) is a hard failure:
# this script never prints a pass for a partial install.
#
# Updating the pin: the MiniZinc release tag and asset are constants below.
# Replace MINIZINC_SHA256 / GLVND_SHA256 with the freshly computed hashes only
# after verifying the release notes and that every oracle runs; record the
# change in the commit message.  Overrides are deliberately not supported: a
# silently different oracle is not the pinned oracle.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The attention prefix is the directory that holds `minizinc/`.  Unlike the
# gate LOG argument it is resolved to an absolute path so relative overrides
# behave the same from any directory.
PREFIX="${LEANFZN_ORACLE_PREFIX:-$ROOT/tmp/oracles}"
case "$PREFIX" in
  /*) ;;
  *) PREFIX="$PWD/$PREFIX" ;;
esac
DOWNLOAD_DIR="$PREFIX/downloads"
MZN_DIR="$PREFIX/minizinc"

MZN_VERSION="2.10.1"
MZN_ASSET="MiniZincIDE-${MZN_VERSION}-x86_64-linux-gnu.tgz"
MZN_URL="https://github.com/MiniZinc/MiniZincIDE/releases/download/${MZN_VERSION}/${MZN_ASSET}"
MZN_TOP="MiniZincIDE-${MZN_VERSION}-x86_64-linux-gnu"
MZN_SHA256="b63dd88491d47b05d0eb0ff4aa1112d1e6f77292c023800b20b98851458ce01c"

GECODE_STRING="Gecode 6.4.0"

# Ubuntu 24.04 (noble) libglvnd binary packages on the main amd64 pool.  The
# bundle's Qt/GL binaries need libEGL.so.1, libGL.so.1, libGLX.so.0 and
# libGLdispatch.so.0, which are not shipped in the bundle.
GLVND_VERSION="1.7.0-1build1"
GLVND_POOL="https://archive.ubuntu.com/ubuntu/pool/main/libg/libglvnd"
# "<package>: <sha256>"
GLVND_PACKAGES=(
  "libgl1 e2b2fadeb883f073b566ad1d7874f6702397514d258473e96152a89d4d502a09"
  "libglx0 aa4953182f30abde90cb5b072e83d7286b557b325769b8686196a7bd396d8795"
  "libglvnd0 33f5e07c74f73c2bfb44086ae0f9e6da52acd6c104d30ffe8fd768d8253d5e82"
  "libegl1 e549f7776216f7bd3b1c216729fb40a97a562e2eb7c563cde632b4931f9a4e57"
)

die() { printf 'install_oracles: FAIL: %s\n' "$*" >&2; exit 1; }
note() { printf 'install_oracles: %s\n' "$*"; }

sha256_of() { sha256sum "$1" | cut -d' ' -f1; }

fetch() {  # fetch URL DEST EXPECTED_SHA256
  local url="$1" dest="$2" sha="$3"
  if [ -f "$dest" ]; then
    local cached
    cached="$(sha256_of "$dest")"
    if [ "$cached" = "$sha" ]; then
      note "cached $(basename "$dest") (sha256 ok)"
      return 0
    fi
    # A stale or corrupt cache is replaced from the pinned URL, never used.
    note "WARNING: $(basename "$dest") has sha256 $cached, expected $sha;" \
         "re-downloading" >&2
  fi
  rm -f "$dest"
  command -v curl >/dev/null 2>&1 || die "curl is required to download $url"
  note "downloading $(basename "$dest")"
  curl -sSL --fail --retry 3 -o "$dest.part" "$url" \
    || die "download failed: $url"
  mv "$dest.part" "$dest"
  local got
  got="$(sha256_of "$dest")"
  [ "$got" = "$sha" ] \
    || die "sha256 mismatch for $(basename "$dest"): got $got want $sha"
}

# The oracle binaries need the bundle runtime libraries.  `minizinc --version`
# works without them, so checking minizinc alone would accept a broken
# `fzn-gecode` installation.
oracle_env() {
  export PATH="$MZN_DIR/bin:$PATH"
  export LD_LIBRARY_PATH="$MZN_DIR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
}

verify() {  # verify the current install; die on any problem
  [ -x "$MZN_DIR/bin/minizinc" ] || die "missing $MZN_DIR/bin/minizinc"
  [ -x "$MZN_DIR/bin/fzn-gecode" ] || die "missing $MZN_DIR/bin/fzn-gecode"
  [ -d "$MZN_DIR/share/minizinc/std" ] \
    || die "missing $MZN_DIR/share/minizinc/std"
  local envlines
  # `ldd` exits 1 for "not a dynamic executable", and an assignment whose
  # command substitution failed is itself a failure for `set -e`.  The
  # diagnostic text is what matters, not ldd's status.
  envlines="$(oracle_env; ldd "$MZN_DIR/bin/minizinc" "$MZN_DIR/bin/fzn-gecode" 2>&1 || true)"
  # `grep -q` returns 1 when nothing matches, so it is only ever used as an
  # `if` condition (an exempt position); never as a bare command.
  local missing_libs
  missing_libs="$(printf '%s\n' "$envlines" | grep 'not found' || true)"
  if [ -n "$missing_libs" ]; then
    printf '%s\n' "$missing_libs" >&2
    die "oracle binaries have unresolved shared libraries"
  fi
  local version
  version="$(oracle_env; minizinc --version 2>&1)"
  case "$version" in
    *"version $MZN_VERSION"*) ;;
    *) die "minizinc --version is not $MZN_VERSION: $version" ;;
  esac
  # fzn-gecode has no --version flag (it exits 1); its banner on `-help`
  # prints " - Version: 6.4.0" under "Gecode FlatZinc interpreter".
  local gecode
  gecode="$(oracle_env; fzn-gecode -help 2>&1 || true)"
  case "$gecode" in
    *"Gecode FlatZinc interpreter"*"Version: ${GECODE_STRING#Gecode }"*) ;;
    *) die "fzn-gecode does not report $GECODE_STRING" ;;
  esac
  local solvers
  solvers="$(oracle_env; minizinc --solvers 2>&1)"
  case "$solvers" in
    *"Gecode 6.4.0"*) ;;
    *) die "minizinc does not register the bundled Gecode 6.4.0 solver" ;;
  esac
  # A trivial solve must produce a solution block, not just a banner.
  # fzn-gecode mmaps its input, so it gets a regular file (not stdin).
  local smoke_dir smoke
  smoke_dir="$(mktemp -d)"
  printf 'var 1..3: x :: output_var;\nconstraint int_le(x,1);\nsolve satisfy;\n' \
    >"$smoke_dir/smoke.fzn"
  smoke="$(oracle_env; fzn-gecode -a "$smoke_dir/smoke.fzn" 2>&1 || true)"
  rm -rf "$smoke_dir"
  case "$smoke" in
    *"x = 1;"*"----------"*) ;;
    *) die "fzn-gecode smoke solve produced no solution: $smoke" ;;
  esac
  note "minizinc $(printf '%s' "$version" | head -1)"
  note "gecode $GECODE_STRING"
}

install_prefix() {
  mkdir -p "$DOWNLOAD_DIR"
  fetch "$MZN_URL" "$DOWNLOAD_DIR/$MZN_ASSET" "$MZN_SHA256"
  local archive="$DOWNLOAD_DIR/$MZN_ASSET"

  # A stale extraction must never be mistaken for the pinned install.
  if [ -e "$MZN_DIR" ]; then
    local stamp="$MZN_DIR/.installed-from"
    if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$MZN_SHA256" ]; then
      die "$MZN_DIR exists but was not installed by this script; remove it"
    fi
  fi
  rm -rf "$MZN_DIR.tmp"
  mkdir -p "$MZN_DIR.tmp/bin" "$MZN_DIR.tmp/share"
  tar xzf "$archive" -C "$MZN_DIR.tmp" --strip-components=1 \
      "$MZN_TOP/bin" "$MZN_TOP/share/minizinc" \
    || die "cannot extract $archive"
  rm -f "$MZN_DIR.tmp/bin/MiniZincIDE" "$MZN_DIR.tmp/bin/findMUS"

  # Runtime libraries: the bundle's Qt stack, plus the glvnd libraries the
  # bundle omits.  Extract the whole bundled lib/ (the Qt stack has many
  # interdependencies), then overlay the pinned glvnd files.
  tar xzf "$archive" -C "$MZN_DIR.tmp" --strip-components=1 \
      "$MZN_TOP/lib" >/dev/null 2>&1 \
    || die "cannot extract $MZN_TOP/lib from $archive"
  local entry pkg sha deb extract
  extract="$DOWNLOAD_DIR/glvnd-extract"
  rm -rf "$extract"
  for entry in "${GLVND_PACKAGES[@]}"; do
    pkg="${entry%% *}"
    sha="${entry##* }"
    deb="$DOWNLOAD_DIR/${pkg}_${GLVND_VERSION}_amd64.deb"
    fetch "$GLVND_POOL/${pkg}_${GLVND_VERSION}_amd64.deb" "$deb" "$sha"
    mkdir -p "$extract"
    dpkg-deb -x "$deb" "$extract" || die "cannot unpack $deb"
  done
  local libdir="$extract/usr/lib/x86_64-linux-gnu"
  for lib in libEGL libGL libGLX libGLdispatch; do
    # Follow the symlinks: a copied symlink pointing at a versioned file that
    # is also copied is fine, but a missing target is not.
    compgen -G "$libdir/$lib.so.*" >/dev/null \
      || die "$libdir has no $lib.so.*"
    cp -a "$libdir"/"$lib".so.* "$MZN_DIR.tmp/lib/" \
      || die "cannot install $lib into the oracle prefix"
  done
  printf '%s\n' "$MZN_SHA256" >"$MZN_DIR.tmp/.installed-from"

  rm -rf "$MZN_DIR"
  mv "$MZN_DIR.tmp" "$MZN_DIR"
}

# --------------------------------------------------------------- interface
mode="install"
case "${1:-}" in
  "") ;;
  --check) mode="check" ;;
  --print-env) mode="print-env" ;;
  -h|--help)
    sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
    exit 0 ;;
  *) die "unknown argument: $1 (see --help)" ;;
esac

# A `case` arm ending in `;;` discards the arm's exit status, so a `die` inside
# one would only set the status via `set -e`, which does not fire for a
# function's internal `exit` in every shell path.  Keep the dispatch explicit.
if [ "$mode" = "print-env" ]; then
  printf 'export PATH="%s/bin:$PATH"\n' "$MZN_DIR"
  printf 'export LD_LIBRARY_PATH="%s/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"\n' \
    "$MZN_DIR"
elif [ "$mode" = "check" ]; then
  verify
  note "install at $MZN_DIR is complete"
elif [ "$mode" = "install" ]; then
  install_prefix
  verify
  note "installed MiniZinc $MZN_VERSION + $GECODE_STRING in $MZN_DIR"
  note "run: bash audits/install_oracles.sh --print-env   # for PATH/LD_LIBRARY_PATH"
else
  die "internal error: unknown mode $mode"
fi

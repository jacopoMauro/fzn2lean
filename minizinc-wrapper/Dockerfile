# syntax=docker/dockerfile:1
#
# MiniZinc 2.10.0 with LeanFzn installed as a solver (and the default one).
# Build from the repository root, which is the build context:
#
#   docker build -f minizinc-wrapper/Dockerfile -t leanfzn-minizinc .
#   docker run --rm -v "$PWD:/work" leanfzn-minizinc model.mzn data.dzn
#
# See minizinc-wrapper/README.md.

ARG UBUNTU=ubuntu:24.04

# ---------------------------------------------------------------------------
# 1. Build leanfzn with the toolchain pinned by lean-toolchain.
FROM ${UBUNTU} AS build
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git \
 && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --no-modify-path --default-toolchain none
WORKDIR /src
# Toolchain first, so it is cached independently of source changes.
COPY lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)"
COPY . .
RUN lake build leanfzn

# ---------------------------------------------------------------------------
# 2. Fetch MiniZinc 2.10.0, the version LeanFzn's FlatZinc semantics are
#    pinned to (specification/). Same bundle and checksum as install.sh.
FROM ${UBUNTU} AS minizinc
ARG MZN_VERSION=2.10.0
ARG MZN_SHA256=1781daef871a52bebc992b21049ed514cfcdf7cc652ce26df8c9fa82aca1a852
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl \
 && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL -o /tmp/mzn.tgz \
      "https://github.com/MiniZinc/MiniZincIDE/releases/download/${MZN_VERSION}/MiniZincIDE-${MZN_VERSION}-bundle-linux-x86_64.tgz" \
 && echo "${MZN_SHA256}  /tmp/mzn.tgz" | sha256sum -c - \
 && mkdir /opt/minizinc \
 && tar xzf /tmp/mzn.tgz -C /opt/minizinc --strip-components=1 \
 && rm /tmp/mzn.tgz \
 # The command-line tools only; drop the IDE.
 && rm -rf /opt/minizinc/MiniZincIDE.sh /opt/minizinc/bin/MiniZincIDE /opt/minizinc/plugins

# ---------------------------------------------------------------------------
# 3. Runtime: MiniZinc + the wrapper + the leanfzn binary.
FROM ${UBUNTU}
RUN apt-get update \
 && apt-get install -y --no-install-recommends python3 tini \
 && rm -rf /var/lib/apt/lists/*
COPY --from=minizinc /opt/minizinc /opt/minizinc
# Same layout as the repository, so the wrapper finds the binary at
# ../.lake/build/bin/leanfzn without any configuration.
COPY --from=build /src/.lake/build/bin/leanfzn /opt/leanfzn/.lake/build/bin/leanfzn
COPY minizinc-wrapper /opt/leanfzn/minizinc-wrapper
ENV PATH=/opt/minizinc/bin:$PATH

# Register the solver in MiniZinc's own solver directory (absolute paths:
# MiniZinc 2.10.0 does not resolve a relative "executable") and make it the
# default solver, so `minizinc model.mzn` runs LeanFzn.
RUN python3 - <<'EOF'
import json
w = "/opt/leanfzn/minizinc-wrapper"
share = "/opt/minizinc/share/minizinc"
msc = json.load(open(f"{w}/leanfzn.msc"))
msc["executable"] = f"{w}/{msc['executable']}"
msc["mznlib"] = f"{w}/{msc['mznlib']}"
json.dump(msc, open(f"{share}/solvers/leanfzn.msc", "w"), indent=2)
prefs = json.load(open(f"{share}/Preferences.json"))
prefs["tagDefaults"] = [["", msc["id"]]]
json.dump(prefs, open(f"{share}/Preferences.json", "w"), indent=2)
EOF

# Fail the build if the installed solver does not work.
RUN /opt/leanfzn/minizinc-wrapper/test.sh \
 && minizinc /opt/leanfzn/minizinc-wrapper/examples/packing.mzn | grep -q 'value = 51$'

WORKDIR /work
ENTRYPOINT ["/usr/bin/tini", "--", "minizinc"]
CMD ["--solvers"]

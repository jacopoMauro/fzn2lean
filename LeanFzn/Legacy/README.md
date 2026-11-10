# Legacy list-based solver

This directory preserves the old list-based search implementations, exclusive
propagation machinery, option drivers and Core-to-kernel fallback adapters.
They are available for historical proofs and explicit development comparisons.
They are not reachable from the production CLI.

Lean declaration namespaces and certified theorem statements are preserved.
Imports now explicitly use `LeanFzn.Legacy...`. Shared domains, constraint
semantics, compiler proofs and the generic optimizer remain outside this folder.
Some shared reference definitions still support those proof foundations; moving
this layer is not a claim that every historical definition has been removed
from shared modules.

Build explicitly with `lake build LeanFzn.Legacy`. Do not add public Core
imports of this directory; the boundary audit rejects them.

Historical regression tests and diagnostic tools mirror this layer under
`Tests/Legacy/` and build with `lake build Tests.Legacy`. Current Core tests
remain outside that directory and cannot import these historical APIs.

As of the 2026-11-10 working-tree review, shared representation/configuration
changes also update Legacy adapters and tests. These edits are uncommitted
relative to `0246b07`. The current 555-module boundary audit confirms public
Core/CLI independence from Legacy; the historical native suites were not rerun
in this review. See [Tests/README.md](../../Tests/README.md) for validation.

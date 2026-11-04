/-
Purpose: Explicit opt-in umbrella for the preserved list-based solver and its old Core fallback adapters.
Dependencies: Legacy search and integration, with unchanged declaration namespaces.
DAG: shared foundations -> Legacy; the production CLI must never import this layer.
-/
import LeanFzn.Legacy.Integration
import LeanFzn.Legacy.Solver.UIP
import LeanFzn.Legacy.Solver.Chronological
import LeanFzn.Legacy.Solver.Reference

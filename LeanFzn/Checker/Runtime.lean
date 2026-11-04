/-
Purpose: Import executable checker APIs without the downstream correctness modules.
Dependencies: Runtime solution parsing/stores, full checking, front door and objective lookup.
DAG: Parser + Semantics -> Checker.Runtime -> Checker.Proofs / CLI consumers.
-/
import LeanFzn.Checker.Runtime.Solution
import LeanFzn.Checker.Runtime.Globals
import LeanFzn.Checker.Runtime.Check
import LeanFzn.Checker.Runtime.Objective

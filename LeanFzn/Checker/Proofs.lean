/-
Purpose: Import the checker correctness and equivalence theorem layers.
Dependencies: Each proof module imports its runtime definitions and predecessor proofs.
DAG: Checker.Runtime -> Checker.Proofs -> full Checker compatibility API.
-/
import LeanFzn.Checker.Proofs.Solution
import LeanFzn.Checker.Proofs.Globals
import LeanFzn.Checker.Proofs.Check
import LeanFzn.Checker.Proofs.Objective

/- Public Core-only source solving and optimization; no Legacy dependency. -/
import LeanFzn.Integration.Public
-- Build the reporting correctness/streaming proofs with the component library.
-- Runtime entry points import Report.Runtime directly and do not depend on them.
import LeanFzn.Integration.Report.Proofs
import LeanFzn.Integration.Report.T8

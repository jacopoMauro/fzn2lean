/-
Purpose: Convert common search configuration to kernel-specific heuristic options.
Dependencies: LeanFzn.Integration.Config.Types, LeanFzn.Integration.LcgHeur
DAG: Common configuration -> parsing / engine adapters.
-/
import LeanFzn.Integration.Config.Types
import LeanFzn.Legacy.Integration.Kernel.Heur

namespace LeanFzn.Integration

/-- The kernel-level heuristic encoding of an implemented configuration.
    `--var=obj` is exactly the legacy `objPrio` toggle. -/
def SearchConfig.toHeurOpts (c : SearchConfig) : LcgHeur.HeurOpts :=
  { objPrio := c.objPrio || c.var == .obj
    objBias := c.objBias
    actBump := c.actBump }

/-- The default configuration is the unchanged public route. -/
theorem SearchConfig.toHeurOpts_default :
    (default : SearchConfig).toHeurOpts = (default : LcgHeur.HeurOpts) := rfl


end LeanFzn.Integration

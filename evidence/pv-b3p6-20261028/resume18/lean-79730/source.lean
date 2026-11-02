import PV_B3P_RunJoinInterface557227
import PV_B3P_SourceCone557227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
/-- Checks the exact original runjoin consumer, with no success/canonicality
hypotheses. The native wrapper residual is still explicitly an argument; this
is NOT a no-new-hypotheses theorem at the deployed dictionary. -/
theorem runjoin_consumer_residual557 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (wrapper : DeployedWrapper557 base ops)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
      (PV_B3P_Install227.Types base) ops self point =
    @R1Z.PV_RunJoin_OracleBridge38.withTerminal (PV_B3P_Install227.Types base) ops
      (transported_reference base) self point :=
  @R1Z.PV_RunJoin_OracleBridge38.selected_callback (PV_B3P_Install227.Types base) ops
    (transported_reference base) self point
    (selected_callback_residual557 base ops wrapper self point)

#print axioms runjoin_consumer_residual557
end
end PV_B3P_Closure557227

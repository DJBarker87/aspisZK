import PV_B3P_Resume2Axioms
import PV_B3P_Resume2CombinedAudit
namespace PV_B3P_Resume2FocusedClosure
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

theorem selected133 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Resume2CombinedAudit.Types base)) :
    @ExternalFuns.op133 (PV_B3P_Resume2CombinedAudit.Types base)
      (PV_B3P_Resume2CombinedAudit.selected base ops) =
      .ok (.Ok PV_B3P_Install133.value) :=
  PV_B3P_Resume2CombinedAudit.source133 base ops

#print axioms selected133
#print axioms PV_B3P_Resume2CombinedAudit.source226
#print axioms PV_B3P_Resume2CombinedAudit.value226
#print axioms PV_B3P_Closure226.complete_result
#print axioms PV_B3P_Closure226.value
#print axioms PV_B3P_Closure226.nonvacuity
#print axioms PV_B3P_MaskStep132.write_retained
end
end PV_B3P_Resume2FocusedClosure

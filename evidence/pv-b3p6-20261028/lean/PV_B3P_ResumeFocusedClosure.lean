import PV_B3P_ResumeCombinedAudit
import PV_B3P_ResumeAxioms
namespace PV_B3P_ResumeFocusedClosure
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section
-- Focused selected-carrier closure. No privacy endpoint or V243 closure is asserted.
theorem selected133 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_ResumeCombinedAudit.Types base)) :
    @ExternalFuns.op133 (PV_B3P_ResumeCombinedAudit.Types base)
      (PV_B3P_ResumeCombinedAudit.selected base ops) =
      .ok (.Ok PV_B3P_Install133.value) :=
  PV_B3P_ResumeCombinedAudit.source133 base ops
#print axioms selected133
#print axioms PV_B3P_Closure133.row_law
#print axioms PV_B3P_ResumeCombinedAudit.source226
#print axioms PV_B3P_SerializerBridge226.installed_value_of_cells
end
end PV_B3P_ResumeFocusedClosure

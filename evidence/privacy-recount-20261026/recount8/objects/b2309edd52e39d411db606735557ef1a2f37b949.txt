import PV_B3P_Resume3Axioms
import PV_B3P_Resume3CombinedAudit
namespace PV_B3P_Resume3FocusedClosure
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

-- Focused closure of the newly completed V228 row. V241 remains open.
theorem ordered_values :
    PV_B3P_Install132.value.val.map (fun x => (x.row.val,x.column.val)) =
      PV_B3P_MaskModel132.cells := PV_B3P_Install132.value_law

theorem selected132 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op132 base (PV_B3P_Resume3CombinedAudit.selected base ops) =
      .ok (.Ok PV_B3P_Install132.value) := PV_B3P_Resume3CombinedAudit.source132 base ops

#print axioms ordered_values
#print axioms selected132
#print axioms PV_B3P_Install132.reference
#print axioms PV_B3P_Install132.nonvacuity
#print axioms PV_B3P_PrefixComplete224.complete_result
#print axioms PV_B3P_HelperComplete224.complete_result
end
end PV_B3P_Resume3FocusedClosure

import PV_B3P_Install133
import PV_B3P_Install226V3
namespace PV_B3P_InstallCommutation
open ProverRwFull
set_option autoImplicit false
noncomputable section

-- Disjoint callback replacement commutes in the original full carrier.
-- This is a reference-installation fact and supplies no native association.
theorem commute (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base)) :
    PV_B3P_Install133.selected (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) =
    PV_B3P_Install226V3.selected base
      (PV_B3P_Install133.selected (PV_B3P_Install226V3.Types base) ops) := rfl

#print axioms commute
end
end PV_B3P_InstallCommutation

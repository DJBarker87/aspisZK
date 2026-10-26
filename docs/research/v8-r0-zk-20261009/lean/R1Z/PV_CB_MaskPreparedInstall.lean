import R1Z.PV_CB_MaskRootEq
import R1Z.PV_CB_Op118Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskPreparedInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Prepared reference selection; current shipped-source association remains an obligation. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op117 := PV_CB_OwnedMask.owned.mask}
theorem prepared_reference (ops : ExternalFuns)
    (a : Array aspis_core.field.QM31 16#usize)
    (b : Array aspis_core.field.QM31 10#usize) (g : aspis_core.field.QM31)
    (p : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op117 a b g p =
      PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value a b g p :=
  PV_CB_MaskRootEq.reference a b g p
#print axioms prepared_reference
end R1Z.PV_CB_MaskPreparedInstall

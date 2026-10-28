import R1Z.PV_CB_Op105Funs
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op105Exact
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op105 := PV_CB_ShippedOp105.m_inv}
/-- The emitted power loop remains symbolic; no canonicality or totality assumption is added. -/
theorem op105_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (selected ops).op105 x =
      PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv x := rfl
#print axioms op105_source
end R1Z.PV_CB_Op105Exact

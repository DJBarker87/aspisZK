import R1Z.PV_Join_InvSource
import R1Z.PV_Join_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current105
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op105 x = (PV_CB_Op105Exact.selected ops).op105 x := by
  calc
    (ProverRwP6BodyStore.selected ops).op105 x = PV_Join_InvLoop.R.inv x :=
      PV_Join_Field.op105_source ops x
    _ = PV_Join_InvLoop.S.inv x := (PV_Join_InvSource.inverse x).symm
    _ = (PV_CB_Op105Exact.selected ops).op105 x :=
      (PV_CB_Op105Exact.op105_source ops x).symm

theorem op105_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op105 x =
      PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv x :=
  (selected_bridge ops x).trans (PV_CB_Op105Exact.op105_source ops x)
#print axioms selected_bridge
#print axioms op105_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Current105

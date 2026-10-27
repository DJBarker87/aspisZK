import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op111Source
import R1Z.PV_CB_Op118Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_State
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op111_source (ops : ExternalFuns) :
    (selected ops).op111 = .ok PV_CB_ShippedOp111.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT := by
  exact PV_CB_Op111Source.op111_source ops
#print axioms op111_source
theorem op118_source (ops : ExternalFuns) (x : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op118 x =
      ProverRwSuccessPointsSource.state_only_prefix.r0.statement_points x := by
  exact PV_CB_Op118Source.op118_source ops x
#print axioms op118_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_State

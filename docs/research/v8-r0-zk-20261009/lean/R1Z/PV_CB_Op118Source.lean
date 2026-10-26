import R1Z.PV_CB_State
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op118Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op118_source (ops : ExternalFuns) (x : Array aspis_core.field.QM31 10#usize) :
    (PV_CB_State.selected ops).op118 x =
      ProverRwSuccessPointsSource.state_only_prefix.r0.statement_points x := rfl
#print axioms op118_source
end R1Z.PV_CB_Op118Source

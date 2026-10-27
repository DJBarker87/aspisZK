import R1Z.PV_CB_Op223CellSupport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223LimbSupport
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op223CellSupport
variable [ExternalTypes]
abbrev Trace := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
abbrev Limb := aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1

theorem limb (ops : ExternalFuns) (f : Compressor) (trace : Trace) (value : Limb) :
    @host_semantic.copy_tuple_limb _ {ops with op223 := f} trace value =
    @host_semantic.copy_tuple_limb _ ops trace value := by
  rfl
#print axioms limb
end R1Z.PV_CB_Op223LimbSupport

import R1Z.PV_CB_Op223LimbSupport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223TupleSupport
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op223CellSupport
variable [ExternalTypes]
abbrev Trace := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
abbrev Tuple := aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1

theorem tuple (ops : ExternalFuns) (f : Compressor) (trace : Trace) (value : Tuple) :
    @host_semantic.copy_tuple_values _ {ops with op223 := f} trace value =
    @host_semantic.copy_tuple_values _ ops trace value := by
  simp only [host_semantic.copy_tuple_values,PV_CB_Op223LimbSupport.limb]
#print axioms tuple
end R1Z.PV_CB_Op223TupleSupport

import PV_B3_FieldScalar
namespace PV_B3_PreparedComponent
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
 theorem source (left : Array U32 3#usize) (x : New.C) :
    map toC (PV_B3_Copy_117.host_arithmetic.prepared_component_mul left x) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (left,toC x) := by
  simp only [PV_B3_Copy_117.host_arithmetic.prepared_component_mul,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    PV_B3_FieldScalar.add,PV_B3_FieldScalar.sub,PV_B3_FieldScalar.mul,map_bind,map_ok,toC]
#print axioms source
end PV_B3_PreparedComponent

import PV_B3_FieldScalar
namespace PV_B3_HostMulR
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
 theorem source (x : New.C) :
    map toC (PV_B3_Copy_117.host_arithmetic.cm31_mul_r x) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r (toC x) := by
  simp only [PV_B3_Copy_117.host_arithmetic.cm31_mul_r,
    PV_B3_Copy_117.aspis_core.field.CM31.new,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,
    PV_B3_FieldScalar.add,PV_B3_FieldScalar.sub,PV_B3_FieldScalar.double,map_bind,map_ok,toC]
#print axioms source
end PV_B3_HostMulR

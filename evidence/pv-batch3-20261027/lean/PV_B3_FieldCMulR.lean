import PV_B3_FieldScalar
namespace PV_B3_FieldCMulR
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false

theorem source (a : New.C) :
    map toC (PV_B3_Copy_117.aspis_core.field.mul_by_r a) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r (toC a) := by
  simp only [PV_B3_Copy_117.aspis_core.field.mul_by_r,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,
    PV_B3_FieldScalar.add,PV_B3_FieldScalar.sub,PV_B3_FieldScalar.mul,
    PV_B3_FieldScalar.double,PV_B3_FieldScalar.neg,map_bind,map_ok,toC]
#print axioms source
end PV_B3_FieldCMulR

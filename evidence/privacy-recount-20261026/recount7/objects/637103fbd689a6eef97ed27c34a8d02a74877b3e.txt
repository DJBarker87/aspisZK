import PV_B3_FieldReduce
namespace PV_B3_FieldCMul
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false

theorem source (a b : New.C) :
    map toC (PV_B3_Copy_117.aspis_core.field.CM31.mul a b) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul (toC a) (toC b) := by
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.mul,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul,
    PV_B3_FieldReduce.source,PV_B3_FieldScalar.p,PV_B3_FieldScalar.add,PV_B3_FieldScalar.sub,PV_B3_FieldScalar.mul,
    PV_B3_FieldScalar.double,PV_B3_FieldScalar.neg,map_bind,map_ok,toC]
#print axioms source
end PV_B3_FieldCMul

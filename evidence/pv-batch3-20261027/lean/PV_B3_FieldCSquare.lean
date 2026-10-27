import PV_B3_FieldReduce
namespace PV_B3_FieldCSquare
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false

theorem source (a : New.C) :
    map toC (PV_B3_Copy_117.aspis_core.field.CM31.square a) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square (toC a) := by
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.square,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square,
    PV_B3_FieldReduce.source,PV_B3_FieldScalar.p,PV_B3_FieldScalar.add,PV_B3_FieldScalar.sub,PV_B3_FieldScalar.mul,
    PV_B3_FieldScalar.double,PV_B3_FieldScalar.neg,map_bind,map_ok,toC]
#print axioms source
end PV_B3_FieldCSquare

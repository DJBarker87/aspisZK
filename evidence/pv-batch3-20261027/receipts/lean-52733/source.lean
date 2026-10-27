import PV_B3_FieldCAdd
namespace PV_B3_FieldCDouble
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false

theorem source (a : New.C) :
    map toC (PV_B3_Copy_117.aspis_core.field.CM31.double a) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.double (toC a) := by
  exact PV_B3_FieldCAdd.source a a

#print axioms source
end PV_B3_FieldCDouble

import PV_B3_FieldScalar
namespace PV_B3_FieldCAdd
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
local notation "N" => PV_B3_Copy_117.aspis_core.field.CM31.add
local notation "O" => R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add

theorem source (a b : New.C) : map toC (N a b) = O (toC a) (toC b) := by
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.add,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add,
    PV_B3_FieldScalar.add, map_bind, map_ok, toC]

#print axioms source
end PV_B3_FieldCAdd

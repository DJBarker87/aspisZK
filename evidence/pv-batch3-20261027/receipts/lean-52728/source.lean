import PV_B3_FieldScalar
namespace PV_B3_FieldReduce
open Aeneas Aeneas.Std
set_option autoImplicit false
 theorem source (x : U64) :
    PV_B3_Copy_117.aspis_core.field.M31.reduce_u64 x =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64 x := by
  with_unfolding_all rfl
#print axioms source
end PV_B3_FieldReduce

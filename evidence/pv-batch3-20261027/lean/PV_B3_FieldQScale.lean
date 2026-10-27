import PV_B3_FieldBind
import PV_B3_FieldCScale
namespace PV_B3_FieldQScale
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_FieldBind
set_option autoImplicit false
 theorem source (a : New.Q) (b : U32) :
    map toQ (PV_B3_Copy_117.aspis_core.field.QM31.mul_m31 a b) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 (toQ a) b := by
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.mul_m31,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31,toQ,
    ← PV_B3_FieldCScale.source,bind_map,map_bind,map_ok]
#print axioms source
end PV_B3_FieldQScale

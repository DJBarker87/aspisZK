import PV_B3_FieldBind
import PV_B3_FieldCAdd
import PV_B3_FieldCMul
import PV_B3_FieldCMulR
import PV_B3_FieldCDouble
import PV_B3_FieldCSquare
namespace PV_B3_FieldQSquare
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_FieldBind
set_option autoImplicit false
 theorem source (a : New.Q) :
    map toQ (PV_B3_Copy_117.aspis_core.field.QM31.square a) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square (toQ a) := by
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.square,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square,toQ,
    ← PV_B3_FieldCAdd.source,    ← PV_B3_FieldCMul.source,    ← PV_B3_FieldCMulR.source,    ← PV_B3_FieldCDouble.source,    ← PV_B3_FieldCSquare.source,bind_map,map_bind,map_ok]
#print axioms source
end PV_B3_FieldQSquare

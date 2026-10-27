import PV_B3_FieldBind
import PV_B3_FieldCAdd
import PV_B3_FieldCSub
import PV_B3_FieldCMul
import PV_B3_FieldCMulR
namespace PV_B3_FieldQMul
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_FieldBind
set_option autoImplicit false
 theorem source (a b : New.Q) :
    map toQ (PV_B3_Copy_117.aspis_core.field.QM31.mul a b) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul (toQ a) (toQ b) := by
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.mul,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul,toQ,
    ← PV_B3_FieldCAdd.source,    ← PV_B3_FieldCSub.source,    ← PV_B3_FieldCMul.source,    ← PV_B3_FieldCMulR.source,bind_map,map_bind,map_ok]
#print axioms source
end PV_B3_FieldQMul

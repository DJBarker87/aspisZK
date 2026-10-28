import PV_B3_FieldBind
import PV_B3_FieldCAdd
namespace PV_B3_FieldQAdd
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_FieldBind
set_option autoImplicit false
 theorem source (a b : New.Q) :
    map toQ (PV_B3_Copy_117.aspis_core.field.QM31.add a b) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add (toQ a) (toQ b) := by
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.add,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add,toQ,
    ← PV_B3_FieldCAdd.source,bind_map,map_bind,map_ok]
#print axioms source
end PV_B3_FieldQAdd

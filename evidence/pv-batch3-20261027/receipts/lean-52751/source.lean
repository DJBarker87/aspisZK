import PV_B3_PreparedCarrier
import PV_B3_PrepareComponent
import PV_B3_FieldCAdd
import PV_B3_FieldBind
namespace PV_B3_PreparedNew
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_PreparedCarrier PV_B3_FieldBind
set_option autoImplicit false
 theorem source (x : New.Q) :
    map toP (PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.new x) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new (toQ x) := by
  simp only [PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.new,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new,
    toQ,← PV_B3_PrepareComponent.source,← PV_B3_FieldCAdd.source,bind_map,map_bind,map_ok,toP]
#print axioms source
end PV_B3_PreparedNew

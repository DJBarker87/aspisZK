import PV_B3_PreparedCarrier
import PV_B3_PreparedComponent
import PV_B3_HostMulR
import PV_B3_FieldCAdd
import PV_B3_FieldCSub
import PV_B3_FieldBind
namespace PV_B3_PreparedMul
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_PreparedCarrier PV_B3_FieldBind
set_option autoImplicit false
 theorem source (p : NewP) (x : New.Q) :
    map toQ (PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.mul p x) =
      R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul (toP p) (toQ x) := by
  simp only [PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.mul,
    R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul,
    toQ,toP,← PV_B3_PreparedComponent.source,← PV_B3_FieldCAdd.source,
    ← PV_B3_FieldCSub.source,← PV_B3_HostMulR.source,bind_map,map_bind,map_ok]
#print axioms source
end PV_B3_PreparedMul

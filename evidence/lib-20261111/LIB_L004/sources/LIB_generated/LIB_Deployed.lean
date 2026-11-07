import LIB_Env
import NHJ_DeployedIds
set_option autoImplicit false
noncomputable section
namespace LIB_Deployed
open Aeneas Aeneas.Std
/-- The SAME two release identifiers as CLOSED TX2:220 and TX2:225.
`devnet` selects the two already pinned release images. -/
def ids (devnet : Bool) : RSL.DeployedIds :=
  ⟨LIB_Carriers.b32 (NHJ_IdPacket.pool devnet),
   LIB_Carriers.b32 (NHJ_IdPacket.registry devnet)⟩
def deployed : RSL.DeployedIds := ids false
def devnet : RSL.DeployedIds := ids true
theorem pool_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (isDevnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (NHJ_DeployedIds.configuration missing isDevnet indexError reservation).adapter.op45 =
      .ok (LIB_Env.nativeKey (ids isDevnet).pool) := by
  have back : LIB_Env.nativeKey (LIB_Carriers.b32 (NHJ_IdPacket.pool isDevnet)) =
      NHJ_IdPacket.pool isDevnet := by
    apply LIB_Carriers.b32_injective
    exact LIB_Env.key_roundtrip _
  change _ = .ok (LIB_Env.nativeKey (LIB_Carriers.b32 (NHJ_IdPacket.pool isDevnet)))
  rw [back]
  exact NHJ_DeployedIds.pool_actual missing isDevnet indexError reservation
theorem registry_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (isDevnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (NHJ_DeployedIds.configuration missing isDevnet indexError reservation).adapter.op46 =
      .ok (LIB_Env.nativeKey (ids isDevnet).registry) := by
  have back : LIB_Env.nativeKey (LIB_Carriers.b32 (NHJ_IdPacket.registry isDevnet)) =
      NHJ_IdPacket.registry isDevnet := by
    apply LIB_Carriers.b32_injective
    exact LIB_Env.key_roundtrip _
  change _ = .ok (LIB_Env.nativeKey (LIB_Carriers.b32 (NHJ_IdPacket.registry isDevnet)))
  rw [back]
  exact NHJ_DeployedIds.registry_actual missing isDevnet indexError reservation
#print axioms pool_actual
#print axioms registry_actual
end LIB_Deployed

import NHJ_DeployedIds
import NND_Carrier
import PCM_ResultTotal
import RSL_Pool
set_option autoImplicit false
namespace PCM_Inst_Deployed
open Aeneas Aeneas.Std

def ids (devnet : Bool) : RSL.DeployedIds :=
  ⟨NND_Carrier.key (NHJ_IdPacket.pool devnet),NND_Carrier.key (NHJ_IdPacket.registry devnet)⟩
def deployed : RSL.DeployedIds := ids false

theorem pool_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    PCM_ResultTotal.mapOuter NND_Carrier.key
      (NHJ_DeployedIds.configuration missing devnet indexError reservation).adapter.op45 =
      Result.ok (ids devnet).pool := by
  rw [NHJ_DeployedIds.pool_actual]
  rfl

theorem registry_actual {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    PCM_ResultTotal.mapOuter NND_Carrier.key
      (NHJ_DeployedIds.configuration missing devnet indexError reservation).adapter.op46 =
      Result.ok (ids devnet).registry := by
  rw [NHJ_DeployedIds.registry_actual]
  rfl

theorem pool_type : (RSL.DeployedIds.pool : RSL.DeployedIds → RSL.B32) = RSL.DeployedIds.pool := rfl
theorem registry_type : (RSL.DeployedIds.registry : RSL.DeployedIds → RSL.B32) = RSL.DeployedIds.registry := rfl
#print axioms pool_actual
#print axioms registry_actual
#print axioms pool_type
#print axioms registry_type
end PCM_Inst_Deployed

import NMS_Native242Children
import NMS_242AtFold
import NMS_RSLPoolCarriers
import NMS_ClonePackets
set_option autoImplicit false
noncomputable section
namespace NMS_242Parameterized
open Aeneas Aeneas.Std AdapterRw
abbrev Auth := NMS_Effect242.AuthCall RSL.Spec
/-- Pullback of the complete corrected233 target at SAME original arguments.
Every Box payload and every ProgramError payload is retained in the map.
Private allocation addresses are excluded only as already permitted by(bl). -/
def reference233 (L : RSL.PoolLib) (D : RSL.DeployedIds) : Auth :=
 fun program accounts pool lane slot env observation =>
 NMS_CloneRef233.Ref L D (NMS_RSLPoolCarriers.args233 program accounts pool lane slot) env
  (NMS_Interpreted.mapObs (NMS_RSLError.reply NMS_RSLPoolCarriers.authenticated) observation)

/-- Relational form of the full OPEN233 packet, quantifying every actual
execution observation (including allocator stops), not only one returned run. -/
def RowSpec233 (L : RSL.PoolLib) (D : RSL.DeployedIds) (authenticate : Auth) : Prop :=
 ∀ program accounts pool lane slot,
 NMS_RSLRefine.Refines (authenticate program accounts pool lane slot)
  (reference233 L D program accounts pool lane slot)

/-- Full typed emitted-source reference. Compared with RSL242 this retains
native carriers and the explicit general-error clone stops. Its CLOSED
children are fixed by NMS_Native242Children, not arbitrary Ops fields.
The final RSL242 carrier equivalence is still a separate proof obligation. -/
def Ref (devnet : Bool) (L : RSL.PoolLib) (D : RSL.DeployedIds) :=
 NMS_Native242Children.meaning devnet (reference233 L D)

/-- Complete observation fold for the fresh242 body with its CLOSED child
interpretations fixed. Only the full OPEN233 packet is parameterized here.
No native/canonical242 credit is claimed before the remaining carrier gate. -/
theorem fold (devnet : Bool) (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (authenticate : Auth) (packet : RowSpec233 L D authenticate)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_RSLRefine.Refines
  (NMS_Native242Children.meaning devnet authenticate program accounts data slot)
  (Ref devnet L D program accounts data slot) :=
 NMS_242AtFold.direct _ _ _ program accounts
  (fun pool lane current => packet program accounts pool lane current) data slot
#print axioms fold
end NMS_242Parameterized

import NMS_R2N_Native242Children
import NMS_R2AtFold242
import NMS_R2N_RSLPoolCarriers
set_option autoImplicit false
noncomputable section
namespace NMS_R2Parameterized242
open Aeneas Aeneas.Std AdapterRw
abbrev Auth := NMS_Effect242.AuthCall RSL.Spec
/-- Pullback of the complete canonical revision2 RowSpec_233 target at SAME original arguments.
Every Box payload and every ProgramError payload is retained in the map.
Private allocation addresses are excluded only as already permitted by(bl). -/
def reference233 (L : RSL.PoolLib) (D : RSL.DeployedIds) : Auth :=
 fun program accounts pool lane slot env observation =>
 RSL.TX2_233.Ref L D (NMS_R2N_RSLPoolCarriers.args233 program accounts pool lane slot) env
  (NMS_R2N_Interpreted.mapObs (NMS_R2N_RSLError.reply NMS_R2N_RSLPoolCarriers.authenticated) observation)

/-- Relational form of the full OPEN233 packet, quantifying every actual
execution observation (including allocator stops), not only one returned run. -/
def RowSpec233 (L : RSL.PoolLib) (D : RSL.DeployedIds) (authenticate : Auth) : Prop :=
 ∀ program accounts pool lane slot,
 NMS_R2Refine.Refines (authenticate program accounts pool lane slot)
  (reference233 L D program accounts pool lane slot)

/-- Full typed emitted-source reference. This retains native carriers while the233 parameter is canonical revision2; its general-error clone stops are included. Its CLOSED
children are fixed by NMS_R2N_Native242Children, not arbitrary Ops fields.
The final RSL242 carrier equivalence is still a separate proof obligation. -/
def Ref (devnet : Bool) (L : RSL.PoolLib) (D : RSL.DeployedIds) :=
 NMS_R2N_Native242Children.meaning devnet (reference233 L D)

/-- Complete observation fold for the fresh242 body with its CLOSED child
interpretations fixed. Only the full OPEN233 packet is parameterized here.
No native/canonical242 credit is claimed before the remaining carrier gate. -/
theorem fold (devnet : Bool) (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (authenticate : Auth) (packet : RowSpec233 L D authenticate)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_R2Refine.Refines
  (NMS_R2N_Native242Children.meaning devnet authenticate program accounts data slot)
  (Ref devnet L D program accounts data slot) :=
 NMS_R2AtFold242.direct _ _ _ program accounts
  (fun pool lane current => packet program accounts pool lane current) data slot
#print axioms fold
end NMS_R2Parameterized242

import NMX_R2_NativeRoot
import NMX_R2_LaneView
import NMX_R2_CanonicalChildren
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeCanonical
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel NMX_R2_Carrier
/-- Both OPEN children enter as the EXACT canonical full-strength RowSpecs.
The implementation of217 is the total canonical view of the SAME typed native
child; registry maps only the original full argument tuple. No endpoint law. -/
theorem fold (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_CanonicalChildren.Registry)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : RSL.TX2_217.RowSpec_217 (NMX_R2_LaneView.view ln))
 (registryPacket : RSL.TX2_234.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (env : RSL.Env) :
 RSL.TX2_233.Ref (NMX_R2_DecoderLibrary.install L) D
  ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩ env
  (NMX_R2_NativeExecution.run owners alloc failure ln (NMX_R2_CanonicalChildren.registry rn) env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot)) :=
 NMX_R2_NativeRoot.fold owners alloc failure ln (NMX_R2_CanonicalChildren.registry rn) L D
  (NMX_R2_LaneView.raw ln lanePacket)
  (NMX_R2_CanonicalChildren.registry_packet (NMX_R2_DecoderLibrary.install L) D rn registryPacket)
  verifier accounts pool outputLane slot env
#print axioms fold
end NMX_R2_NativeCanonical
end

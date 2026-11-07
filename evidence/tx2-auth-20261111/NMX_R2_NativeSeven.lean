import NMX_R2_NativeProgram
import NMX_R2_SevenSourceFold
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeSeven
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R2_Carrier
/-- The seven-account operational fold reaches the EXACT revised reference at
its complete translated input. The raw217/234 representation variants remain
explicit; this is not yet the universal canonical RowSpec_233 wrapper. -/
theorem fold (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount)
 (shape : accounts.val = [p,m,c,l,r,e,v]) (env : RSL.Env) :
 RSL.TX2_233.Ref (NMX_R2_DecoderLibrary.install L) D
  ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩ env
  (NMX_R2_NativeExecution.run owners alloc failure ln rn env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot)) := by
 have included := NMX_R2_SevenSourceFold.fold owners ln rn L D lanePacket registryPacket
  verifier accounts pool outputLane slot p m c l r e v shape env _
  (NMX_R2_NativeProgram.member owners alloc failure ln rn env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot))
 simpa only [NMX_R2_HeterogeneousPrimitives.map_identity] using included
#print axioms fold
end NMX_R2_NativeSeven
end

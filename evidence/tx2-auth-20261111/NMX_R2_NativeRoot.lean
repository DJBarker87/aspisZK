import NMX_R2_NativeSeven
import NMX_R2_CountReference
import NMX_R2_CountNative
import NMX_R2_SevenList
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeRoot
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel NMX_R2_Carrier
/-- All native-carrier inputs. This operational source fold keeps the exact
canonical Ref, but the canonical all-Args wrapper and emitted-observation
association are separate, explicitly reported obligations. -/
theorem fold (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_R2_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_R2_RawChildren.RowSpec_234 (NMX_R2_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (env : RSL.Env) :
 RSL.TX2_233.Ref (NMX_R2_DecoderLibrary.install L) D
  ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩ env
  (NMX_R2_NativeExecution.run owners alloc failure ln rn env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot)) := by
 by_cases count : accounts.val.length = 7
 · obtain ⟨p,m,c,l,r,e,v,shape⟩ := NMX_R2_SevenList.shape accounts.val count
   exact NMX_R2_NativeSeven.fold owners alloc failure ln rn L D lanePacket registryPacket
    verifier accounts pool outputLane slot p m c l r e v shape env
 · rw [NMX_R2_CountReference.other _ _ _ (by simpa only [List.length_map] using count)]
   rw [NMX_R2_CountNative.source owners alloc failure ln rn verifier accounts pool outputLane slot env count]
   simp only [List.length_map]
   rfl
#print axioms fold
end NMX_R2_NativeRoot
end

import NNH_U64BytesKernel
set_option autoImplicit false
namespace NNH_CheckpointSeeds
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem bytes (m : solana_pubkey.Pubkey) (seq : U64) (b : U8) :
 (NNH_AuthSeeds.checkpoint m seq b).val.map NND_Carrier.bytes=
 [RSL.SEED_CHECKPOINT,(key m).bytes,RSL.u64le (slot seq),[byte b]] := by
 change [NND_Carrier.bytes r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,(key m).bytes,
  NND_Carrier.bytes (Array.to_slice (core.num.U64.to_le_bytes seq)),[byte b]]=_
 rw [NND_Constants.checkpoint_seed,NNH_U64BytesKernel.value]
#print axioms bytes
end NNH_CheckpointSeeds

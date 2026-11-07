import NNH_MPdaSeeds
import NNH_Tx2ModelSlots
set_option autoImplicit false
namespace NNH_AuthSeeds
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

def master (mint : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 3#usize [r1_pool_adapter.PAIR_FOREST_MASTER_SEED,Array.to_slice mint,NNH_MPdaSeeds.one b])
def checkpoint (m : solana_pubkey.Pubkey) (seq : U64) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 4#usize [r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,Array.to_slice m,
  Array.to_slice (core.num.U64.to_le_bytes seq),NNH_MPdaSeeds.one b])
def lane (m : solana_pubkey.Pubkey) (id b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 4#usize [r1_pool_adapter.PAIR_FOREST_LANE_SEED,Array.to_slice m,
  NNH_MPdaSeeds.one id,NNH_MPdaSeeds.one b])

theorem master_bytes (mint : solana_pubkey.Pubkey) (b : U8) :
 (master mint b).val.map bytes=[RSL.SEED_MASTER,(key mint).bytes,[byte b]] := by
 change [bytes r1_pool_adapter.PAIR_FOREST_MASTER_SEED,(key mint).bytes,[byte b]]=_
 rw [NND_Constants.master_seed]

theorem lane_bytes (m : solana_pubkey.Pubkey) (id b : U8) :
 (lane m id b).val.map bytes=[RSL.SEED_LANE,(key m).bytes,[byte id],[byte b]] := by
 change [bytes r1_pool_adapter.PAIR_FOREST_LANE_SEED,(key m).bytes,[byte id],[byte b]]=_
 rw [NND_Constants.lane_seed]
#print axioms master_bytes
#print axioms lane_bytes
end NNH_AuthSeeds

import NMX_Carrier
set_option autoImplicit false
namespace NMX_SeedConstants
open Aeneas Aeneas.Std AdapterRw NMX_Carrier

theorem master : bytes r1_pool_adapter.PAIR_FOREST_MASTER_SEED = RSL.SEED_MASTER := by
 unfold r1_pool_adapter.PAIR_FOREST_MASTER_SEED
 rfl
theorem checkpoint : bytes r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED = RSL.SEED_CHECKPOINT := by
 unfold r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED
 rfl
theorem lane : bytes r1_pool_adapter.PAIR_FOREST_LANE_SEED = RSL.SEED_LANE := by
 unfold r1_pool_adapter.PAIR_FOREST_LANE_SEED
 rfl

theorem key_ref (key : solana_pubkey.Pubkey) : bytes (Array.to_slice key) = (NMX_Carrier.key key).bytes := rfl
#print axioms master
#print axioms checkpoint
#print axioms lane
#print axioms key_ref
end NMX_SeedConstants

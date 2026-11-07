import NMX_R2_SeedConstants
set_option autoImplicit false
namespace NMX_R2_SeedFrames
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier

theorem single (x : U8) : bytes (Array.to_slice (Array.make 1#usize [x])) = [byte x] := rfl

theorem master (mint bump : Slice U8) :
 (Array.to_slice (Array.make 3#usize [r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mint,bump])).val.map bytes =
 [RSL.SEED_MASTER,bytes mint,bytes bump] := by
 change [bytes r1_pool_adapter.PAIR_FOREST_MASTER_SEED,bytes mint,bytes bump] = _
 rw [NMX_R2_SeedConstants.master]

theorem checkpoint (master sequence bump : Slice U8) :
 (Array.to_slice (Array.make 4#usize [r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,master,sequence,bump])).val.map bytes =
 [RSL.SEED_CHECKPOINT,bytes master,bytes sequence,bytes bump] := by
 change [bytes r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,bytes master,bytes sequence,bytes bump] = _
 rw [NMX_R2_SeedConstants.checkpoint]

theorem lane (master laneId bump : Slice U8) :
 (Array.to_slice (Array.make 4#usize [r1_pool_adapter.PAIR_FOREST_LANE_SEED,master,laneId,bump])).val.map bytes =
 [RSL.SEED_LANE,bytes master,bytes laneId,bytes bump] := by
 change [bytes r1_pool_adapter.PAIR_FOREST_LANE_SEED,bytes master,bytes laneId,bytes bump] = _
 rw [NMX_R2_SeedConstants.lane]
#print axioms single
#print axioms master
#print axioms checkpoint
#print axioms lane
end NMX_R2_SeedFrames

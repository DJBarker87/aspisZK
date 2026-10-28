import NDO_JHg_AccountValues
import NDO_JHg_PDAFields
set_option autoImplicit false
namespace AspisR1.JHj_Seeds
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World

def key : solana_pubkey.Pubkey := (e2.snapshot 1 384 384).key

def master : Slice (Slice U8) := (Array.make 3#usize [
  r1_pool_adapter.PAIR_FOREST_MASTER_SEED,
  JHg_AccountValues.master.identity.asset_mint.to_slice,
  (Array.make 1#usize [JHg_AccountValues.master.bump]).to_slice]).to_slice

def checkpoint : Slice (Slice U8) := (Array.make 4#usize [
  r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,key.to_slice,
  (core.num.U64.to_le_bytes JHg_AccountValues.checkpoint.checkpoint_sequence).to_slice,
  (Array.make 1#usize [JHg_AccountValues.checkpoint.bump]).to_slice]).to_slice

def lane : Slice (Slice U8) := (Array.make 4#usize [
  r1_pool_adapter.PAIR_FOREST_LANE_SEED,key.to_slice,
  (Array.make 1#usize [3#u8]).to_slice,
  (Array.make 1#usize [JHg_AccountValues.lane.bump]).to_slice]).to_slice

theorem master_count : master.val.length=3 := rfl
#print axioms master_count
theorem checkpoint_count : checkpoint.val.length=4 := rfl
#print axioms checkpoint_count
theorem lane_count : lane.val.length=4 := rfl
#print axioms lane_count
end AspisR1.JHj_Seeds

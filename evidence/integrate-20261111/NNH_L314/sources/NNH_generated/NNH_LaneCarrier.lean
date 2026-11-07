import NMX_R3_LaneTotal
import NND_LaneCarrier
set_option autoImplicit false
namespace NNH_LaneCarrier
open Aeneas Aeneas.Std AdapterRw
/-- Typed host record at the same reference input; no native observation is
chosen and no length/canonicality precondition is added. -/
def native (a : NCV_Reference.Lane) :
 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
 ⟨a.bump,a.master,a.lane_id,⟨a.next_leaf_index,a.root,a.frontier⟩⟩

theorem byte (x : U8) : NND_Carrier.byte x=NMX_R3_ByteCarrier.byte x := by
 have value : (NND_Carrier.byte x).toNat=(NMX_R3_ByteCarrier.byte x).toNat := by
  rw [NMX_R3_ByteCarrier.byte_value]
  rfl
 have step := congrArg UInt8.ofNat value
 simpa only [UInt8.ofNat_toNat] using step

theorem word (x : U32) : NND_Carrier.word x=NMX_R3_ByteCarrier.word x := by
 have value : (NND_Carrier.word x).toNat=(NMX_R3_ByteCarrier.word x).toNat := by
  rw [NMX_R3_ByteCarrier.word_value]
  rfl
 have step := congrArg UInt32.ofNat value
 simpa only [UInt32.ofNat_toNat] using step

theorem long (x : U64) : NND_Carrier.slot x=NMX_R3_ByteCarrier.long x := by
 have value : (NND_Carrier.slot x).toNat=(NMX_R3_ByteCarrier.long x).toNat := by
  rw [NMX_R3_ByteCarrier.long_value]
  rfl
 have step := congrArg UInt64.ofNat value
 simpa only [UInt64.ofNat_toNat] using step

theorem key (x : Array U8 32#usize) : NND_Carrier.key x=NMX_R3_LaneCarrier.key x := by
 unfold NND_Carrier.key NMX_R3_LaneCarrier.key
 congr 1
 exact List.map_congr_left (fun x _ => byte x)

theorem lane (a : NCV_Reference.Lane) :
 NND_Carrier.lane (native a)=NMX_R3_LaneCarrier.lane a := by
 unfold NND_Carrier.lane native NMX_R3_LaneCarrier.lane NND_Carrier.tree
 simp only [byte,key,long]
 congr 2
 · unfold NND_Carrier.digest
   exact List.map_congr_left (fun x _ => word x)
 · unfold NND_Carrier.frontier NND_Carrier.digest
   apply List.map_congr_left
   intro row _
   exact List.map_congr_left (fun x _ => word x)

#print axioms byte
#print axioms word
#print axioms long
#print axioms key
#print axioms lane
end NNH_LaneCarrier

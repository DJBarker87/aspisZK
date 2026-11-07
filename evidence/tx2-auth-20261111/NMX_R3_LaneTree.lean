import NMX_R3_LaneCounter
import NMX_R3_BoolReject
set_option autoImplicit false
namespace NMX_R3_LaneTree
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] NMX_R3_LaneModels.counter

theorem value (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (bExtent : b.val.length = 768) :
 observe (NMX_R3_LaneCuts.tree b master laneId) =
 ok (NMX_R3_LaneModels.tree (b.val.map byte) (key master) (byte laneId)) := by
 let t := Slice.drop b 80#usize
 have tExtent : t.val.length = 688 := by
  simp only [t, Slice.drop, List.length_drop, NMX_R3_Indices.v80, bExtent]
 have tImage : t.val.map byte = (b.val.map byte).drop LANE_HEADER_BYTES := by
  simp only [t, Slice.drop, NMX_R3_Indices.v80, List.map_drop, LANE_HEADER_BYTES]
 have tailCall := NMX_R3_Slices.drop_total b 80#usize (by rw [NMX_R3_Indices.v80,bExtent]; decide)
 have headCall := NMX_R3_Slices.prefix_total t 4#usize (by rw [NMX_R3_Indices.v4,tExtent]; decide)
 have headImage : (NMX_R3_Slices.window t 0 (4#usize).val).val.map byte = slice (t.val.map byte) 0 4 := by
  simpa only [NMX_R3_Indices.v4] using NMX_R3_Slices.image t 0 4
 have equalCall := NMX_R3_Equality.value (NMX_R3_Slices.window t 0 (4#usize).val)
  (Array.to_slice (Array.make 4#usize [65#u8,83#u8,80#u8,84#u8]))
  (by have := NMX_R3_Slices.length t 0 4 (by omega); rw [NMX_R3_Indices.v4]; omega)
 have magic : (Array.to_slice (Array.make 4#usize [65#u8,83#u8,80#u8,84#u8])).val.map byte = TREE_STATE_MAGIC := rfl
 have read4 := NCV_ZeroStep.read t 4#usize (by rw [NMX_R3_Indices.v4,tExtent]; decide)
 have read5 := NCV_ZeroStep.read t 5#usize (by rw [NMX_R3_Indices.v5,tExtent]; decide)
 have read6 := NCV_ZeroStep.read t 6#usize (by rw [NMX_R3_Indices.v6,tExtent]; decide)
 have read7 := NCV_ZeroStep.read t 7#usize (by rw [NMX_R3_Indices.v7,tExtent]; decide)
 simp only [NMX_R3_Indices.v4] at headCall equalCall headImage
 simp only [NMX_R3_LaneCuts.tree, tailCall, bind_tc_ok, show Slice.drop b 80#usize=t from rfl,
  headCall, lift]
 erw [equalCall]
 simp only [bind_tc_ok, headImage, magic, through_if, read4, read5, read6, read7,
  NMX_R3_Indices.v4, NMX_R3_Indices.v5, NMX_R3_Indices.v6, NMX_R3_Indices.v7,
  NMX_R3_LaneCounter.value b master laneId t bExtent tExtent, returned,
  NMX_R3_LaneCarrier.result, pure_if, NMX_R3_ByteCompare.ne]
 rw [NMX_R3_BoolReject.chain5]
 simp only [NMX_R3_LaneModels.tree, ←tImage, TX2_217.treeHeaderBad,
  NMX_R3_ByteIndex.mapped, TREE_STATE_VERSION, TREE_HASH_VERSION,
  DIGEST_ENCODING_VERSION, bne]
 rfl
#print axioms value
end NMX_R3_LaneTree

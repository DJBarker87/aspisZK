import NMX_R3_LaneMaster
set_option autoImplicit false
namespace NMX_R3_LaneHeader
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] NMX_R3_LaneModels.master

theorem lane_count (x : U8) : (x ≥ 8#u8) ↔ LANE_COUNT ≤ (byte x).toNat := by
 change 8 ≤ x.val ↔ 8 ≤ (byte x).toNat
 rw [byte_value]

theorem value (b : Slice U8) (extent : b.val.length = 768) :
 observe (NMX_R3_LaneCuts.header b) = ok (NMX_R3_LaneModels.header (b.val.map byte)) := by
 have headCall := NMX_R3_Slices.prefix_total b 4#usize (by rw [NMX_R3_Indices.v4,extent]; decide)
 have headImage : (NMX_R3_Slices.window b 0 (4#usize).val).val.map byte = slice (b.val.map byte) 0 4 := by
  simpa only [NMX_R3_Indices.v4] using NMX_R3_Slices.image b 0 4
 have equalCall := NMX_R3_Equality.value (NMX_R3_Slices.window b 0 (4#usize).val)
  (Array.to_slice (Array.make 4#usize [65#u8,83#u8,76#u8,56#u8]))
  (by rw [NMX_R3_Indices.v4]; have := NMX_R3_Slices.length b 0 4 (by omega); omega)
 have magic : (Array.to_slice (Array.make 4#usize [65#u8,83#u8,76#u8,56#u8])).val.map byte = LANE_MAGIC := rfl
 have read4 := NCV_ZeroStep.read b 4#usize (by rw [NMX_R3_Indices.v4,extent]; decide)
 have read5 := NCV_ZeroStep.read b 5#usize (by rw [NMX_R3_Indices.v5,extent]; decide)
 have read6 := NCV_ZeroStep.read b 6#usize (by rw [NMX_R3_Indices.v6,extent]; decide)
 have read7 := NCV_ZeroStep.read b 7#usize (by rw [NMX_R3_Indices.v7,extent]; decide)
 have bindingCall := NMX_R3_Slices.range_total b 8#usize 40#usize
  (by rw [NMX_R3_Indices.v8,NMX_R3_Indices.v40]; decide)
  (by rw [NMX_R3_Indices.v40,extent]; decide)
 have bindingImage : (NMX_R3_Slices.window b (8#usize).val ((40#usize).val-(8#usize).val)).val.map byte =
  slice (b.val.map byte) 8 40 := by
  simpa only [NMX_R3_Indices.v8,NMX_R3_Indices.v40] using NMX_R3_Slices.image b 8 32
 have bindingEqual := NMX_R3_Equality.value
  (NMX_R3_Slices.window b (8#usize).val ((40#usize).val-(8#usize).val)) (Array.to_slice NCV_Reference.BINDING)
  (by change (NMX_R3_Slices.window b 8 32).val.length ≤ 768; rw [NMX_R3_Slices.length b 8 32 (by omega)]; decide)
 have reservedCall := NMX_R3_Slices.range_total b 73#usize 80#usize
  (by rw [NMX_R3_Indices.v73,NMX_R3_Indices.v80]; decide)
  (by rw [NMX_R3_Indices.v80,extent]; decide)
 have reservedImage : (NMX_R3_Slices.window b (73#usize).val ((80#usize).val-(73#usize).val)).val.map byte =
  slice (b.val.map byte) 73 80 := by
  simpa only [NMX_R3_Indices.v73,NMX_R3_Indices.v80] using NMX_R3_Slices.image b 73 7
 have reservedZero := NMX_R3_Zero.value
  (NMX_R3_Slices.window b (73#usize).val ((80#usize).val-(73#usize).val))
  (by change (NMX_R3_Slices.window b 73 7).val.length ≤ 768; rw [NMX_R3_Slices.length b 73 7 (by omega)]; decide)
 simp only [NMX_R3_Indices.v4] at headCall equalCall headImage
 simp only [NMX_R3_LaneCuts.header, headCall, lift, bind_tc_ok]
 erw [equalCall]
 simp only [bind_tc_ok, headImage, magic,
  through_if, read4, read5, read6, read7, NMX_R3_Indices.v4, NMX_R3_Indices.v5,
  NMX_R3_Indices.v6, NMX_R3_Indices.v7, bindingCall, bindingEqual,
  NMX_R3_Slices.array_val, bindingImage, NMX_R3_Constants.binding,
  reservedCall, reservedZero, reservedImage, returned, NMX_R3_LaneCarrier.result,
  NMX_R3_LaneMaster.value b (NCV_ZeroStep.byte b 5) extent, pure_if, NMX_R3_ByteCompare.ne,
  lane_count]
 rw [NMX_R3_BoolReject.as_bool (LANE_COUNT ≤ (byte (NCV_ZeroStep.byte b 5)).toNat)]
 rw [NMX_R3_BoolReject.chain7]
 simp only [NMX_R3_LaneModels.header, TX2_217.headerBad, List.length_map, extent,
  show (768 != LANE_ACCOUNT_BYTES)=false from rfl, Bool.false_or, NMX_R3_ByteIndex.mapped,
  LANE_HEADER_BYTES, LANE_VERSION]
 rw [NMX_R3_BoolReject.any_ne]
 rfl
#print axioms lane_count
#print axioms value
end NMX_R3_LaneHeader

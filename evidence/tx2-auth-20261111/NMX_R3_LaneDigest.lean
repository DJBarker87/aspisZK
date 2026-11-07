import NMX_R3_LaneFrontier
set_option autoImplicit false
namespace NMX_R3_LaneDigest
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] RSL.TX2_217.decodeDigestCanonical NCV_Reference.digest

theorem value (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (t : Slice U8) (next : U64) (bExtent : b.val.length = 768) (tExtent : t.val.length = 688) :
 observe (NMX_R3_LaneCuts.digest b master laneId t next) =
 ok (NMX_R3_LaneModels.digest (b.val.map byte) (key master) (byte laneId)
  (t.val.map byte) (long next)) := by
 obtain ⟨r,call,mapped⟩ := NMX_R3_DigestBridge.value t 16#usize (by omega)
  (by rw [NMX_R3_Indices.v16,tExtent]; decide)
 have same : NMX_R3_LaneTry.option (fun a : Array U32 8#usize => a.val.map word) r =
  TX2_217.decodeDigestCanonical (slice (t.val.map byte) 16 48) := by
  rw [NMX_R3_LaneQuestionCuts.digest_map]
  simpa only [NMX_R3_Indices.v16] using mapped
 rw [NMX_R3_LaneQuestionCuts.digest]
 have joined := NMX_R3_LaneTry.fold (NCV_Reference.digest t 16#usize) r
  (fun a => a.val.map word) (TX2_217.decodeDigestCanonical (slice (t.val.map byte) 16 48))
  (fun root => NMX_R3_LaneCuts.frontier b master laneId t next root)
  (NMX_R3_LaneModels.frontier (b.val.map byte) (key master) (byte laneId) (t.val.map byte) (long next))
  call same (fun root => NMX_R3_LaneFrontier.value b master laneId t next root bExtent tExtent)
 rw [joined]
 unfold NMX_R3_LaneModels.digest
 generalize TX2_217.decodeDigestCanonical (slice (t.val.map byte) 16 48) = model
 cases model <;> rfl

#print axioms value
end NMX_R3_LaneDigest

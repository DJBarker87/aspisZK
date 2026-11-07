import LIBB_ProtocolBytes
import LIBB_C04Partition
set_option autoImplicit false
namespace LIBB_FlattenBytes
open Aeneas Aeneas.Std
/-- Partitioned source slices and flattened protocol bytes contain exactly
the same bytes, without merging or deduplicating requests. -/
theorem flatten (p : Slice (Slice U8)) :
 LIBB_ProtocolBytes.host (AspisV8R19.SqueezeOracleBridge.flatten p) =
 p.val.flatMap (fun s => NNC_ByteCarriers.host s.val) := by
 have h := LIBB_ProtocolBytes.host_native (p.val.flatMap (fun s => s.val))
 change LIBB_ProtocolBytes.host (AspisV8R19.SqueezeOracleBridge.flatten p) = _ at h
 simpa only [NNC_ByteCarriers.host,List.map_flatMap,Function.comp_def] using h

/-- Every node request recovers its exact three original hashv parts. -/
theorem node (left right : Array U8 32#usize) :
 LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
  (AspisV8R19.SqueezeOracleBridge.flatten (AspisR1.MultiproofConePhysicalDigest.parts left right))) =
 NNC_ResumeEvents.parts (AspisR1.MultiproofConePhysicalDigest.parts left right) := by
 rw [flatten]
 simpa only [AspisR1.MultiproofConePhysicalDigest.parts,NNC_ResumeEvents.parts,
   List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
   NNC_ByteCarriers.host] using
  LIBB_C04Partition.node (NNC_ByteCarriers.host left.val) (NNC_ByteCarriers.host right.val)
   (by simpa only [NNC_ByteCarriers.host,List.length_map] using left.property)
   (by simpa only [NNC_ByteCarriers.host,List.length_map] using right.property)
#print axioms flatten
#print axioms node
end LIBB_FlattenBytes

import LIBB_FlattenBytes
import LIBB_C04PartialPartition
set_option autoImplicit false
namespace LIBB_C04LeafPartition
open Aeneas Aeneas.Std
/-- Any source view, including a truncated/error-prefix view, preserves the
exact hashv parts. No successful opening decode is a precondition. -/
theorem parts (tag : U8) (n : Nat) (value salt : Slice U8)
 (size : n = if NND_Carrier.byte tag = 113 then 480 else 128)
 (hv : value.val.length ≤ n) (hs : salt.val.length ≤ 32)
 (full : salt.val ≠ [] → value.val.length = n) :
 LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
  (AspisV8R19.SqueezeOracleBridge.flatten (AspisR1.Port4B_LeafCode.parts tag value salt))) =
 NNC_ResumeEvents.parts (AspisR1.Port4B_LeafCode.parts tag value salt) := by
 rw [LIBB_FlattenBytes.flatten]
 have h := LIBB_C04PartialPartition.leaf (NND_Carrier.byte tag) n
  (NNC_ByteCarriers.host value.val) (NNC_ByteCarriers.host salt.val) size
  (by simpa only [NNC_ByteCarriers.host,List.length_map] using hv)
  (by simpa only [NNC_ByteCarriers.host,List.length_map] using hs) (by
   intro hne
   have hraw : salt.val ≠ [] := by intro hnil; exact hne (by simp [hnil,NNC_ByteCarriers.host])
   simpa only [NNC_ByteCarriers.host,List.length_map] using full hraw)
 simpa only [AspisR1.Port4B_LeafCode.parts,NNC_ResumeEvents.parts,
  List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
  NNC_ByteCarriers.host,NND_Carrier.byte] using h

/-- A slice that starts later than the value ends can contain salt only
once the complete value is present. This is plain interval geometry. -/
theorem windows (o : Slice U8) (vs ve ss se n : Nat)
 (order : vs ≤ ve) (separated : ve ≤ ss) (saltWidth : se - ss = 32) (width : ve - vs = n) :
 let value := (o.val.drop vs).take n
 let salt := (o.val.drop ss).take 32
 value.length ≤ n ∧ salt.length ≤ 32 ∧ (salt ≠ [] → value.length = n) := by
 dsimp only
 constructor
 · simp only [List.length_take,List.length_drop]; omega
 constructor
 · simp only [List.length_take,List.length_drop]; omega
 · intro hne
   have hpos : 0 < ((o.val.drop ss).take 32).length := List.length_pos_iff.mpr hne
   simp only [List.length_take,List.length_drop] at hpos ⊢
   omega

#print axioms parts
#print axioms windows
end LIBB_C04LeafPartition

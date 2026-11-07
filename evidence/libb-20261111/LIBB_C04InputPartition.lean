import LIBB_C04LeafPartition
set_option autoImplicit false
namespace LIBB_C04InputPartition
open Aeneas Aeneas.Std
open AspisR1 MultiproofConeSlices
/-- Full input law on arbitrary views. The disjoint source subranges imply
that a salt suffix is possible only after the whole value window is present. -/
theorem input (kind : Usize) (o : Slice U8) :
 LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
  (AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input kind o))) =
 NNC_ResumeEvents.parts (Port4B_LeafCode.input kind o) := by
 unfold Port4B_LeafCode.input
 split
 · apply LIBB_C04LeafPartition.parts 113#u8 480 _ _
   · decide
   · simp only [sub,List.length_take,List.length_drop]; omega
   · simp only [sub,List.length_take,List.length_drop]; omega
   · intro hne
     have hp : 0 < (sub o 608#usize 640#usize).val.length := List.length_pos_iff.mpr hne
     simp [sub] at hp ⊢
     omega
 · split
   · apply LIBB_C04LeafPartition.parts 241#u8 128 _ _
     · decide
     · simp only [sub,List.length_take,List.length_drop]; omega
     · simp only [sub,List.length_take,List.length_drop]; omega
     · intro hne
       have hp : 0 < (sub o 640#usize 672#usize).val.length := List.length_pos_iff.mpr hne
       simp [sub] at hp ⊢
       omega
   · apply LIBB_C04LeafPartition.parts 114#u8 128 _ _
     · decide
     · simp only [sub,List.length_take,List.length_drop]; omega
     · simp only [sub,List.length_take,List.length_drop]; omega
     · intro hne
       have hp : 0 < (sub o 800#usize 832#usize).val.length := List.length_pos_iff.mpr hne
       simp [sub] at hp ⊢
       omega
#print axioms input
end LIBB_C04InputPartition

import NMX_R3_LaneModels
set_option autoImplicit false
namespace NMX_R3_LaneModelEquality
open RSL
attribute [local irreducible] TX2_217.frontierLoop TX2_217.decodeDigestCanonical RSL.le64

theorem value (b : Bytes) (extent : b.length = 768) :
 NMX_R3_LaneModels.header b = TX2_217.laneDecode b := by
 have width : (slice b 40 72).length = 32 := by
  simp only [slice, List.length_take, List.length_drop, extent]
  rfl
 unfold NMX_R3_LaneModels.header NMX_R3_LaneModels.master NMX_R3_LaneModels.tree
  NMX_R3_LaneModels.counter NMX_R3_LaneModels.digest NMX_R3_LaneModels.frontier
  NMX_R3_LaneModels.emit TX2_217.laneDecode
 simp only [width, ↓reduceDIte]
 split
 · rfl
 · split
   · rfl
   · split
     · rfl
     · split
       · rfl
       · generalize TX2_217.decodeDigestCanonical (slice (b.drop LANE_HEADER_BYTES) 16 48) = root
         cases root with
         | none => rfl
         | some r =>
          generalize TX2_217.frontierLoop (b.drop LANE_HEADER_BYTES)
           (le64 (slice (b.drop LANE_HEADER_BYTES) 8 16)) TREE_DEPTH = frontier
          cases frontier with
          | none => rfl
          | some f => rfl
#print axioms value
end NMX_R3_LaneModelEquality

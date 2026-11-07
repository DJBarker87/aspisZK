import NMX_R3_LaneTree
set_option autoImplicit false
namespace NMX_R3_LaneMaster
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] NMX_R3_LaneModels.tree

theorem value (b : Slice U8) (laneId : U8) (extent : b.val.length = 768) :
 observe (NMX_R3_LaneCuts.master b laneId) =
 ok (NMX_R3_LaneModels.master (b.val.map byte) (byte laneId)) := by
 let a := NDB_PrimaryWords.window b 40 32#usize
 have fit : 40+32 ≤ b.val.length := by omega
 have field : (b.val.drop 40).take 32 = a.val := by
  simpa only [NMX_R3_Indices.v32] using (NMX_R3_PrimaryWindow.bytes b 40 32#usize
   (by rw [NMX_R3_Indices.v32]; exact fit)).symm
 have call := NMX_R3_PrimaryWindow.bytes32 b 40#usize a (by omega)
  (by rw [NMX_R3_Indices.v40]; exact fit) (by simpa only [NMX_R3_Indices.v40] using field)
 have image : a.val.map byte = slice (b.val.map byte) 40 72 := by
  rw [←field, NMX_R3_ByteCarrier.window]
 have width : (slice (b.val.map byte) 40 72).length = 32 := by
  rw [←image, List.length_map, a.property, NMX_R3_Indices.v32]
 have same : key a = (⟨slice (b.val.map byte) 40 72,width⟩ : B32) := by
  unfold key
  congr 1
 have zeroCall := NMX_R3_Zero.value (Array.to_slice a)
  (by rw [NMX_R3_Slices.array_val,a.property,NMX_R3_Indices.v32]; decide)
 simp only [NMX_R3_LaneCuts.master, call, lift, bind_tc_ok, zeroCall,
  NMX_R3_Slices.array_val, image, through_if, returned, NMX_R3_LaneCarrier.result,
  NMX_R3_LaneTree.value b a laneId extent, pure_if, NMX_R3_LaneModels.master, width,
  ↓reduceDIte, same]
#print axioms value
end NMX_R3_LaneMaster

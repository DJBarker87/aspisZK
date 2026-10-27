import RPz7_AuS1_Absorb
import RPz7_SdkD_FirstModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Frame
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

 theorem folded (state root : Array U8 32#usize) (tag : U8) (len : U32)
    (tail : List U8) (payload : Slice U8)
    (payload_eq : payload.val = root.val ++ tail) :
    BinRawByteCollisionTargets.pred 3
      (flatten (AuS1_Absorb.parts state tag len payload)) = some (decodeState root) := by
  rw [BinRawByteCollisionTargets.pred_middle]
  let pre := bytesOf state.val ++ [decodeByte 0#u8,decodeByte tag] ++
    bytesOf (core.num.U32.to_le_bytes len).val
  have length : pre.length = 38 := by
    have stateLength := state.property
    have lenLength := (core.num.U32.to_le_bytes len).property
    change state.val.length = 32 at stateLength
    change (core.num.U32.to_le_bytes len).val.length = 4 at lenLength
    simp only [pre,bytesOf,List.length_append,List.length_map,List.length_cons,List.length_nil,
      stateLength,lenLength]
  have shape : flatten (AuS1_Absorb.parts state tag len payload) =
      pre ++ bytes (decodeState root) ++ bytesOf tail := by
    simp only [AuS1_Absorb.parts,flatten,Array.to_slice,Array.make,List.flatMap_cons,
      List.flatMap_nil,List.map_append]
    rw [payload_eq]
    simp only [pre,bytesOf,List.map_cons,List.map_nil,List.map_append,
      MultiproofConePhysicalTransport.digest_bytes,List.append_nil,List.append_assoc]
  rw [shape]
  exact BinRawByteCollisionTargets.fixed_frame 38 pre (decodeState root) (bytesOf tail) length

#print axioms folded
end AspisR1.AuS1_Frame
end

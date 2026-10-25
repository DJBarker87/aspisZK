import AuS1_Absorb
import SdkD_FirstModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Frame
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

 theorem folded (state root : Array U8 32#usize) (tail : List U8) (payload : Slice U8)
    (payload_eq : payload.val = root.val ++ tail) :
    BinRawByteCollisionTargets.pred 3
      (flatten (AuS1_Absorb.parts state 190#u8 256#u32 payload)) = some (decodeState root) := by
  rw [BinRawByteCollisionTargets.pred_middle]
  have shape : flatten (AuS1_Absorb.parts state 190#u8 256#u32 payload) =
      bytes (decodeState state) ++ [0,190,0,1,0,0] ++ bytes (decodeState root) ++ bytesOf tail := by
    have stateBytes := MultiproofConePhysicalTransport.digest_bytes state
    have rootBytes := MultiproofConePhysicalTransport.digest_bytes root
    change bytesOf state.val ++ ([0,190] ++ ([0,1,0,0] ++ (bytesOf payload.val ++ []))) = _
    rw [payload_eq]
    simp only [bytesOf,List.map_append,← stateBytes,← rootBytes,List.append_nil,List.append_assoc]
  rw [shape]
  apply BinRawByteCollisionTargets.fixed_frame
  simp only [List.length_append,bytes_length,List.length_cons,List.length_nil]

#print axioms folded
end AspisR1.AuS1_Frame
end

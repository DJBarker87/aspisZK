import AuS1_Suffix
import AuS1_Frame
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_DigestRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode

theorem digest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (parts : Slice (Slice U8)) (out : Array U8 32#usize)
    (success : erase (effects.digest D hash parts) = ok out) :
    Read (observe (run (effects.digest D hash parts)).1) (flatten parts) := by
  change D.digest hash parts = ok out at success
  simp only [effects,run,success,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append]
  exact List.mem_singleton_self _

def initParts (pub : Slice U8) (len : U32) (root : Array U8 32#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 5#usize [AspisR1PublicPreparation.r1_wire.DOMAIN,
    Array.to_slice (Array.make 1#usize [0#u8]),Array.to_slice (core.num.U32.to_le_bytes len),pub,
    Array.to_slice root])

theorem target (pub : Slice U8) (len : U32) (root : Array U8 32#usize) :
    BinRawByteCollisionTargets.pred 2 (flatten (initParts pub len root)) =
      some (decodeState root) := by
  rw [BinRawByteCollisionTargets.pred_tail]
  have shape : flatten (initParts pub len root) =
      (bytesOf AspisR1PublicPreparation.r1_wire.DOMAIN.val ++
        [decodeByte 0#u8] ++ bytesOf (core.num.U32.to_le_bytes len).val ++ bytesOf pub.val) ++
        bytes (decodeState root) := by
    simp only [initParts,flatten,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
      MultiproofConeCanonical.bytesOf,List.map_cons,List.map_nil,List.append_nil,
      MultiproofConePhysicalTransport.digest_bytes,List.append_assoc]
  rw [shape]
  exact BinRawByteCollisionTargets.trailing_frame _ _

#print axioms digest
#print axioms target
end AspisR1.RawJ_DigestRead
end

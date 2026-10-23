import S2W_CommittedCheckpoint

/-! Canonical conversion of the ACTUAL returned Aeneas vector to the SDK
payload carrier. No independent source-byte representation equality assumed. -/
set_option autoImplicit false
namespace AspisR1.S2W_ReturnedCheckpoint
open Aeneas Aeneas.Std S2Trust S2W_WrapperLaws S2W_EntryWriteHistory S2W_CommittedCheckpoint
open MultiproofConeCanonical AspisV8R19.DuplexFrames

def encode (byte : UInt8) : AspisV8R19.DuplexFrames.Byte := byte.toFin
def nativeByte (byte : U8) : UInt8 := UInt8.ofNat byte.val
def nativeBytes (saved : alloc.vec.Vec U8) : List UInt8 := saved.val.map nativeByte

theorem byte_representation (byte : U8) :
    encode (nativeByte byte) = AspisV8R19.SqueezeOracleBridge.decodeByte byte := by
  apply Fin.ext
  change (UInt8.ofNat byte.val).toNat = byte.val
  exact UInt8.toNat_ofNat_of_lt' byte.bv.isLt

theorem vector_representation (saved : alloc.vec.Vec U8) :
    (nativeBytes saved).map encode = bytesOf saved.val := by
  simp only [nativeBytes,bytesOf,List.map_map]
  exact List.map_congr_left (fun byte _ => byte_representation byte)

/-- The loaded version is connected to the same returned vector by first
using the computed write payload in the history premise. A1768-byte list is
never manufactured as an independent checkpoint observation. Native wrapper
source/heap interpretation is still needed to instantiate this local law. -/
theorem returned_committed {F : Type} (heap : Heap F) (account token owner : Nat)
    (saved : alloc.vec.Vec U8) (loaded : Bytes)
    (empty : heap.guards = []) (zero : heap.counter (heap.accounts account).1 = 0)
    (destinationSize : (heap.payload (heap.accounts account).1).descriptor.length = 1768)
    (savedSize : saved.val.length = 1768)
    (version : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket heap account token owner (source (nativeBytes saved))).payload
        (heap.accounts account).1) 1768) loaded) :
    loaded = bytesOf saved.val ∧
    Nonempty (S2W_AuthenticatedInputs.CheckpointVersionBinding (bytesOf saved.val) loaded) := by
  have size : (nativeBytes saved).length = 1768 := by
    simpa only [nativeBytes,List.length_map] using savedSize
  obtain ⟨same,rebound⟩ := committed_version encode heap account token owner (nativeBytes saved)
    loaded empty zero destinationSize size version
  rw [vector_representation] at same rebound
  exact ⟨same,rebound⟩

#print axioms byte_representation
#print axioms vector_representation
#print axioms returned_committed
end AspisR1.S2W_ReturnedCheckpoint

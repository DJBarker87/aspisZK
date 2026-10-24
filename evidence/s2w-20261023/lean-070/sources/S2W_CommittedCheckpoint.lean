import S2W_EntryWriteHistory
import S2W_D188Consolidation

/-! Commit-indexed checkpoint composition. The history premise is indexed to
THE COMPUTED POST-WRITE PAYLOAD, rather than to the returned vector. This
removes a savedAtCommit substitution from the local composition. This module
makes no claim that writeBracket is already the native AccountInfo wrapper. -/
set_option autoImplicit false
namespace AspisR1.S2W_CommittedCheckpoint
open S2Trust S2W_TrustedStd S2W_WrapperLaws S2W_EntryWriteHistory
open AspisV8R19.DuplexFrames

def source (bytes : List UInt8) : Payload :=
  ⟨⟨0,bytes.length,0⟩,fun i => bytes[i]?.getD 0⟩

theorem source_bytes (encode : UInt8 → Byte) (bytes : List UInt8) :
    payloadBytes encode (source bytes) bytes.length = bytes.map encode := by
  apply List.ext_getElem
  · simp [payloadBytes]
  · intro i left right
    simp [payloadBytes,source,List.getElem?_eq_getElem,left]

/-- Kani's arbitrary-coordinate copy contract lifts symbolically, without
reducing 1768 entries. The runtime version is associated with the computed
account write, then transported to the returned serialization. -/
theorem committed_version {F : Type} (encode : UInt8 → Byte)
    (heap : Heap F) (account token owner : Nat) (saved : List UInt8)
    (loaded : Bytes) (empty : heap.guards = [])
    (zero : heap.counter (heap.accounts account).1 = 0)
    (destinationSize : (heap.payload (heap.accounts account).1).descriptor.length = 1768)
    (savedSize : saved.length = 1768)
    (version : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket heap account token owner (source saved)).payload
        (heap.accounts account).1) 1768) loaded) :
    loaded = saved.map encode ∧
    S2W_AuthenticatedInputs.CheckpointVersionBinding (saved.map encode) loaded := by
  have written := written_bytes encode heap account token owner (source saved)
    empty zero destinationSize
  have same : payloadBytes encode ((writeBracket heap account token owner (source saved)).payload
      (heap.accounts account).1) 1768 = saved.map encode := by
    rw [written,← savedSize]
    exact source_bytes encode saved
  have rebound : S2X.CheckpointVersionBinding (saved.map encode) loaded := by
    rw [← same]
    exact version
  exact ⟨S2X.checkpoint_persistence _ _ rebound,⟨rebound⟩⟩

#print axioms source_bytes
#print axioms committed_version
end AspisR1.S2W_CommittedCheckpoint

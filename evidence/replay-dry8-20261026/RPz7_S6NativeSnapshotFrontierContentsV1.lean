import RPz7_S6NativeSnapshotLoopV1
import RPz7_S6NativeDigestByteContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeAfterstateEncoderReuse
open AspisS6SourceCodec
namespace Snapshot

theorem frontier_fold_contents
    (nodes : List (Array U32 8#usize)) (level : Nat)
    (output : Slice U8) (lead : List U8)
    (position : lead.length=160+32*level)
    (initialized : output.val=lead++List.replicate (32*nodes.length) 0#u8) :
    (AspisS6NativeSnapshotLoop.fold nodes level output).val=
      lead++nodes.flatMap DigestContents.chunks := by
  induction nodes generalizing level output lead with
  | nil => simpa [AspisS6NativeSnapshotLoop.fold] using initialized
  | cons node tail ih =>
    have hwrite :
        (AspisS6NativeSnapshotStore.write output (160+32*level) (AspisR1.S2K.DigestBytes.bytes node)).val=
        (lead++DigestContents.chunks node)++List.replicate (32*tail.length) 0#u8 := by
      change output.val.setSlice! (160+32*level) (AspisR1.S2K.DigestBytes.bytes node).val=_
      rw [initialized,←position,native_digest_bytes]
      have h := AspisS6SliceFrame.setSlice_append_chunk lead (DigestContents.chunks node)
        (32*(tail.length+1)) 0#u8 (by rw [PaymentContents.digest_chunks_length]; omega)
      simpa [PaymentContents.digest_chunks_length,Nat.mul_add] using h
    have hposition : (lead++DigestContents.chunks node).length=160+32*(level+1) := by
      simp only [List.length_append,PaymentContents.digest_chunks_length,position]
      omega
    have rest := ih (level+1)
      (AspisS6NativeSnapshotStore.write output (160+32*level) (AspisR1.S2K.DigestBytes.bytes node))
      (lead++DigestContents.chunks node) hposition hwrite
    simpa only [AspisS6NativeSnapshotLoop.fold,List.flatMap_cons,List.append_assoc] using rest

#print axioms frontier_fold_contents
end Snapshot
end AspisS6NativeAfterstateEncoderReuse

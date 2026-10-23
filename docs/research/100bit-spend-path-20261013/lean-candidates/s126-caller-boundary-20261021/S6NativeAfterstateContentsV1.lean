import S6NativeDigestByteContentsV1
import S6AfterstateWriteFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeAfterstateEncoderReuse
open AspisS6SourceCodec

theorem frontier_fold_contents
    (nodes : List (Array U32 8#usize)) (level : Nat)
    (output : Array U8 688#usize) (lead : List U8)
    (position : lead.length=48+32*level)
    (initialized : output.val=lead++List.replicate (32*nodes.length) 0#u8) :
    (AspisR1.S2K.AfterstateBytes.fold nodes level output).val=
      lead++nodes.flatMap DigestContents.chunks := by
  induction nodes generalizing level output lead with
  | nil => simpa [AspisR1.S2K.AfterstateBytes.fold] using initialized
  | cons node tail ih =>
    have hwrite :
        (output.setSlice! (48+32*level) (AspisR1.S2K.DigestBytes.bytes node).val).val=
        (lead++DigestContents.chunks node)++List.replicate (32*tail.length) 0#u8 := by
      change output.val.setSlice! (48+32*level) (AspisR1.S2K.DigestBytes.bytes node).val=_
      rw [initialized,←position,native_digest_bytes]
      have h := AspisS6SliceFrame.setSlice_append_chunk lead (DigestContents.chunks node)
        (32*(tail.length+1)) 0#u8 (by rw [PaymentContents.digest_chunks_length]; omega)
      simpa [PaymentContents.digest_chunks_length,Nat.mul_add] using h
    have hposition : (lead++DigestContents.chunks node).length=48+32*(level+1) := by
      simp only [List.length_append,PaymentContents.digest_chunks_length,position]
      omega
    have rest := ih (level+1)
      (output.setSlice! (48+32*level) (AspisR1.S2K.DigestBytes.bytes node).val)
      (lead++DigestContents.chunks node) hposition hwrite
    simpa only [AspisR1.S2K.AfterstateBytes.fold,List.flatMap_cons,List.append_assoc] using rest


def header_bytes : List U8 :=
  AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val++
    [AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
     AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
     AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,1#u8]

def prefix_bytes (a : Native.Afterstate) : List U8 :=
  header_bytes++(core.num.U64.to_le_bytes a.next_pair_index).val++DigestContents.chunks a.next_root

theorem prefix_length (a : Native.Afterstate) : (prefix_bytes a).length=48 := by
  simp [prefix_bytes,header_bytes,PaymentContents.digest_chunks_length,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
    (core.num.U64.to_le_bytes a.next_pair_index).property]

theorem prepare_contents (a : Native.Afterstate) (output : Array U8 688#usize)
    (initialized : output.val=List.replicate 688 0#u8) :
    (AspisR1.S2K.AfterstatePrepare.value a output).val=
      prefix_bytes a++List.replicate 640 0#u8 := by
  unfold AspisR1.S2K.AfterstatePrepare.value
  change ((((((output.val.setSlice! 0 AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val).set 4 AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION).set 5 AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION).set 6 AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION).set 7 1#u8).setSlice! 8 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice! 16 (AspisR1.S2K.DigestBytes.bytes a.next_root).val=prefix_bytes a++List.replicate 640 0#u8
  rw [initialized,native_digest_bytes]
  erw [AspisS6SliceFrame.afterstate_header_writes
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property
    0#u8
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION 1#u8]
  exact AspisS6SliceFrame.afterstate_prefix_chunks 0#u8 header_bytes
    (core.num.U64.to_le_bytes a.next_pair_index).val (DigestContents.chunks a.next_root)
    (by simp [header_bytes,AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property])
    (core.num.U64.to_le_bytes a.next_pair_index).property
    (PaymentContents.digest_chunks_length a.next_root)

theorem native_afterstate_contents (a : Native.Afterstate) :
    (AspisR1.S2K.AfterstateEncoding.bytes a).val=
      prefix_bytes a++a.next_frontier.val.flatMap DigestContents.chunks := by
  unfold AspisR1.S2K.AfterstateEncoding.bytes
  apply frontier_fold_contents _ 0 _ (prefix_bytes a)
  · simpa using prefix_length a
  · have hlen : a.next_frontier.val.length=20 := a.next_frontier.property
    simpa only [hlen, Nat.reduceMul] using
      prepare_contents a (Array.repeat 688#usize 0#u8) rfl

#print axioms frontier_fold_contents
#print axioms prefix_length
#print axioms prepare_contents
#print axioms native_afterstate_contents
end AspisS6NativeAfterstateEncoderReuse

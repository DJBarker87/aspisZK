import S6NativeAfterstateContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeAfterstateEncoderReuse
open AspisS6SourceCodec
open AspisS6SourceCodec.AfterstateFactored.Frames

theorem accepted_header_prefix (raw : Array U8 688#usize)
    (frame : header_frame raw) : header_bytes=raw.val.take 8 := by
  rcases frame with ⟨magic,h4,h5,h6,h7⟩
  have hm : raw.val.take 4=
      AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val := by
    simpa [List.slice] using magic
  have split := AspisS6SliceFrame.header_eight raw.val (by rw [raw.property]; decide)
  rw [hm,h4,h5,h6,h7] at split
  simpa only [header_bytes,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
    AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    AspisS6SourceCodec.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION] using split.symm

theorem decoded_layout (bytes : Slice U8) (a : ReferenceAfterstate)
    (frame : full_frame bytes a) :
    prefix_bytes (native a)++a.next_frontier.val.flatMap DigestContents.chunks=bytes.val := by
  rcases frame with ⟨⟨raw,rawbytes,header⟩,root,frontier,index,validated⟩
  have hheader := accepted_header_prefix raw header
  rw [rawbytes] at hheader
  have hroot := digest_frame_contents bytes 16 a.next_root root
  have hfrontier := frontier_frame_contents bytes 48 a.next_frontier.val frontier
  have hfrontierlen : a.next_frontier.val.length=20 := a.next_frontier.property
  simp only [hfrontierlen,Nat.reduceMul,Nat.reduceAdd] at hfrontier
  unfold prefix_bytes native
  rw [hheader,index,hroot,hfrontier]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 8 16 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 16 48 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 48 688 (by decide)]
  have hlen : bytes.val.length=688 := rawbytes ▸ raw.property
  simpa only [←hlen,List.take_length]

/-- Native iterator encoder bytes equal the same accepted complete reference
input. Both concrete successful calls are retained, matching the enclosing
FullForestAcceptedRoundtrip interface. Source/native decoder transport is a
separate obligation; no arbitrary encoder or simplified carrier is used. -/
theorem accepted_roundtrip (bytes : Slice U8) (a : ReferenceAfterstate)
    (encoded : Array U8 688#usize)
    (decoded : AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=
      ok (core.result.Result.Ok a))
    (encoded_actual : AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (native a)=
      ok (core.result.Result.Ok encoded)) : encoded.val=bytes.val := by
  rw [accepted_encoder_bytes (native a) encoded encoded_actual,native_afterstate_contents]
  exact decoded_layout bytes a (source_accepted_frames bytes a decoded)

#print axioms accepted_header_prefix
#print axioms decoded_layout
#print axioms accepted_roundtrip
end AspisS6NativeAfterstateEncoderReuse

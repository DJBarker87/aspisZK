import RPz7_S6NativeAfterstateDecodedFramesV1
import RPz7_S6NativeAfterstateContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateCodec
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
open AspisS6NativeAfterstateDecoderFactored
open AspisS6NativeAfterstateDecoderFactored.Frames
open AspisS6NativeAfterstateEncoderReuse

/-- TOTAL actual native decoder, on all slices and all rejection paths. -/
theorem decode_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_pair_verified_afterstate_v1 bytes=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (decode_frames bytes)
  exact ⟨result,(decode_source bytes).symm.trans run⟩

/-- Accepted frames are consequences of the actual native decoder return. -/
theorem accepted_frames (bytes : Slice U8) (afterstate : PoolV1PairVerifiedAfterstateV1)
    (accepted : decode_pool_v1_pair_verified_afterstate_v1 bytes=ok (core.result.Result.Ok afterstate)) :
    full_frame bytes afterstate := by
  have frames := decode_frames bytes
  rw [decode_source bytes,accepted,WP.spec_ok] at frames
  exact frames afterstate rfl

theorem header_prefix (raw : Array U8 688#usize) (frame : header_frame raw) :
    header_bytes=raw.val.take 8 := by
  rcases frame with ⟨magic,h4,h5,h6,h7⟩
  have hm : raw.val.take 4=POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val := by
    simpa [List.slice] using magic
  have split := AspisS6SliceFrame.header_eight raw.val (by rw [raw.property]; decide)
  rw [hm,h4,h5,h6,h7] at split
  exact split.symm

theorem decoded_layout (bytes : Slice U8) (a : PoolV1PairVerifiedAfterstateV1)
    (frame : full_frame bytes a) :
    prefix_bytes a++a.next_frontier.val.flatMap AspisS6SourceCodec.DigestContents.chunks=bytes.val := by
  rcases frame with ⟨⟨raw,rawbytes,header⟩,root,frontier,index,validated⟩
  have hheader := header_prefix raw header
  rw [rawbytes] at hheader
  have hroot := AspisS6SourceCodec.AfterstateFactored.Frames.digest_frame_contents bytes 16 a.next_root root
  have hfrontier := AspisS6SourceCodec.AfterstateFactored.Frames.frontier_frame_contents bytes 48 a.next_frontier.val frontier
  have hfrontierlen : a.next_frontier.val.length=20 := a.next_frontier.property
  simp only [hfrontierlen,Nat.reduceMul,Nat.reduceAdd] at hfrontier
  unfold prefix_bytes
  rw [hheader,index,hroot,hfrontier]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 8 16 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 16 48 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 48 688 (by decide)]
  have hlen : bytes.val.length=688 := rawbytes ▸ raw.property
  simpa only [←hlen,List.take_length]

/-- TOTAL actual native encoder on arbitrary full records, including validator
errors. No accepted/canonical input or successful child is a hypothesis. -/
theorem encode_total (afterstate : PoolV1PairVerifiedAfterstateV1) :
    ∃ result, encode_pool_v1_pair_verified_afterstate_v1 afterstate=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (AspisS6NativeAfterstateValidatorTotal.validator_spec afterstate)
  cases result with
  | Ok unit =>
    cases unit
    exact ⟨_,AspisR1.S2K.AfterstateEncoding.encode_exact afterstate run⟩
  | Err error =>
    exact ⟨_,AspisR1.S2K.AfterstateStatus.rejection afterstate error run⟩

/-- The actual complete native codec inverse. The sole premise is the actual
native successful decode; native encoder success and exact bytes are derived. -/
theorem accepted_inverse (bytes : Slice U8) (afterstate : PoolV1PairVerifiedAfterstateV1)
    (accepted : decode_pool_v1_pair_verified_afterstate_v1 bytes=ok (core.result.Result.Ok afterstate)) :
    ∃ encoded : Array U8 688#usize, encoded.val=bytes.val ∧
      encode_pool_v1_pair_verified_afterstate_v1 afterstate=ok (core.result.Result.Ok encoded) := by
  have frames := accepted_frames bytes afterstate accepted
  have validated := frames.2.2.2.2
  refine ⟨AspisR1.S2K.AfterstateEncoding.bytes afterstate,?_,?_⟩
  · rw [native_afterstate_contents]
    exact decoded_layout bytes afterstate frames
  · exact AspisR1.S2K.AfterstateEncoding.encode_exact afterstate validated

/-- Two-success form at the actual source operations, for parent composition. -/
theorem accepted_roundtrip (bytes : Slice U8) (afterstate : PoolV1PairVerifiedAfterstateV1)
    (encoded : Array U8 688#usize)
    (decoded : decode_pool_v1_pair_verified_afterstate_v1 bytes=ok (core.result.Result.Ok afterstate))
    (encoded_actual : encode_pool_v1_pair_verified_afterstate_v1 afterstate=ok (core.result.Result.Ok encoded)) :
    encoded.val=bytes.val := by
  obtain ⟨actual,contents,run⟩ := accepted_inverse bytes afterstate decoded
  rw [encoded_actual] at run
  cases run
  exact contents

#print axioms decode_total
#print axioms accepted_frames
#print axioms header_prefix
#print axioms decoded_layout
#print axioms encode_total
#print axioms accepted_inverse
#print axioms accepted_roundtrip
end AspisS6NativeAfterstateCodec

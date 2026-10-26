import RPz7_S6NativeAfterstateDecoderFactoredV1
import RPz7_S6NativeAfterstateDecodeHelpersV1
import S6ByteInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
abbrev Digest := Array U32 8#usize

abbrev digest_frame := AspisS6SourceCodec.AfterstateFactored.Frames.digest_frame
abbrev frontier_frames := AspisS6SourceCodec.AfterstateFactored.Frames.frontier_frames

def part_frame (bytes : Slice U8) (root : Digest) (prior : List Digest)
    (afterstate : PoolV1PairVerifiedAfterstateV1) : Prop :=
  afterstate.next_root=root ∧ ∃ suffix,
    afterstate.next_frontier.val=prior++suffix ∧
    frontier_frames bytes (48+32*prior.length) suffix ∧
    (core.num.U64.to_le_bytes afterstate.next_pair_index).val=List.slice 8 16 bytes.val ∧
    validate_verified_afterstate afterstate=ok (core.result.Result.Ok ())

@[step] theorem part16_frames (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Digest)
    (hlen : bytes.length=688) :
    part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25,val27,val29,val31,val33] afterstate ⦄ := by
  unfold part_16
  step*
  all_goals (intro afterstate accepted; cases accepted)
  all_goals (unfold part_frame; refine ⟨rfl, [val35,val37,val39,val41], rfl, ?_, ?_, ?_⟩)
  all_goals (simp_all [frontier_frames,digest_frame,AspisS6SourceCodec.AfterstateFactored.Frames.frontier_frames,AspisS6SourceCodec.AfterstateFactored.Frames.digest_frame,AspisS6ByteInverse.u64_to_from,List.slice])

#print axioms part16_frames
end AspisS6NativeAfterstateDecoderFactored.Frames

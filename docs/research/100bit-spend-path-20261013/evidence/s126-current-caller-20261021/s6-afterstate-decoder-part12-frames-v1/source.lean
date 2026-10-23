import S6AfterstateDecoderFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

@[step] theorem part12_frames (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Digest)
    (hlen : bytes.length=688) :
    part_12 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25] afterstate ⦄ := by
  unfold part_12
  step*
  all_goals (intro afterstate accepted)
  all_goals (simp_all [part_frame,frontier_frames,digest_frame,List.append_assoc])

#print axioms part12_frames
end AspisS6SourceCodec.AfterstateFactored.Frames

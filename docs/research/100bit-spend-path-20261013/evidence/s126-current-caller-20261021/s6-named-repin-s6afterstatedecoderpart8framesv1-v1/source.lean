import S6AfterstateDecoderPart12FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

@[step] theorem part8_frames (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Digest)
    (hlen : bytes.length=688) :
    part_8 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [val3,val5,val7,val9,val11,val13,val15,val17] afterstate ⦄ := by
  unfold part_8
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val1 val25 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23] _ later (by
    unfold digest_frame
    refine ⟨val24, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val23 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21] _ later (by
    unfold digest_frame
    refine ⟨val22, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val21 [val3,val5,val7,val9,val11,val13,val15,val17,val19] _ later (by
    unfold digest_frame
    refine ⟨val20, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val19 [val3,val5,val7,val9,val11,val13,val15,val17] _ later (by
    unfold digest_frame
    refine ⟨val18, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part8_frames
end AspisS6SourceCodec.AfterstateFactored.Frames

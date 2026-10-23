import S6AfterstateFramePrependV1
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
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val1 val33 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25,val27,val29,val31] _ later (by
    unfold digest_frame
    refine ⟨val32, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val31 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25,val27,val29] _ later (by
    unfold digest_frame
    refine ⟨val30, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val29 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25,val27] _ later (by
    unfold digest_frame
    refine ⟨val28, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val27 [val3,val5,val7,val9,val11,val13,val15,val17,val19,val21,val23,val25] _ later (by
    unfold digest_frame
    refine ⟨val26, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part12_frames
end AspisS6SourceCodec.AfterstateFactored.Frames

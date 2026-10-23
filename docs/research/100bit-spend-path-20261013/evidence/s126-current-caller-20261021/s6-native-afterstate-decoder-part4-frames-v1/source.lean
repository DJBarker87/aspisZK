import S6NativeAfterstateDecoderPart8FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_terminal

@[step] theorem part4_frames (bytes : Slice U8)
    (val1 val3 val5 val7 val9 : Digest)
    (hlen : bytes.length=688) :
    part_4 bytes val1 val3 val5 val7 val9
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [val3,val5,val7,val9] afterstate ⦄ := by
  unfold part_4
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val1 val17 [val3,val5,val7,val9,val11,val13,val15] _ later (by
    unfold digest_frame
    refine ⟨val16, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val15 [val3,val5,val7,val9,val11,val13] _ later (by
    unfold digest_frame
    refine ⟨val14, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val13 [val3,val5,val7,val9,val11] _ later (by
    unfold digest_frame
    refine ⟨val12, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val11 [val3,val5,val7,val9] _ later (by
    unfold digest_frame
    refine ⟨val10, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part4_frames
end AspisS6NativeAfterstateDecoderFactored.Frames

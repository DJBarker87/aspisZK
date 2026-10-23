import S6NativeAfterstateDecoderPart4FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_terminal

@[step] theorem part0_frames (bytes : Slice U8)
    (val1 : Digest)
    (hlen : bytes.length=688) :
    part_0 bytes val1
      ⦃ result => ∀ afterstate, result=core.result.Result.Ok afterstate →
        part_frame bytes val1 [] afterstate ⦄ := by
  unfold part_0
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val1 val9 [val3,val5,val7] _ later (by
    unfold digest_frame
    refine ⟨val8, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val7 [val3,val5] _ later (by
    unfold digest_frame
    refine ⟨val6, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val5 [val3] _ later (by
    unfold digest_frame
    refine ⟨val4, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val1 val3 [] _ later (by
    unfold digest_frame
    refine ⟨val2, ?_, ?_⟩ <;> simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part0_frames
end AspisS6NativeAfterstateDecoderFactored.Frames

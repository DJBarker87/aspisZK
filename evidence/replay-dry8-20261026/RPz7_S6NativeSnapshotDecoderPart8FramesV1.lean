import RPz7_S6NativeSnapshotDecoderPart12FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem part8_frames (bytes : Slice U8)
    (val val1 val2 val3 val4 val5 val6 val7 val8 : Digest) (size : bytes.length=800) :
    part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8
      ⦃ result => ∀ snapshot, result=core.result.Result.Ok snapshot →
        part_frame bytes val [val1,val2,val3,val4,val5,val6,val7,val8] snapshot ⦄ := by
  unfold part_8
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val val12 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val11 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val10 [val1,val2,val3,val4,val5,val6,val7,val8,val9] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val9 [val1,val2,val3,val4,val5,val6,val7,val8] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part8_frames
end AspisS6NativeSnapshotDecoderFactored.Frames

import RPz7_S6NativeSnapshotDecoderPart8FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem part4_frames (bytes : Slice U8)
    (val val1 val2 val3 val4 : Digest) (size : bytes.length=800) :
    part_4 bytes val val1 val2 val3 val4
      ⦃ result => ∀ snapshot, result=core.result.Result.Ok snapshot →
        part_frame bytes val [val1,val2,val3,val4] snapshot ⦄ := by
  unfold part_4
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val val8 [val1,val2,val3,val4,val5,val6,val7] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val7 [val1,val2,val3,val4,val5,val6] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val6 [val1,val2,val3,val4,val5] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val5 [val1,val2,val3,val4] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part4_frames
end AspisS6NativeSnapshotDecoderFactored.Frames

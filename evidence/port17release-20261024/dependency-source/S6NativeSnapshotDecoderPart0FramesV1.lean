import S6NativeSnapshotDecoderPart4FramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem part0_frames (bytes : Slice U8)
    (val : Digest) (size : bytes.length=800) :
    part_0 bytes val
      ⦃ result => ∀ snapshot, result=core.result.Result.Ok snapshot →
        part_frame bytes val [] snapshot ⦄ := by
  unfold part_0
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val val4 [val1,val2,val3] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val3 [val1,val2] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val2 [val1] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val1 [] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part0_frames
end AspisS6NativeSnapshotDecoderFactored.Frames

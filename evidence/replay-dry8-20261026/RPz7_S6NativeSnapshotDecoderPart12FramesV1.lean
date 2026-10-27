import RPz7_S6NativeSnapshotFramePrependV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem part12_frames (bytes : Slice U8)
    (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Digest) (size : bytes.length=800) :
    part_12 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
      ⦃ result => ∀ snapshot, result=core.result.Result.Ok snapshot →
        part_frame bytes val [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12] snapshot ⦄ := by
  unfold part_12
  step*
  all_goals (have later := result_post1 _ result_post2)
  all_goals (have previous := frame_prepend bytes val val16 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12,val13,val14,val15] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val15 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12,val13,val14] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val14 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12,val13] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals (have previous := frame_prepend bytes val val13 [val1,val2,val3,val4,val5,val6,val7,val8,val9,val10,val11,val12] _ later (by simp_all); clear later; have later := previous; clear previous)
  all_goals exact later

#print axioms part12_frames
end AspisS6NativeSnapshotDecoderFactored.Frames

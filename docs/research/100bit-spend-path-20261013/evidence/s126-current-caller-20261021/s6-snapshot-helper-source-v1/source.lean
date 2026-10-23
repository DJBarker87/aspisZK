import S6FullSourceCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error






noncomputable section

namespace AspisS6SnapshotHelper
open AspisS6FiveUnrolledCodec


def frontier_step (snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice Std.U8) (level : Std.Usize) : Result (Slice Std.U8) := do
  let i ← 32#usize * level
  let start ← 160#usize + i
  let i1 ← start + 32#usize
  let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output { start, «end» := i1 }
  let a ← Array.index_usize snapshot.frontier level
  let a1 ← AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical a
  let s1 ← lift (Array.to_slice a1)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  ok (index_mut_back s2)


 def frontier_loop_loop.body (snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (iter : core.ops.range.Range Std.Usize) (output : Slice Std.U8) : Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U8)) (Slice Std.U8)) := do
                    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
                    match o with
                    | none => ok (done output)
                    | some level => let output1 ← frontier_step snapshot output level
                                    ok (cont (iter1, output1))


 def frontier_loop_loop (iter : core.ops.range.Range Std.Usize) (snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice Std.U8) : Result (Slice Std.U8) := do
               loop
                 (fun (iter1, output1) => frontier_loop_loop.body snapshot iter1 output1)
                 (iter, output)


 def frontier_loop (snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice Std.U8) : Result (Slice Std.U8) := do
               frontier_loop_loop { start := 0#usize, «end» := 20#usize } snapshot output

end AspisS6SnapshotHelper

#print axioms AspisS6SnapshotHelper.frontier_step
#print axioms AspisS6SnapshotHelper.frontier_loop

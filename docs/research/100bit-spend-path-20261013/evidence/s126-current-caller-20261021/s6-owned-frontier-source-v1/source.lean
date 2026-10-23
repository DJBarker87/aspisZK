import S6FullSourceCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error






noncomputable section

namespace AspisS6OwnedFrontier
open AspisS6FiveUnrolledCodec


def frontier_step (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) (level : Std.Usize) : Result (Array Std.U8 688#usize) := do
  let i ← 32#usize * level
  let start ← 48#usize + i
  let i1 ← start + 32#usize
  let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start, «end» := i1 }
  let a ← Array.index_usize afterstate.next_frontier level
  let a1 ← AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical a
  let s1 ← lift (Array.to_slice a1)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  ok (index_mut_back s2)


 def frontier_owned_loop.body (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (iter : core.ops.range.Range Std.Usize) (output : Array Std.U8 688#usize) : Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8 688#usize)) (Array Std.U8 688#usize)) := do
                    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
                    match o with
                    | none => ok (done output)
                    | some level => let output1 ← frontier_step afterstate output level
                                    ok (cont (iter1, output1))


 def frontier_owned_loop (iter : core.ops.range.Range Std.Usize) (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) : Result (Array Std.U8 688#usize) := do
               loop
                 (fun (iter1, output1) => frontier_owned_loop.body afterstate iter1 output1)
                 (iter, output)


 def frontier_owned (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) : Result (Array Std.U8 688#usize) := do
               frontier_owned_loop { start := 0#usize, «end» := 20#usize } afterstate output

end AspisS6OwnedFrontier

#print axioms AspisS6OwnedFrontier.frontier_step
#print axioms AspisS6OwnedFrontier.frontier_owned

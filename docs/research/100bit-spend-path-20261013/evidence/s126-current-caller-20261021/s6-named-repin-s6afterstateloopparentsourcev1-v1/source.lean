import S6FullSourceCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error






noncomputable section

namespace AspisS6AfterstateLoopParent
open AspisS6FiveUnrolledCodec


 def aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : Std.U8 := 1#u8


 def aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION : Std.U8 := 1#u8


 def aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC : Array Std.U8 4#usize := Array.make 4#usize [ 65#u8, 83#u8, 74#u8, 65#u8 ]


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION : Std.U8 := 1#u8


 def aspis_statement.pool_v1.pair_terminal.frontier_step_reference (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) (level : Std.Usize) : Result (Array Std.U8 688#usize) := do
                                                                                 let i ← 32#usize * level
                                                                                 let start ← 48#usize + i
                                                                                 let i1 ← start + 32#usize
                                                                                 let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start, «end» := i1 }
                                                                                 let a ← Array.index_usize afterstate.next_frontier level
                                                                                 let a1 ← AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical a
                                                                                 let s1 ← lift (Array.to_slice a1)
                                                                                 let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
                                                                                 ok (index_mut_back s2)


 def aspis_statement.pool_v1.pair_terminal.frontier_owned_reference_loop.body (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (iter : core.ops.range.Range Std.Usize) (output : Array Std.U8 688#usize) : Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8 688#usize)) (Array Std.U8 688#usize)) := do
                                                                                                  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
                                                                                                  match o with
                                                                                                  | none => ok (done output)
                                                                                                  | some level => let output1 ← aspis_statement.pool_v1.pair_terminal.frontier_step_reference afterstate output level
                                                                                                                  ok (cont (iter1, output1))


 def aspis_statement.pool_v1.pair_terminal.frontier_owned_reference_loop (iter : core.ops.range.Range Std.Usize) (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) : Result (Array Std.U8 688#usize) := do
                                                                                             loop
                                                                                               (fun (iter1, output1) => aspis_statement.pool_v1.pair_terminal.frontier_owned_reference_loop.body afterstate iter1 output1)
                                                                                               (iter, output)


 def aspis_statement.pool_v1.pair_terminal.frontier_owned_reference (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) (output : Array Std.U8 688#usize) : Result (Array Std.U8 688#usize) := do
                                                                                             aspis_statement.pool_v1.pair_terminal.frontier_owned_reference_loop { start := 0#usize, «end» := 20#usize } afterstate output



def aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Result (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let r ← AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate afterstate
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 688#usize 0#u8
    let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output { «end» := 4#usize }
    let s1 ← lift (Array.to_slice aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ← Array.update output1 4#usize aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
    let output3 ← Array.update output2 5#usize aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
    let output4 ← Array.update output3 6#usize aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    let output5 ← Array.update output4 7#usize 1#u8
    let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5 { start := 8#usize, «end» := 16#usize }
    let a ← lift (core.num.U64.to_le_bytes afterstate.next_pair_index)
    let s4 ← lift (Array.to_slice a)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6 { start := 16#usize, «end» := 48#usize }
    let a1 ← AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical afterstate.next_root
    let s7 ← lift (Array.to_slice a1)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output7 := index_mut_back2 s8
    let output8 ← aspis_statement.pool_v1.pair_terminal.frontier_owned_reference afterstate output7
    ok (core.result.Result.Ok output8)
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array Std.U8 688#usize) (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual


def encode (afterstate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Result (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 afterstate

end AspisS6AfterstateLoopParent

#print axioms AspisS6AfterstateLoopParent.encode

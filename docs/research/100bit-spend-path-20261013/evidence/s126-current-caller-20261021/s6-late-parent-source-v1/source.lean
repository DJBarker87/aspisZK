import S6SnapshotLoopParentSourceV1
import S6AfterstateLoopParentSourceV1
import S6StdOptionSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error






noncomputable section

namespace AspisS6LateParent
open AspisS6FiveUnrolledCodec



impl_def core.option.Option.Insts.CoreCmpPartialEqOption {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T) (Option T) := {
  eq := AspisS6StdOptionMethods.option_eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption cmpPartialEqInst)
}


 def core.result.Result.map_err {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst : core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) : Result (core.result.Result T F) := do
                                                                      match self with
                                                                      | core.result.Result.Ok t => ok (core.result.Result.Ok t)
                                                                      | core.result.Result.Err e => let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
                                                                                                    ok (core.result.Result.Err t)


 def aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES : Std.Usize := 680#usize


 def aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : Result Std.Usize := 8#usize + aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES : Std.Usize := 800#usize


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC : Array Std.U8 8#usize := Array.make 8#usize [ 65#u8, 83#u8, 80#u8, 76#u8, 65#u8, 84#u8, 69#u8, 49#u8 ]


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION : Std.U8 := 1#u8


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT : Std.U8 := 2#u8


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES : Std.Usize := 32#usize


 def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES : Result Std.Usize := do let i ← aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES + aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
                                                                                                                                                                                                                                                 let i1 ← aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
                                                                                                                                                                                                                                                 i + i1



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once (c : aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1) (tupled_args : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : Result aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 := do
  ok (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Afterstate tupled_args)



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 : core.ops.function.FnOnce aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1 aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 := {
  call_once := aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once
}



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once (c : aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure) (tupled_args : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : Result aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 := do
  ok (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Snapshot tupled_args)



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 : core.ops.function.FnOnce aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 := {
  call_once := aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once
}



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 (statement : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) (output : Slice Std.U8) : Result ((core.result.Result Unit aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) × (Slice Std.U8)) := do
  let i := Slice.len output
  let i1 ← aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  if i != i1
  then ok (core.result.Result.Err aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongLength, output)
  else
    let o ← lift (U64.checked_add statement.live_snapshot.next_pair_index 1#u64)
    let b ← core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) o (some statement.candidate_afterstate.next_pair_index)
    if b
    then ok (core.result.Result.Err aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.AfterstateIndexMismatch, output)
    else
      let output1 ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output1 { «end» := 8#usize }
      let s1 ← lift (Array.to_slice aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
      let output4 ← Slice.update output3 9#usize aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 10#usize, «end» := 12#usize }
      let i2 ← lift (UScalar.cast .U16 aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES)
      let a ← lift (core.num.U16.to_le_bytes i2)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output5 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 12#usize, «end» := 16#usize }
      let i3 ← lift (UScalar.cast .U32 aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
      let a1 ← lift (core.num.U32.to_le_bytes i3)
      let s7 ← lift (Array.to_slice a1)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output6 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 16#usize, «end» := 20#usize }
      let i4 ← aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      let i5 ← lift (UScalar.cast .U32 i4)
      let a2 ← lift (core.num.U32.to_le_bytes i5)
      let s10 ← lift (Array.to_slice a2)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output7 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 20#usize, «end» := 24#usize }
      let i6 ← lift (UScalar.cast .U32 i1)
      let a3 ← lift (core.num.U32.to_le_bytes i6)
      let s13 ← lift (Array.to_slice a3)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output8 := index_mut_back4 s14
      let i7 ← 32#usize + aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output8 { start := 32#usize, «end» := i7 }
      let (r, s16) ← AspisS6SnapshotLoopParent.encode statement.live_snapshot s15
      let r1 ← core.result.Result.map_err aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let output9 := index_mut_back5 s16
        let r2 ← AspisS6AfterstateLoopParent.encode statement.candidate_afterstate
        let r3 ← core.result.Result.map_err aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r2 ()
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val => let (s17, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) output9 { start := i7 }
                                                            let s18 ← lift (Array.to_slice val)
                                                            let s19 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s17 s18
                                                            let output10 := index_mut_back6 s19
                                                            ok (core.result.Result.Ok (), output10)
        | core.ops.control_flow.ControlFlow.Break residual => let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                              ok (r4, output9)
      | core.ops.control_flow.ControlFlow.Break residual => let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                            let output9 := index_mut_back5 s16
                                                            ok (r2, output9)


def encode (statement : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) (output : Slice Std.U8) : Result ((core.result.Result Unit aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) × (Slice Std.U8)) := do
  aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 statement output

end AspisS6LateParent

#print axioms AspisS6LateParent.encode

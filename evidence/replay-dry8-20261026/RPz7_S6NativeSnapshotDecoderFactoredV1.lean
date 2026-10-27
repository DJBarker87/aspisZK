import RPz7_S6NativeSnapshotReadArrayV1
import Mathlib.Tactic.CongrExclamation
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS6NativeSnapshotDecoderFactored
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def part_16 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }
  let r52 ← AspisS6NativeSnapshotReadDigest.read_digest s21
  let r53 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()
  let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r53
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }
    let r55 ← AspisS6NativeSnapshotReadDigest.read_digest s22
    let r56 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()
    let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r56
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }
      let r58 ← AspisS6NativeSnapshotReadDigest.read_digest s23
      let r59 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()
      let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r59
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        let s24 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }
        let r61 ← AspisS6NativeSnapshotReadDigest.read_digest s24
        let r62 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()
        let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r62
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          let s25 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
          let a22 ← AspisS6NativeSnapshotReadArray.read_array 32#usize s25
          let s26 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
          let a23 ← AspisS6NativeSnapshotReadArray.read_array 32#usize s26
          let s27 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }
          let a24 ← AspisS6NativeSnapshotReadArray.read_array 8#usize s27
          let i9 ← lift (core.num.U64.from_le_bytes a24)
          let s28 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }
          let a25 ← AspisS6NativeSnapshotReadArray.read_array 8#usize s28
          let i10 ← lift (core.num.U64.from_le_bytes a25)
          let r67 ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
          let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r67
          match cf21 with
          | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def part_12 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize }
  let r40 ← AspisS6NativeSnapshotReadDigest.read_digest s17
  let r41 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ()
  let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r41
  match cf13 with
  | core.ops.control_flow.ControlFlow.Continue val13 =>
    let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize }
    let r43 ← AspisS6NativeSnapshotReadDigest.read_digest s18
    let r44 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ()
    let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r44
    match cf14 with
    | core.ops.control_flow.ControlFlow.Continue val14 =>
      let s19 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize }
      let r46 ← AspisS6NativeSnapshotReadDigest.read_digest s19
      let r47 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ()
      let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r47
      match cf15 with
      | core.ops.control_flow.ControlFlow.Continue val15 =>
        let s20 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize }
        let r49 ← AspisS6NativeSnapshotReadDigest.read_digest s20
        let r50 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ()
        let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r50
        match cf16 with
        | core.ops.control_flow.ControlFlow.Continue val16 =>
          part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def part_8 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }
  let r28 ← AspisS6NativeSnapshotReadDigest.read_digest s13
  let r29 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()
  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r29
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }
    let r31 ← AspisS6NativeSnapshotReadDigest.read_digest s14
    let r32 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()
    let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r32
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }
      let r34 ← AspisS6NativeSnapshotReadDigest.read_digest s15
      let r35 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()
      let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r35
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }
        let r37 ← AspisS6NativeSnapshotReadDigest.read_digest s16
        let r38 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()
        let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r38
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          part_12 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def part_4 (bytes : Slice U8) (val val1 val2 val3 val4 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }
  let r16 ← AspisS6NativeSnapshotReadDigest.read_digest s9
  let r17 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r17
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }
    let r19 ← AspisS6NativeSnapshotReadDigest.read_digest s10
    let r20 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()
    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r20
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }
      let r22 ← AspisS6NativeSnapshotReadDigest.read_digest s11
      let r23 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()
      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r23
      match cf7 with
      | core.ops.control_flow.ControlFlow.Continue val7 =>
        let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }
        let r25 ← AspisS6NativeSnapshotReadDigest.read_digest s12
        let r26 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()
        let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r26
        match cf8 with
        | core.ops.control_flow.ControlFlow.Continue val8 =>
          part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def part_0 (bytes : Slice U8) (val : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }
  let r4 ← AspisS6NativeSnapshotReadDigest.read_digest s5
  let r5 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }
    let r7 ← AspisS6NativeSnapshotReadDigest.read_digest s6
    let r8 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }
      let r10 ← AspisS6NativeSnapshotReadDigest.read_digest s7
      let r11 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r11
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }
        let r13 ← AspisS6NativeSnapshotReadDigest.read_digest s8
        let r14 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r14
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          part_4 bytes val val1 val2 val3 val4
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def decode (bytes : Slice U8) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic)
    else
      let i1 ← Slice.index_usize bytes 8#usize
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion)
      else
        let i2 ← Slice.index_usize bytes 9#usize
        if i2 != 0#u8
        then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
        else
          let i3 ← Slice.index_usize bytes 10#usize
          if i3 != 0#u8
          then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
          else
            let i4 ← Slice.index_usize bytes 11#usize
            if i4 != 0#u8
            then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
            else
              let i5 ← Slice.index_usize bytes 12#usize
              if i5 != 0#u8
              then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
              else
                let i6 ← Slice.index_usize bytes 13#usize
                if i6 != 0#u8
                then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                else
                  let i7 ← Slice.index_usize bytes 14#usize
                  if i7 != 0#u8
                  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                  else
                    let i8 ← Slice.index_usize bytes 15#usize
                    if i8 != 0#u8
                    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                    else
                      let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
                      let a ← pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
                      let s3 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }
                      let b1 ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3
                      if b1
                      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding)
                      else
                        let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }
                        let r1 ← AspisS6NativeSnapshotReadDigest.read_digest s4
                        let r2 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()
                        let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          part_0 bytes val
                        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual


def unpacked_part_16 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }
  let r51 ← core.array.TryFromSharedArraySlice.try_from 32#usize s21
  let a18 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51
  let r52 ← atomic_statement.decode_digest_canonical a18
  let r53 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()
  let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r53
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }
    let r54 ← core.array.TryFromSharedArraySlice.try_from 32#usize s22
    let a19 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54
    let r55 ← atomic_statement.decode_digest_canonical a19
    let r56 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()
    let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r56
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }
      let r57 ← core.array.TryFromSharedArraySlice.try_from 32#usize s23
      let a20 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57
      let r58 ← atomic_statement.decode_digest_canonical a20
      let r59 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()
      let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r59
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        let s24 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }
        let r60 ← core.array.TryFromSharedArraySlice.try_from 32#usize s24
        let a21 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60
        let r61 ← atomic_statement.decode_digest_canonical a21
        let r62 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()
        let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r62
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          let s25 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
          let r63 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25
          let a22 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63
          let s26 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
          let r64 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26
          let a23 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64
          let s27 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }
          let r65 ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27
          let a24 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65
          let i9 ← lift (core.num.U64.from_le_bytes a24)
          let s28 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }
          let r66 ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28
          let a25 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66
          let i10 ← lift (core.num.U64.from_le_bytes a25)
          let r67 ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
          let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r67
          match cf21 with
          | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def unpacked_part_12 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize }
  let r39 ← core.array.TryFromSharedArraySlice.try_from 32#usize s17
  let a14 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r39
  let r40 ← atomic_statement.decode_digest_canonical a14
  let r41 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ()
  let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r41
  match cf13 with
  | core.ops.control_flow.ControlFlow.Continue val13 =>
    let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize }
    let r42 ← core.array.TryFromSharedArraySlice.try_from 32#usize s18
    let a15 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r42
    let r43 ← atomic_statement.decode_digest_canonical a15
    let r44 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ()
    let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r44
    match cf14 with
    | core.ops.control_flow.ControlFlow.Continue val14 =>
      let s19 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize }
      let r45 ← core.array.TryFromSharedArraySlice.try_from 32#usize s19
      let a16 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r45
      let r46 ← atomic_statement.decode_digest_canonical a16
      let r47 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ()
      let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r47
      match cf15 with
      | core.ops.control_flow.ControlFlow.Continue val15 =>
        let s20 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize }
        let r48 ← core.array.TryFromSharedArraySlice.try_from 32#usize s20
        let a17 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r48
        let r49 ← atomic_statement.decode_digest_canonical a17
        let r50 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ()
        let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r50
        match cf16 with
        | core.ops.control_flow.ControlFlow.Continue val16 =>
          unpacked_part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def unpacked_part_8 (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }
  let r27 ← core.array.TryFromSharedArraySlice.try_from 32#usize s13
  let a10 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27
  let r28 ← atomic_statement.decode_digest_canonical a10
  let r29 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()
  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r29
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }
    let r30 ← core.array.TryFromSharedArraySlice.try_from 32#usize s14
    let a11 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30
    let r31 ← atomic_statement.decode_digest_canonical a11
    let r32 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()
    let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r32
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }
      let r33 ← core.array.TryFromSharedArraySlice.try_from 32#usize s15
      let a12 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33
      let r34 ← atomic_statement.decode_digest_canonical a12
      let r35 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()
      let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r35
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }
        let r36 ← core.array.TryFromSharedArraySlice.try_from 32#usize s16
        let a13 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36
        let r37 ← atomic_statement.decode_digest_canonical a13
        let r38 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()
        let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r38
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          unpacked_part_12 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def unpacked_part_4 (bytes : Slice U8) (val val1 val2 val3 val4 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }
  let r15 ← core.array.TryFromSharedArraySlice.try_from 32#usize s9
  let a6 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r15
  let r16 ← atomic_statement.decode_digest_canonical a6
  let r17 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r17
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }
    let r18 ← core.array.TryFromSharedArraySlice.try_from 32#usize s10
    let a7 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r18
    let r19 ← atomic_statement.decode_digest_canonical a7
    let r20 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()
    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r20
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }
      let r21 ← core.array.TryFromSharedArraySlice.try_from 32#usize s11
      let a8 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r21
      let r22 ← atomic_statement.decode_digest_canonical a8
      let r23 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()
      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r23
      match cf7 with
      | core.ops.control_flow.ControlFlow.Continue val7 =>
        let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }
        let r24 ← core.array.TryFromSharedArraySlice.try_from 32#usize s12
        let a9 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r24
        let r25 ← atomic_statement.decode_digest_canonical a9
        let r26 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()
        let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r26
        match cf8 with
        | core.ops.control_flow.ControlFlow.Continue val8 =>
          unpacked_part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def unpacked_part_0 (bytes : Slice U8) (val : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }
  let r3 ← core.array.TryFromSharedArraySlice.try_from 32#usize s5
  let a2 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3
  let r4 ← atomic_statement.decode_digest_canonical a2
  let r5 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }
    let r6 ← core.array.TryFromSharedArraySlice.try_from 32#usize s6
    let a3 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6
    let r7 ← atomic_statement.decode_digest_canonical a3
    let r8 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }
      let r9 ← core.array.TryFromSharedArraySlice.try_from 32#usize s7
      let a4 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9
      let r10 ← atomic_statement.decode_digest_canonical a4
      let r11 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r11
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }
        let r12 ← core.array.TryFromSharedArraySlice.try_from 32#usize s8
        let a5 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12
        let r13 ← atomic_statement.decode_digest_canonical a5
        let r14 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r14
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          unpacked_part_4 bytes val val1 val2 val3 val4
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

def unpacked_decode (bytes : Slice U8) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic)
    else
      let i1 ← Slice.index_usize bytes 8#usize
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion)
      else
        let i2 ← Slice.index_usize bytes 9#usize
        if i2 != 0#u8
        then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
        else
          let i3 ← Slice.index_usize bytes 10#usize
          if i3 != 0#u8
          then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
          else
            let i4 ← Slice.index_usize bytes 11#usize
            if i4 != 0#u8
            then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
            else
              let i5 ← Slice.index_usize bytes 12#usize
              if i5 != 0#u8
              then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
              else
                let i6 ← Slice.index_usize bytes 13#usize
                if i6 != 0#u8
                then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                else
                  let i7 ← Slice.index_usize bytes 14#usize
                  if i7 != 0#u8
                  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                  else
                    let i8 ← Slice.index_usize bytes 15#usize
                    if i8 != 0#u8
                    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                    else
                      let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
                      let a ← pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
                      let s3 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }
                      let b1 ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3
                      if b1
                      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding)
                      else
                        let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }
                        let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s4
                        let a1 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r
                        let r1 ← atomic_statement.decode_digest_canonical a1
                        let r2 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()
                        let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          unpacked_part_0 bytes val
                        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual


theorem part_16_eq (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array aspis_core.field.M31 8#usize) :
    part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16=unpacked_part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 := by
  unfold part_16 unpacked_part_16
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  try unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem part_12_eq (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array aspis_core.field.M31 8#usize) :
    part_12 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12=unpacked_part_12 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 := by
  unfold part_12 unpacked_part_12
  simp only [part_16_eq]
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  try unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem part_8_eq (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array aspis_core.field.M31 8#usize) :
    part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8=unpacked_part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8 := by
  unfold part_8 unpacked_part_8
  simp only [part_12_eq]
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  try unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem part_4_eq (bytes : Slice U8) (val val1 val2 val3 val4 : Array aspis_core.field.M31 8#usize) :
    part_4 bytes val val1 val2 val3 val4=unpacked_part_4 bytes val val1 val2 val3 val4 := by
  unfold part_4 unpacked_part_4
  simp only [part_8_eq]
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  try unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem part_0_eq (bytes : Slice U8) (val : Array aspis_core.field.M31 8#usize) :
    part_0 bytes val=unpacked_part_0 bytes val := by
  unfold part_0 unpacked_part_0
  simp only [part_4_eq]
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  try unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem unpacked_source (bytes : Slice U8) :
    unpacked_decode bytes=decode_pool_v1_pair_live_snapshot_v1 bytes := by
  unfold unpacked_decode decode_pool_v1_pair_live_snapshot_v1
  unfold unpacked_part_0 unpacked_part_4 unpacked_part_8 unpacked_part_12 unpacked_part_16
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem packed_unpacked (bytes : Slice U8) :
    decode bytes=unpacked_decode bytes := by
  unfold decode unpacked_decode
  simp only [part_0_eq]
  unfold AspisS6NativeSnapshotReadDigest.read_digest
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

theorem decode_source (bytes : Slice U8) :
    decode bytes=decode_pool_v1_pair_live_snapshot_v1 bytes :=
  (packed_unpacked bytes).trans (unpacked_source bytes)

#print axioms decode_source
end AspisS6NativeSnapshotDecoderFactored

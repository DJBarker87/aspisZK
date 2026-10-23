import S6FullSourceCodecV1
import Mathlib.Tactic.CongrExclamation
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS6SourceCodec.AfterstateFactored
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

def part_16 (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s19 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 560#usize, «end» := 592#usize }
  let r51 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s19
  let cf34 ← core.result.Result.Insts.CoreOpsTry.branch r51
  match cf34 with
  | core.ops.control_flow.ControlFlow.Continue val34 =>
    let r52 ← aspis_statement.atomic_statement.decode_digest_canonical val34
    let r53 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r52 ()
    let cf35 ← core.result.Result.Insts.CoreOpsTry.branch r53
    match cf35 with
    | core.ops.control_flow.ControlFlow.Continue val35 =>
      let s20 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 592#usize, «end» := 624#usize }
      let r54 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s20
      let cf36 ← core.result.Result.Insts.CoreOpsTry.branch r54
      match cf36 with
      | core.ops.control_flow.ControlFlow.Continue val36 =>
        let r55 ← aspis_statement.atomic_statement.decode_digest_canonical val36
        let r56 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r55 ()
        let cf37 ← core.result.Result.Insts.CoreOpsTry.branch r56
        match cf37 with
        | core.ops.control_flow.ControlFlow.Continue val37 =>
          let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 624#usize, «end» := 656#usize }
          let r57 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s21
          let cf38 ← core.result.Result.Insts.CoreOpsTry.branch r57
          match cf38 with
          | core.ops.control_flow.ControlFlow.Continue val38 =>
            let r58 ← aspis_statement.atomic_statement.decode_digest_canonical val38
            let r59 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r58 ()
            let cf39 ← core.result.Result.Insts.CoreOpsTry.branch r59
            match cf39 with
            | core.ops.control_flow.ControlFlow.Continue val39 =>
              let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 656#usize, «end» := 688#usize }
              let r60 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s22
              let cf40 ← core.result.Result.Insts.CoreOpsTry.branch r60
              match cf40 with
              | core.ops.control_flow.ControlFlow.Continue val40 =>
                let r61 ← aspis_statement.atomic_statement.decode_digest_canonical val40
                let r62 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r61 ()
                let cf41 ← core.result.Result.Insts.CoreOpsTry.branch r62
                match cf41 with
                | core.ops.control_flow.ControlFlow.Continue val41 =>
                  let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize }
                  let r63 ← aspis_statement.pool_v1.pair_terminal.exact 8#usize s23
                  let cf42 ← core.result.Result.Insts.CoreOpsTry.branch r63
                  match cf42 with
                  | core.ops.control_flow.ControlFlow.Continue val42 =>
                    let i6 ← lift (core.num.U64.from_le_bytes val42)
                    let r64 ← aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
                    let cf43 ← core.result.Result.Insts.CoreOpsTry.branch r64
                    match cf43 with
                    | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
                    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def part_12 (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize }
  let r39 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s15
  let cf26 ← core.result.Result.Insts.CoreOpsTry.branch r39
  match cf26 with
  | core.ops.control_flow.ControlFlow.Continue val26 =>
    let r40 ← aspis_statement.atomic_statement.decode_digest_canonical val26
    let r41 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ()
    let cf27 ← core.result.Result.Insts.CoreOpsTry.branch r41
    match cf27 with
    | core.ops.control_flow.ControlFlow.Continue val27 =>
      let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize }
      let r42 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s16
      let cf28 ← core.result.Result.Insts.CoreOpsTry.branch r42
      match cf28 with
      | core.ops.control_flow.ControlFlow.Continue val28 =>
        let r43 ← aspis_statement.atomic_statement.decode_digest_canonical val28
        let r44 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ()
        let cf29 ← core.result.Result.Insts.CoreOpsTry.branch r44
        match cf29 with
        | core.ops.control_flow.ControlFlow.Continue val29 =>
          let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize }
          let r45 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s17
          let cf30 ← core.result.Result.Insts.CoreOpsTry.branch r45
          match cf30 with
          | core.ops.control_flow.ControlFlow.Continue val30 =>
            let r46 ← aspis_statement.atomic_statement.decode_digest_canonical val30
            let r47 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ()
            let cf31 ← core.result.Result.Insts.CoreOpsTry.branch r47
            match cf31 with
            | core.ops.control_flow.ControlFlow.Continue val31 =>
              let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize }
              let r48 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s18
              let cf32 ← core.result.Result.Insts.CoreOpsTry.branch r48
              match cf32 with
              | core.ops.control_flow.ControlFlow.Continue val32 =>
                let r49 ← aspis_statement.atomic_statement.decode_digest_canonical val32
                let r50 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ()
                let cf33 ← core.result.Result.Insts.CoreOpsTry.branch r50
                match cf33 with
                | core.ops.control_flow.ControlFlow.Continue val33 =>
                  part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def part_8 (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize }
  let r27 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s11
  let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r27
  match cf18 with
  | core.ops.control_flow.ControlFlow.Continue val18 =>
    let r28 ← aspis_statement.atomic_statement.decode_digest_canonical val18
    let r29 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ()
    let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r29
    match cf19 with
    | core.ops.control_flow.ControlFlow.Continue val19 =>
      let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize }
      let r30 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s12
      let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r30
      match cf20 with
      | core.ops.control_flow.ControlFlow.Continue val20 =>
        let r31 ← aspis_statement.atomic_statement.decode_digest_canonical val20
        let r32 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ()
        let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r32
        match cf21 with
        | core.ops.control_flow.ControlFlow.Continue val21 =>
          let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize }
          let r33 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s13
          let cf22 ← core.result.Result.Insts.CoreOpsTry.branch r33
          match cf22 with
          | core.ops.control_flow.ControlFlow.Continue val22 =>
            let r34 ← aspis_statement.atomic_statement.decode_digest_canonical val22
            let r35 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ()
            let cf23 ← core.result.Result.Insts.CoreOpsTry.branch r35
            match cf23 with
            | core.ops.control_flow.ControlFlow.Continue val23 =>
              let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize }
              let r36 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s14
              let cf24 ← core.result.Result.Insts.CoreOpsTry.branch r36
              match cf24 with
              | core.ops.control_flow.ControlFlow.Continue val24 =>
                let r37 ← aspis_statement.atomic_statement.decode_digest_canonical val24
                let r38 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ()
                let cf25 ← core.result.Result.Insts.CoreOpsTry.branch r38
                match cf25 with
                | core.ops.control_flow.ControlFlow.Continue val25 =>
                  part_12 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def part_4 (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize }
  let r15 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s7
  let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r15
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val10 =>
    let r16 ← aspis_statement.atomic_statement.decode_digest_canonical val10
    let r17 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ()
    let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r17
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val11 =>
      let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize }
      let r18 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s8
      let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r18
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue val12 =>
        let r19 ← aspis_statement.atomic_statement.decode_digest_canonical val12
        let r20 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ()
        let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r20
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val13 =>
          let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize }
          let r21 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s9
          let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r21
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue val14 =>
            let r22 ← aspis_statement.atomic_statement.decode_digest_canonical val14
            let r23 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ()
            let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r23
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue val15 =>
              let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize }
              let r24 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s10
              let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r24
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue val16 =>
                let r25 ← aspis_statement.atomic_statement.decode_digest_canonical val16
                let r26 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ()
                let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r26
                match cf17 with
                | core.ops.control_flow.ControlFlow.Continue val17 =>
                  part_8 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def part_0 (bytes : Slice U8) (val1 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
  let r3 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s3
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let r4 ← aspis_statement.atomic_statement.decode_digest_canonical val2
    let r5 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r4 ()
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
      let r6 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s4
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val4 =>
        let r7 ← aspis_statement.atomic_statement.decode_digest_canonical val4
        let r8 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r7 ()
        let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r8
        match cf5 with
        | core.ops.control_flow.ControlFlow.Continue val5 =>
          let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 144#usize }
          let r9 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s5
          let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf6 with
          | core.ops.control_flow.ControlFlow.Continue val6 =>
            let r10 ← aspis_statement.atomic_statement.decode_digest_canonical val6
            let r11 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r10 ()
            let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r11
            match cf7 with
            | core.ops.control_flow.ControlFlow.Continue val7 =>
              let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 144#usize, «end» := 176#usize }
              let r12 ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s6
              let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf8 with
              | core.ops.control_flow.ControlFlow.Continue val8 =>
                let r13 ← aspis_statement.atomic_statement.decode_digest_canonical val8
                let r14 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ()
                let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r14
                match cf9 with
                | core.ops.control_flow.ControlFlow.Continue val9 =>
                  part_4 bytes val1 val3 val5 val7 val9
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def decode (bytes : Slice U8) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let i := Slice.len bytes
  let i1 ← aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  if i != i1
  then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
      then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        if i3 != aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
        then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat)
        else
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding)
          else
            let i5 ← Slice.index_usize bytes 7#usize
            if i5 != 1#u8
            then ok (core.result.Result.Err aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode)
            else
              let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
              let r ← aspis_statement.pool_v1.pair_terminal.exact 32#usize s2
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r1 ← aspis_statement.atomic_statement.decode_digest_canonical val
                let r2 ← core.result.Result.map_err aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  part_0 bytes val1
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual



/-- Full Result equality, including failure/divergence and all Rust errors.
Only beta-expanded Lean continuations differ; native carriers/callees are exact. -/
theorem decode_source (bytes : Slice U8) :
    decode bytes=decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  unfold decode decode_pool_v1_pair_verified_afterstate_v1
  unfold part_0 part_4 part_8 part_12 part_16
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisS6SourceCodec.AfterstateFactored." ||
          s.startsWith "AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  all_goals with_unfolding_none rfl

#print axioms decode_source
end AspisS6SourceCodec.AfterstateFactored

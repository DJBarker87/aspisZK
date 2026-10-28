import R1Z.PV_RunJoin_DecoderStage1629
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotChunk16
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s21 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize })
  let r51 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 32#usize s21)
  let a18 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51)
  let r52 ← R1Z.PV_RJDec_Parser03.program a18
  let r53 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ())
  let cf17 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r53)
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    let s22 ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize })
    let r54 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
        letI : ExternalFuns := ops
        core.array.TryFromSharedArraySlice.try_from 32#usize s22)
    let a19 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54)
    let r55 ← R1Z.PV_RJDec_Parser03.program a19
    let r56 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ())
    let cf18 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r56)
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      let s23 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize })
      let r57 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
          letI : ExternalFuns := ops
          core.array.TryFromSharedArraySlice.try_from 32#usize s23)
      let a20 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
          letI : ExternalFuns := ops
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57)
      let r58 ← R1Z.PV_RJDec_Parser03.program a20
      let r59 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ())
      let cf19 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r59)
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        let s24 ← invoke "core.slice.index.Slice.index" (fun ops =>
            letI : ExternalFuns := ops
            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize })
        let r60 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
            letI : ExternalFuns := ops
            core.array.TryFromSharedArraySlice.try_from 32#usize s24)
        let a21 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
            letI : ExternalFuns := ops
            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60)
        let r61 ← R1Z.PV_RJDec_Parser03.program a21
        let r62 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ())
        let cf20 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r62)
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          R1Z.PV_RJDec_SnapshotChunk20.program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize) :
  erase ops (program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16) = R1Z.PV_RunJoin_DecoderStage1629.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 := by
  unfold program R1Z.PV_RunJoin_DecoderStage1629.run
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s21
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r51
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro a18
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact R1Z.PV_RJDec_Parser03.source ops a18
        · intro r52
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r53
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf17
              try dsimp only
              cases cf17 with
              | Continue val17 =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s22
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r54
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro a19
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact R1Z.PV_RJDec_Parser03.source ops a19
                      · intro r55
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r56
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro cf18
                            try dsimp only
                            cases cf18 with
                            | Continue val18 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro s23
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro r57
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro a20
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact R1Z.PV_RJDec_Parser03.source ops a20
                                    · intro r58
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro r59
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro cf19
                                          try dsimp only
                                          cases cf19 with
                                          | Continue val19 =>
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro s24
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro r60
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro a21
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact R1Z.PV_RJDec_Parser03.source ops a21
                                                  · intro r61
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r62
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf20
                                                        try dsimp only
                                                        cases cf20 with
                                                        | Continue val20 =>
                                                          exact R1Z.PV_RJDec_SnapshotChunk20.source ops bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                                          | Break residual =>
                                            exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
              | Break residual =>
                exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_SnapshotChunk16

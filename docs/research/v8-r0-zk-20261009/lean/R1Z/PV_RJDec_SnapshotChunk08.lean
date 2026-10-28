import R1Z.PV_RunJoin_DecoderStage829
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
import R1Z.PV_RJDec_SnapshotChunk12
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotChunk08
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s13 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize })
  let r27 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 32#usize s13)
  let a10 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27)
  let r28 ← R1Z.PV_RJDec_Parser03.program a10
  let r29 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ())
  let cf9 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r29)
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    let s14 ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize })
    let r30 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
        letI : ExternalFuns := ops
        core.array.TryFromSharedArraySlice.try_from 32#usize s14)
    let a11 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30)
    let r31 ← R1Z.PV_RJDec_Parser03.program a11
    let r32 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ())
    let cf10 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r32)
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      let s15 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize })
      let r33 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
          letI : ExternalFuns := ops
          core.array.TryFromSharedArraySlice.try_from 32#usize s15)
      let a12 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
          letI : ExternalFuns := ops
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33)
      let r34 ← R1Z.PV_RJDec_Parser03.program a12
      let r35 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ())
      let cf11 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r35)
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        let s16 ← invoke "core.slice.index.Slice.index" (fun ops =>
            letI : ExternalFuns := ops
            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize })
        let r36 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
            letI : ExternalFuns := ops
            core.array.TryFromSharedArraySlice.try_from 32#usize s16)
        let a13 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
            letI : ExternalFuns := ops
            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36)
        let r37 ← R1Z.PV_RJDec_Parser03.program a13
        let r38 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ())
        let cf12 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r38)
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          R1Z.PV_RJDec_SnapshotChunk12.program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
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

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize) :
  erase ops (program bytes val val1 val2 val3 val4 val5 val6 val7 val8) = R1Z.PV_RunJoin_DecoderStage829.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 := by
  unfold program R1Z.PV_RunJoin_DecoderStage829.run
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s13
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r27
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro a10
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact R1Z.PV_RJDec_Parser03.source ops a10
        · intro r28
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r29
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf9
              try dsimp only
              cases cf9 with
              | Continue val9 =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s14
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r30
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro a11
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact R1Z.PV_RJDec_Parser03.source ops a11
                      · intro r31
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r32
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro cf10
                            try dsimp only
                            cases cf10 with
                            | Continue val10 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro s15
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro r33
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro a12
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact R1Z.PV_RJDec_Parser03.source ops a12
                                    · intro r34
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro r35
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro cf11
                                          try dsimp only
                                          cases cf11 with
                                          | Continue val11 =>
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro s16
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro r36
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro a13
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact R1Z.PV_RJDec_Parser03.source ops a13
                                                  · intro r37
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r38
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf12
                                                        try dsimp only
                                                        cases cf12 with
                                                        | Continue val12 =>
                                                          exact R1Z.PV_RJDec_SnapshotChunk12.source ops bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                                          | Break residual =>
                                            exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
              | Break residual =>
                exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_SnapshotChunk08

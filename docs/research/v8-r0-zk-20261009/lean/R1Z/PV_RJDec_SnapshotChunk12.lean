import R1Z.PV_RunJoin_DecoderStage1229
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotChunk12
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array U32 8#usize) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s17 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize })
  let r39 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 32#usize s17)
  let a14 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r39)
  let r40 ← R1Z.PV_RJDec_Parser03.program a14
  let r41 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ())
  let cf13 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r41)
  match cf13 with
  | core.ops.control_flow.ControlFlow.Continue val13 =>
    let s18 ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize })
    let r42 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromSharedArraySlice.try_from 32#usize s18)
    let a15 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r42)
    let r43 ← R1Z.PV_RJDec_Parser03.program a15
    let r44 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ())
    let cf14 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r44)
    match cf14 with
    | core.ops.control_flow.ControlFlow.Continue val14 =>
      let s19 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize })
      let r45 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.TryFromSharedArraySlice.try_from 32#usize s19)
      let a16 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r45)
      let r46 ← R1Z.PV_RJDec_Parser03.program a16
      let r47 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ())
      let cf15 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r47)
      match cf15 with
      | core.ops.control_flow.ControlFlow.Continue val15 =>
        let s20 ← invoke "core.slice.index.Slice.index" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize })
        let r48 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.array.TryFromSharedArraySlice.try_from 32#usize s20)
        let a17 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r48)
        let r49 ← R1Z.PV_RJDec_Parser03.program a17
        let r50 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ())
        let cf16 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r50)
        match cf16 with
        | core.ops.control_flow.ControlFlow.Continue val16 =>
          R1Z.PV_RJDec_SnapshotChunk16.program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array U32 8#usize) :
  erase ops (program bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12) = R1Z.PV_RunJoin_DecoderStage1229.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 := by
  unfold program R1Z.PV_RunJoin_DecoderStage1229.run
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s17
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r39
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro a14
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact R1Z.PV_RJDec_Parser03.source ops a14
        · intro r40
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r41
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf13
              try dsimp only
              cases cf13 with
              | Continue val13 =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s18
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r42
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro a15
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact R1Z.PV_RJDec_Parser03.source ops a15
                      · intro r43
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r44
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro cf14
                            try dsimp only
                            cases cf14 with
                            | Continue val14 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro s19
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro r45
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro a16
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact R1Z.PV_RJDec_Parser03.source ops a16
                                    · intro r46
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro r47
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro cf15
                                          try dsimp only
                                          cases cf15 with
                                          | Continue val15 =>
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro s20
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro r48
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro a17
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact R1Z.PV_RJDec_Parser03.source ops a17
                                                  · intro r49
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r50
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf16
                                                        try dsimp only
                                                        cases cf16 with
                                                        | Continue val16 =>
                                                          exact R1Z.PV_RJDec_SnapshotChunk16.source ops bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                                          | Break residual =>
                                            exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
              | Break residual =>
                exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_SnapshotChunk12

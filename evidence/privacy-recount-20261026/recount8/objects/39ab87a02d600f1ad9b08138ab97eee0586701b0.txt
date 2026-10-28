import R1Z.PV_RunJoin_DecoderStage029
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
import R1Z.PV_RJDec_SnapshotChunk12
import R1Z.PV_RJDec_SnapshotChunk08
import R1Z.PV_RJDec_SnapshotChunk04
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotChunk00
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def program (bytes : Slice U8) (val : Array U32 8#usize) : P (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s5 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize })
  let r3 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 32#usize s5)
  let a2 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3)
  let r4 ← R1Z.PV_RJDec_Parser03.program a2
  let r5 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ())
  let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r5)
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let s6 ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize })
    let r6 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.TryFromSharedArraySlice.try_from 32#usize s6)
    let a3 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6)
    let r7 ← R1Z.PV_RJDec_Parser03.program a3
    let r8 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ())
    let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r8)
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s7 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize })
      let r9 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.TryFromSharedArraySlice.try_from 32#usize s7)
      let a4 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9)
      let r10 ← R1Z.PV_RJDec_Parser03.program a4
      let r11 ← invoke "core.result.Result.map_err" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ())
      let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r11)
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let s8 ← invoke "core.slice.index.Slice.index" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize })
        let r12 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.array.TryFromSharedArraySlice.try_from 32#usize s8)
        let a5 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12)
        let r13 ← R1Z.PV_RJDec_Parser03.program a5
        let r14 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ())
        let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r14)
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          R1Z.PV_RJDec_SnapshotChunk04.program bytes val val1 val2 val3 val4
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

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val : Array U32 8#usize) :
  erase ops (program bytes val) = R1Z.PV_RunJoin_DecoderStage029.run bytes val := by
  unfold program R1Z.PV_RunJoin_DecoderStage029.run
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s5
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r3
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro a2
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact R1Z.PV_RJDec_Parser03.source ops a2
        · intro r4
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r5
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf1
              try dsimp only
              cases cf1 with
              | Continue val1 =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s6
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro r6
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro a3
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact R1Z.PV_RJDec_Parser03.source ops a3
                      · intro r7
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r8
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro cf2
                            try dsimp only
                            cases cf2 with
                            | Continue val2 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro s7
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro r9
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro a4
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact R1Z.PV_RJDec_Parser03.source ops a4
                                    · intro r10
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro r11
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro cf3
                                          try dsimp only
                                          cases cf3 with
                                          | Continue val3 =>
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro s8
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro r12
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro a5
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact R1Z.PV_RJDec_Parser03.source ops a5
                                                  · intro r13
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r14
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf4
                                                        try dsimp only
                                                        cases cf4 with
                                                        | Continue val4 =>
                                                          exact R1Z.PV_RJDec_SnapshotChunk04.source ops bytes val val1 val2 val3 val4
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                                          | Break residual =>
                                            exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
              | Break residual =>
                exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_SnapshotChunk00

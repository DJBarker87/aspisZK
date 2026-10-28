import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser09
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let s ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET, «end» := pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET })
  let r ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.TryFromSharedArraySlice.try_from 32#usize s)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        atomic_statement.decode_digest_canonical val)
    let r3 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1 r2 ())
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i ← invoke "pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET)
      let s1 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET, «end» := i })
      let r4 ← invoke "pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 s1)
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r4)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.MASTER_OFFSET, «end» := pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET })
        let r5 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s2)
        let r6 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r5 ())
        let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r6)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let s3 ← invoke "core.slice.index.Slice.index" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET, «end» := pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET })
          let r7 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s3)
          let r8 ← invoke "core.result.Result.map_err" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r7 ())
          let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r8)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s4 ← invoke "core.slice.index.Slice.index" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET, «end» := pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET })
            let r9 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s4)
            let r10 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r9 ())
            let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r10)
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i1 ← invoke "Slice.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Slice.index_usize bytes 7#usize)
              let s5 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET, «end» := pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET })
              let r11 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s5)
              let r12 ← invoke "core.result.Result.map_err" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r11 ())
              let cf6 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r12)
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let i2 ← invoke "lift" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    lift (core.num.U64.from_le_bytes val6))
                pure (core.result.Result.Ok { master_account := val3, checkpoint_account := val4, selected_lane_account := val5, output_lane := i1, checkpoint_sequence := i2, historical_global_anchor := val1, lane_transition := val2 })
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 bytes := by
  unfold program pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro r1
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro cf
          try dsimp only
          cases cf with
          | Continue val =>
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro r2
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
                · intro cf1
                  try dsimp only
                  cases cf1 with
                  | Continue val1 =>
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro i
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro s1
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r4
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
                              · intro s2
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
                                  · intro r6
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
                                        · intro s3
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact erase_invoke ops _ _
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
                                              · intro cf4
                                                try dsimp only
                                                cases cf4 with
                                                | Continue val4 =>
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro s4
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
                                                      · intro r10
                                                        try dsimp only
                                                        rw [erase_bind]
                                                        apply PV_W_RecursiveLaws.bind_congr
                                                        ·
                                                          exact erase_invoke ops _ _
                                                        · intro cf5
                                                          try dsimp only
                                                          cases cf5 with
                                                          | Continue val5 =>
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · intro i1
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
                                                                · intro r11
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
                                                                    · intro cf6
                                                                      try dsimp only
                                                                      cases cf6 with
                                                                      | Continue val6 =>
                                                                        try dsimp only
                                                                        rw [erase_bind]
                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                        ·
                                                                          exact erase_invoke ops _ _
                                                                        · intro i2
                                                                          rfl
                                                                      | Break residual =>
                                                                        exact erase_invoke ops _ _
                                                          | Break residual =>
                                                            exact erase_invoke ops _ _
                                                | Break residual =>
                                                  exact erase_invoke ops _ _
                                      | Break residual =>
                                        exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
                  | Break residual =>
                    exact erase_invoke ops _ _
          | Break residual =>
            exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser09

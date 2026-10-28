import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
import R1Z.PV_RJDec_SnapshotChunk12
import R1Z.PV_RJDec_SnapshotChunk08
import R1Z.PV_RJDec_SnapshotChunk04
import R1Z.PV_RJDec_SnapshotChunk00
import R1Z.PV_RJDec_AfterChunk41
import R1Z.PV_RJDec_AfterChunk33
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AfterChunk25
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def reference (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array U32 8#usize) : Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize }
  let r39 ← pool_v1.pair_terminal.exact 32#usize s15
  let cf26 ← core.result.Result.Insts.CoreOpsTry.branch r39
  match cf26 with
  | core.ops.control_flow.ControlFlow.Continue val26 =>
    let r40 ← atomic_statement.decode_digest_canonical val26
    let r41 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ()
    let cf27 ← core.result.Result.Insts.CoreOpsTry.branch r41
    match cf27 with
    | core.ops.control_flow.ControlFlow.Continue val27 =>
      let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize }
      let r42 ← pool_v1.pair_terminal.exact 32#usize s16
      let cf28 ← core.result.Result.Insts.CoreOpsTry.branch r42
      match cf28 with
      | core.ops.control_flow.ControlFlow.Continue val28 =>
        let r43 ← atomic_statement.decode_digest_canonical val28
        let r44 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ()
        let cf29 ← core.result.Result.Insts.CoreOpsTry.branch r44
        match cf29 with
        | core.ops.control_flow.ControlFlow.Continue val29 =>
          let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize }
          let r45 ← pool_v1.pair_terminal.exact 32#usize s17
          let cf30 ← core.result.Result.Insts.CoreOpsTry.branch r45
          match cf30 with
          | core.ops.control_flow.ControlFlow.Continue val30 =>
            let r46 ← atomic_statement.decode_digest_canonical val30
            let r47 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ()
            let cf31 ← core.result.Result.Insts.CoreOpsTry.branch r47
            match cf31 with
            | core.ops.control_flow.ControlFlow.Continue val31 =>
              let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize }
              let r48 ← pool_v1.pair_terminal.exact 32#usize s18
              let cf32 ← core.result.Result.Insts.CoreOpsTry.branch r48
              match cf32 with
              | core.ops.control_flow.ControlFlow.Continue val32 =>
                let r49 ← atomic_statement.decode_digest_canonical val32
                let r50 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ()
                let cf33 ← core.result.Result.Insts.CoreOpsTry.branch r50
                match cf33 with
                | core.ops.control_flow.ControlFlow.Continue val33 =>
                  R1Z.PV_RJDec_AfterChunk33.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def program (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array U32 8#usize) : P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s15 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize })
  let r39 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_terminal.exact 32#usize s15)
  let cf26 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r39)
  match cf26 with
  | core.ops.control_flow.ControlFlow.Continue val26 =>
    let r40 ← R1Z.PV_RJDec_Parser03.program val26
    let r41 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ())
    let cf27 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r41)
    match cf27 with
    | core.ops.control_flow.ControlFlow.Continue val27 =>
      let s16 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize })
      let r42 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          pool_v1.pair_terminal.exact 32#usize s16)
      let cf28 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r42)
      match cf28 with
      | core.ops.control_flow.ControlFlow.Continue val28 =>
        let r43 ← R1Z.PV_RJDec_Parser03.program val28
        let r44 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ())
        let cf29 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r44)
        match cf29 with
        | core.ops.control_flow.ControlFlow.Continue val29 =>
          let s17 ← invoke "core.slice.index.Slice.index" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize })
          let r45 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              pool_v1.pair_terminal.exact 32#usize s17)
          let cf30 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r45)
          match cf30 with
          | core.ops.control_flow.ControlFlow.Continue val30 =>
            let r46 ← R1Z.PV_RJDec_Parser03.program val30
            let r47 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ())
            let cf31 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r47)
            match cf31 with
            | core.ops.control_flow.ControlFlow.Continue val31 =>
              let s18 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize })
              let r48 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.pair_terminal.exact 32#usize s18)
              let cf32 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r48)
              match cf32 with
              | core.ops.control_flow.ControlFlow.Continue val32 =>
                let r49 ← R1Z.PV_RJDec_Parser03.program val32
                let r50 ← invoke "core.result.Result.map_err" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ())
                let cf33 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r50)
                match cf33 with
                | core.ops.control_flow.ControlFlow.Continue val33 =>
                  R1Z.PV_RJDec_AfterChunk33.program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array U32 8#usize) :
  erase ops (program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25) = R1Z.PV_RJDec_AfterChunk25.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 := by
  unfold program R1Z.PV_RJDec_AfterChunk25.reference
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
    · intro r39
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf26
        try dsimp only
        cases cf26 with
        | Continue val26 =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact R1Z.PV_RJDec_Parser03.source ops val26
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
              · intro cf27
                try dsimp only
                cases cf27 with
                | Continue val27 =>
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
                    · intro r42
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro cf28
                        try dsimp only
                        cases cf28 with
                        | Continue val28 =>
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact R1Z.PV_RJDec_Parser03.source ops val28
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
                              · intro cf29
                                try dsimp only
                                cases cf29 with
                                | Continue val29 =>
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
                                    · intro r45
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro cf30
                                        try dsimp only
                                        cases cf30 with
                                        | Continue val30 =>
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact R1Z.PV_RJDec_Parser03.source ops val30
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
                                              · intro cf31
                                                try dsimp only
                                                cases cf31 with
                                                | Continue val31 =>
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
                                                    · intro r48
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf32
                                                        try dsimp only
                                                        cases cf32 with
                                                        | Continue val32 =>
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact R1Z.PV_RJDec_Parser03.source ops val32
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
                                                              · intro cf33
                                                                try dsimp only
                                                                cases cf33 with
                                                                | Continue val33 =>
                                                                  exact R1Z.PV_RJDec_AfterChunk33.source ops bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
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
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_AfterChunk25

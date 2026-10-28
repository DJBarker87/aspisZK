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
import R1Z.PV_RJDec_AfterChunk25
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AfterChunk17
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def reference (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array U32 8#usize) : Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize }
  let r27 ← pool_v1.pair_terminal.exact 32#usize s11
  let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r27
  match cf18 with
  | core.ops.control_flow.ControlFlow.Continue val18 =>
    let r28 ← atomic_statement.decode_digest_canonical val18
    let r29 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ()
    let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r29
    match cf19 with
    | core.ops.control_flow.ControlFlow.Continue val19 =>
      let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize }
      let r30 ← pool_v1.pair_terminal.exact 32#usize s12
      let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r30
      match cf20 with
      | core.ops.control_flow.ControlFlow.Continue val20 =>
        let r31 ← atomic_statement.decode_digest_canonical val20
        let r32 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ()
        let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r32
        match cf21 with
        | core.ops.control_flow.ControlFlow.Continue val21 =>
          let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize }
          let r33 ← pool_v1.pair_terminal.exact 32#usize s13
          let cf22 ← core.result.Result.Insts.CoreOpsTry.branch r33
          match cf22 with
          | core.ops.control_flow.ControlFlow.Continue val22 =>
            let r34 ← atomic_statement.decode_digest_canonical val22
            let r35 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ()
            let cf23 ← core.result.Result.Insts.CoreOpsTry.branch r35
            match cf23 with
            | core.ops.control_flow.ControlFlow.Continue val23 =>
              let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize }
              let r36 ← pool_v1.pair_terminal.exact 32#usize s14
              let cf24 ← core.result.Result.Insts.CoreOpsTry.branch r36
              match cf24 with
              | core.ops.control_flow.ControlFlow.Continue val24 =>
                let r37 ← atomic_statement.decode_digest_canonical val24
                let r38 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ()
                let cf25 ← core.result.Result.Insts.CoreOpsTry.branch r38
                match cf25 with
                | core.ops.control_flow.ControlFlow.Continue val25 =>
                  R1Z.PV_RJDec_AfterChunk25.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def program (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array U32 8#usize) : P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s11 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize })
  let r27 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
      letI : ExternalFuns := ops
      pool_v1.pair_terminal.exact 32#usize s11)
  let cf18 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r27)
  match cf18 with
  | core.ops.control_flow.ControlFlow.Continue val18 =>
    let r28 ← R1Z.PV_RJDec_Parser03.program val18
    let r29 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ())
    let cf19 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r29)
    match cf19 with
    | core.ops.control_flow.ControlFlow.Continue val19 =>
      let s12 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize })
      let r30 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
          letI : ExternalFuns := ops
          pool_v1.pair_terminal.exact 32#usize s12)
      let cf20 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r30)
      match cf20 with
      | core.ops.control_flow.ControlFlow.Continue val20 =>
        let r31 ← R1Z.PV_RJDec_Parser03.program val20
        let r32 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ())
        let cf21 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r32)
        match cf21 with
        | core.ops.control_flow.ControlFlow.Continue val21 =>
          let s13 ← invoke "core.slice.index.Slice.index" (fun ops =>
              letI : ExternalFuns := ops
              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize })
          let r33 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
              letI : ExternalFuns := ops
              pool_v1.pair_terminal.exact 32#usize s13)
          let cf22 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r33)
          match cf22 with
          | core.ops.control_flow.ControlFlow.Continue val22 =>
            let r34 ← R1Z.PV_RJDec_Parser03.program val22
            let r35 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ())
            let cf23 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r35)
            match cf23 with
            | core.ops.control_flow.ControlFlow.Continue val23 =>
              let s14 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize })
              let r36 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                  letI : ExternalFuns := ops
                  pool_v1.pair_terminal.exact 32#usize s14)
              let cf24 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r36)
              match cf24 with
              | core.ops.control_flow.ControlFlow.Continue val24 =>
                let r37 ← R1Z.PV_RJDec_Parser03.program val24
                let r38 ← invoke "core.result.Result.map_err" (fun ops =>
                    letI : ExternalFuns := ops
                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ())
                let cf25 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r38)
                match cf25 with
                | core.ops.control_flow.ControlFlow.Continue val25 =>
                  R1Z.PV_RJDec_AfterChunk25.program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array U32 8#usize) :
  erase ops (program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17) = R1Z.PV_RJDec_AfterChunk17.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 := by
  unfold program R1Z.PV_RJDec_AfterChunk17.reference
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s11
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
      · intro cf18
        try dsimp only
        cases cf18 with
        | Continue val18 =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact R1Z.PV_RJDec_Parser03.source ops val18
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
              · intro cf19
                try dsimp only
                cases cf19 with
                | Continue val19 =>
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro s12
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
                      · intro cf20
                        try dsimp only
                        cases cf20 with
                        | Continue val20 =>
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact R1Z.PV_RJDec_Parser03.source ops val20
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
                              · intro cf21
                                try dsimp only
                                cases cf21 with
                                | Continue val21 =>
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
                                    · intro r33
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro cf22
                                        try dsimp only
                                        cases cf22 with
                                        | Continue val22 =>
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact R1Z.PV_RJDec_Parser03.source ops val22
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
                                              · intro cf23
                                                try dsimp only
                                                cases cf23 with
                                                | Continue val23 =>
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
                                                    · intro r36
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf24
                                                        try dsimp only
                                                        cases cf24 with
                                                        | Continue val24 =>
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact R1Z.PV_RJDec_Parser03.source ops val24
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
                                                              · intro cf25
                                                                try dsimp only
                                                                cases cf25 with
                                                                | Continue val25 =>
                                                                  exact R1Z.PV_RJDec_AfterChunk25.source ops bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
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
end R1Z.PV_RJDec_AfterChunk17

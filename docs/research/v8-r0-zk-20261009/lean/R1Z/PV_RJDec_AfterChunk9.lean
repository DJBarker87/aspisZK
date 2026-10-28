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
import R1Z.PV_RJDec_AfterChunk17
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AfterChunk9
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def reference (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array U32 8#usize) : Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize }
  let r15 ← pool_v1.pair_terminal.exact 32#usize s7
  let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r15
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val10 =>
    let r16 ← atomic_statement.decode_digest_canonical val10
    let r17 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ()
    let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r17
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val11 =>
      let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize }
      let r18 ← pool_v1.pair_terminal.exact 32#usize s8
      let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r18
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue val12 =>
        let r19 ← atomic_statement.decode_digest_canonical val12
        let r20 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ()
        let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r20
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val13 =>
          let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize }
          let r21 ← pool_v1.pair_terminal.exact 32#usize s9
          let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r21
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue val14 =>
            let r22 ← atomic_statement.decode_digest_canonical val14
            let r23 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ()
            let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r23
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue val15 =>
              let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize }
              let r24 ← pool_v1.pair_terminal.exact 32#usize s10
              let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r24
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue val16 =>
                let r25 ← atomic_statement.decode_digest_canonical val16
                let r26 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ()
                let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r26
                match cf17 with
                | core.ops.control_flow.ControlFlow.Continue val17 =>
                  R1Z.PV_RJDec_AfterChunk17.reference bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def program (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array U32 8#usize) : P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let s7 ← invoke "core.slice.index.Slice.index" (fun ops =>
      letI : ExternalFuns := ops
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize })
  let r15 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
      letI : ExternalFuns := ops
      pool_v1.pair_terminal.exact 32#usize s7)
  let cf10 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r15)
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val10 =>
    let r16 ← R1Z.PV_RJDec_Parser03.program val10
    let r17 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ())
    let cf11 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r17)
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val11 =>
      let s8 ← invoke "core.slice.index.Slice.index" (fun ops =>
          letI : ExternalFuns := ops
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize })
      let r18 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
          letI : ExternalFuns := ops
          pool_v1.pair_terminal.exact 32#usize s8)
      let cf12 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r18)
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue val12 =>
        let r19 ← R1Z.PV_RJDec_Parser03.program val12
        let r20 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ())
        let cf13 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r20)
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val13 =>
          let s9 ← invoke "core.slice.index.Slice.index" (fun ops =>
              letI : ExternalFuns := ops
              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize })
          let r21 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
              letI : ExternalFuns := ops
              pool_v1.pair_terminal.exact 32#usize s9)
          let cf14 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r21)
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue val14 =>
            let r22 ← R1Z.PV_RJDec_Parser03.program val14
            let r23 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ())
            let cf15 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r23)
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue val15 =>
              let s10 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize })
              let r24 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                  letI : ExternalFuns := ops
                  pool_v1.pair_terminal.exact 32#usize s10)
              let cf16 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r24)
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue val16 =>
                let r25 ← R1Z.PV_RJDec_Parser03.program val16
                let r26 ← invoke "core.result.Result.map_err" (fun ops =>
                    letI : ExternalFuns := ops
                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ())
                let cf17 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r26)
                match cf17 with
                | core.ops.control_flow.ControlFlow.Continue val17 =>
                  R1Z.PV_RJDec_AfterChunk17.program bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
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

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array U32 8#usize) :
  erase ops (program bytes val1 val3 val5 val7 val9) = R1Z.PV_RJDec_AfterChunk9.reference bytes val1 val3 val5 val7 val9 := by
  unfold program R1Z.PV_RJDec_AfterChunk9.reference
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
    · intro r15
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
            exact R1Z.PV_RJDec_Parser03.source ops val10
          · intro r16
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro r17
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
                  · intro s8
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro r18
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro cf12
                        try dsimp only
                        cases cf12 with
                        | Continue val12 =>
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact R1Z.PV_RJDec_Parser03.source ops val12
                          · intro r19
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro r20
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
                                  · intro s9
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro r21
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
                                            exact R1Z.PV_RJDec_Parser03.source ops val14
                                          · intro r22
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro r23
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
                                                  · intro s10
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro r24
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf16
                                                        try dsimp only
                                                        cases cf16 with
                                                        | Continue val16 =>
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact R1Z.PV_RJDec_Parser03.source ops val16
                                                          · intro r25
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · intro r26
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro cf17
                                                                try dsimp only
                                                                cases cf17 with
                                                                | Continue val17 =>
                                                                  exact R1Z.PV_RJDec_AfterChunk17.source ops bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
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
end R1Z.PV_RJDec_AfterChunk9

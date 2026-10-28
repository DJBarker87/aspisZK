import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser20
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let i := Slice.len bytes
  let i1 ← invoke "pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES)
  if i != i1 then
    pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize })
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC { start := 0#usize, «end» := 4#usize })
    let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
    if b then
      pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← invoke "Slice.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Slice.index_usize bytes 4#usize)
      if i2 != pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION then
        pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i3 ← invoke "Slice.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Slice.index_usize bytes 5#usize)
        let r ← invoke "pool_v1.pair_forest_terminal.transition_kind" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            pool_v1.pair_forest_terminal.transition_kind i3)
        let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r)
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i4 ← invoke "Slice.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Slice.index_usize bytes 6#usize)
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION then
            pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let r1 ← invoke "pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 bytes)
            let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r1)
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              match val with
              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer =>
                let i5 ← invoke "pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET)
                let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 })
                let r2 ← invoke "pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1 val1 s2)
                let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r2)
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 =>
                  let r3 ← invoke "pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 val2)
                  let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTry.branch r3)
                  match cf3 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    pure (core.result.Result.Ok val2)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal =>
                let i5 ← invoke "pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET)
                let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 })
                let r2 ← invoke "pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1 val1 s2)
                let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r2)
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 =>
                  let r3 ← invoke "pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 val2)
                  let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTry.branch r3)
                  match cf3 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    pure (core.result.Result.Ok val2)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes := by
  unfold program pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
  try dsimp only
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i1
    try dsimp only
    apply PV_W_IfLaws.erase_if_congr
    ·
      rfl
    ·
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
        · intro s1
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro b
            try dsimp only
            apply PV_W_IfLaws.erase_if_congr
            ·
              rfl
            ·
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro i2
                try dsimp only
                apply PV_W_IfLaws.erase_if_congr
                ·
                  rfl
                ·
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro i3
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
                      · intro cf
                        try dsimp only
                        cases cf with
                        | Continue val =>
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro i4
                            try dsimp only
                            apply PV_W_IfLaws.erase_if_congr
                            ·
                              rfl
                            ·
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
                                · intro cf1
                                  try dsimp only
                                  cases cf1 with
                                  | Continue val1 =>
                                    try dsimp only
                                    cases val with
                                    | PrivateTransfer =>
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro i5
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
                                          · intro r2
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
                                                · intro r3
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro cf3
                                                    try dsimp only
                                                    cases cf3 with
                                                    | Continue unused0_0 =>
                                                      rfl
                                                    | Break residual =>
                                                      exact erase_invoke ops _ _
                                              | Break residual =>
                                                exact erase_invoke ops _ _
                                    | Withdrawal =>
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro i5
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
                                          · intro r2
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
                                                · intro r3
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro cf3
                                                    try dsimp only
                                                    cases cf3 with
                                                    | Continue unused0_0 =>
                                                      rfl
                                                    | Break residual =>
                                                      exact erase_invoke ops _ _
                                              | Break residual =>
                                                exact erase_invoke ops _ _
                                  | Break residual =>
                                    exact erase_invoke ops _ _
                        | Break residual =>
                          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser20

import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser21
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (statement : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
  P (core.result.Result Unit pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let common ← invoke "pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement)
  let a := Array.repeat 32#usize 0#u8
  let b ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.master_account a)
  if b then
    pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.checkpoint_account a1)
    if b1 then
      pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
    else
      let a2 := Array.repeat 32#usize 0#u8
      let b2 ← invoke "core.array.equality.PartialEqArray.eq" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.selected_lane_account a2)
      if b2 then
        pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
      else
        let i ← invoke "lift" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            lift (core.convert.num.FromUsizeU8.from common.output_lane))
        if i >= pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT then
          pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidOutputLane)
        else
          match statement with
          | pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer _ public1 =>
            let r ← invoke "pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 public1)
            let r1 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r ())
            let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r1)
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let (pool, deployment, anchor_sequence, anchor, nullifier, _) ← invoke "pool_v1.pair_forest_terminal.statement_public_common" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.pair_forest_terminal.statement_public_common statement)
              let b3 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool common.master_account)
              if b3 then
                pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
              else
                let b4 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 deployment common.lane_transition.live_snapshot.deployment_domain)
                if b4 then
                  pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
                else
                  let b5 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 common.lane_transition.live_snapshot.pool common.master_account)
                  if b5 then
                    pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
                  else
                    if anchor_sequence != common.checkpoint_sequence then
                      pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
                    else
                      let b6 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor common.historical_global_anchor)
                      if b6 then
                        pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
                      else
                        let r2 ← invoke "pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 nullifier)
                        let r3 ← invoke "core.result.Result.map_err" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 r2 ())
                        let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTry.branch r3)
                        match cf1 with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          if val != common.output_lane then
                            pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                          else
                            let late_bytes := Array.repeat 1520#usize 0#u8
                            let (s, _) ← invoke "lift" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                lift (Array.to_slice_mut late_bytes))
                            let (r4, _) ← invoke "pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 common.lane_transition s)
                            let r5 ← invoke "core.result.Result.map_err" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r4 ())
                            let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTry.branch r5)
                            match cf2 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              pure (core.result.Result.Ok ())
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
          | pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal _ public1 =>
            let r ← invoke "pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 public1)
            let r1 ← invoke "core.result.Result.map_err" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r ())
            let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r1)
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let (pool, deployment, anchor_sequence, anchor, nullifier, _) ← invoke "pool_v1.pair_forest_terminal.statement_public_common" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.pair_forest_terminal.statement_public_common statement)
              let b3 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool common.master_account)
              if b3 then
                pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
              else
                let b4 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 deployment common.lane_transition.live_snapshot.deployment_domain)
                if b4 then
                  pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
                else
                  let b5 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 common.lane_transition.live_snapshot.pool common.master_account)
                  if b5 then
                    pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
                  else
                    if anchor_sequence != common.checkpoint_sequence then
                      pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
                    else
                      let b6 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor common.historical_global_anchor)
                      if b6 then
                        pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
                      else
                        let r2 ← invoke "pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 nullifier)
                        let r3 ← invoke "core.result.Result.map_err" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 r2 ())
                        let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTry.branch r3)
                        match cf1 with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          if val != common.output_lane then
                            pure (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                          else
                            let late_bytes := Array.repeat 1520#usize 0#u8
                            let (s, _) ← invoke "lift" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                lift (Array.to_slice_mut late_bytes))
                            let (r4, _) ← invoke "pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 common.lane_transition s)
                            let r5 ← invoke "core.result.Result.map_err" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r4 ())
                            let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTry.branch r5)
                            match cf2 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              pure (core.result.Result.Ok ())
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (statement : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
  erase ops (program statement) =
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement := by
  unfold program pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro common
    try dsimp only
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
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro b1
          try dsimp only
          apply PV_W_IfLaws.erase_if_congr
          ·
            rfl
          ·
            try dsimp only
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro b2
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
                · intro i
                  try dsimp only
                  apply PV_W_IfLaws.erase_if_congr
                  ·
                    rfl
                  ·
                    try dsimp only
                    cases statement with
                    | PrivateTransfer unused0_0 public1 =>
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
                            | Continue unused0_0 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · rintro ⟨pool, deployment, anchor_sequence, anchor, nullifier, _⟩
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro b3
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
                                    · intro b4
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
                                        · intro b5
                                          try dsimp only
                                          apply PV_W_IfLaws.erase_if_congr
                                          ·
                                            rfl
                                          ·
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
                                              · intro b6
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
                                                        | Continue val =>
                                                          try dsimp only
                                                          apply PV_W_IfLaws.erase_if_congr
                                                          ·
                                                            rfl
                                                          ·
                                                            try dsimp only
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · rintro ⟨s, _⟩
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · rintro ⟨r4, _⟩
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
                                                                  · intro cf2
                                                                    try dsimp only
                                                                    cases cf2 with
                                                                    | Continue unused0_0 =>
                                                                      rfl
                                                                    | Break residual =>
                                                                      exact erase_invoke ops _ _
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _
                    | Withdrawal unused1_0 public1 =>
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
                            | Continue unused0_0 =>
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · rintro ⟨pool, deployment, anchor_sequence, anchor, nullifier, _⟩
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro b3
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
                                    · intro b4
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
                                        · intro b5
                                          try dsimp only
                                          apply PV_W_IfLaws.erase_if_congr
                                          ·
                                            rfl
                                          ·
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
                                              · intro b6
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
                                                        | Continue val =>
                                                          try dsimp only
                                                          apply PV_W_IfLaws.erase_if_congr
                                                          ·
                                                            rfl
                                                          ·
                                                            try dsimp only
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · rintro ⟨s, _⟩
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · rintro ⟨r4, _⟩
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
                                                                  · intro cf2
                                                                    try dsimp only
                                                                    cases cf2 with
                                                                    | Continue unused0_0 =>
                                                                      rfl
                                                                    | Break residual =>
                                                                      exact erase_invoke ops _ _
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser21

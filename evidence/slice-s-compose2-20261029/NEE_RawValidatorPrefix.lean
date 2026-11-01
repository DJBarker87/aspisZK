import NEE_ValidatorBindings
set_option autoImplicit false
noncomputable section
namespace NEE_RawValidatorPrefix
open Aeneas Aeneas.Std Result AspisR1AdapterReconstruct NED_ErrorCarriers
abbrev RawStatement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev RawCommon := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev R := Result (core.result.Result Unit NED_RawValidatorControl.E)

def continuation (statement : RawStatement) (common : RawCommon) : R := do
  match statement with
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    _ public1 =>
    let r ←
      aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
        public1
    let r1 ←
      core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (pool, deployment, anchor_sequence, anchor, nullifier, _) ←
        aspis_statement.pool_v1.pair_forest_terminal.statement_public_common
          statement
      let b3 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool
          common.master_account
      if b3
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
      else
        let b4 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            deployment
            common.lane_transition.live_snapshot.deployment_domain
        if b4
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
        else
          let b5 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              common.lane_transition.live_snapshot.pool
              common.master_account
          if b5
          then
            ok (core.result.Result.Err
              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
          else
            if anchor_sequence != common.checkpoint_sequence
            then
              ok (core.result.Result.Err
                aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
            else
              let b6 ←
                core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor
                  common.historical_global_anchor
              if b6
              then
                ok (core.result.Result.Err
                  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
              else
                let r2 ←
                  aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
                    nullifier
                let r3 ←
                  core.result.Result.map_err
                    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
                    r2 ()
                let cf1 ←
                  core.result.Result.Insts.CoreOpsTry.branch r3
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  if val != common.output_lane
                  then
                    ok (core.result.Result.Err
                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                  else
                    let late_bytes := Array.repeat 1520#usize 0#u8
                    let (s, _) ← lift (Array.to_slice_mut late_bytes)
                    let (r4, _) ←
                      aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
                        common.lane_transition s
                    let r5 ←
                      core.result.Result.map_err
                        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r4 ()
                    let cf2 ←
                      core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf2 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      ok (core.result.Result.Ok ())
                    | core.ops.control_flow.ControlFlow.Break residual
                      =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    _ public1 =>
    let r ←
      aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
        public1
    let r1 ←
      core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (pool, deployment, anchor_sequence, anchor, nullifier, _) ←
        aspis_statement.pool_v1.pair_forest_terminal.statement_public_common
          statement
      let b3 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool
          common.master_account
      if b3
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
      else
        let b4 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            deployment
            common.lane_transition.live_snapshot.deployment_domain
        if b4
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
        else
          let b5 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              common.lane_transition.live_snapshot.pool
              common.master_account
          if b5
          then
            ok (core.result.Result.Err
              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
          else
            if anchor_sequence != common.checkpoint_sequence
            then
              ok (core.result.Result.Err
                aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
            else
              let b6 ←
                core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor
                  common.historical_global_anchor
              if b6
              then
                ok (core.result.Result.Err
                  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
              else
                let r2 ←
                  aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
                    nullifier
                let r3 ←
                  core.result.Result.map_err
                    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
                    r2 ()
                let cf1 ←
                  core.result.Result.Insts.CoreOpsTry.branch r3
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  if val != common.output_lane
                  then
                    ok (core.result.Result.Err
                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
                  else
                    let late_bytes := Array.repeat 1520#usize 0#u8
                    let (s, _) ← lift (Array.to_slice_mut late_bytes)
                    let (r4, _) ←
                      aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
                        common.lane_transition s
                    let r5 ←
                      core.result.Result.map_err
                        aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r4 ()
                    let cf2 ←
                      core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf2 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      ok (core.result.Result.Ok ())
                    | core.ops.control_flow.ControlFlow.Break residual
                      =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual


def gate (common : RawCommon) (next : R) : R := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      common.master_account a
  if b
  then
    ok (core.result.Result.Err
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        common.checkpoint_account a1
    if b1
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
    else
      let a2 := Array.repeat 32#usize 0#u8
      let b2 ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
          common.selected_lane_account a2
      if b2
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
      else
        let i ← lift (core.convert.num.FromUsizeU8.from common.output_lane)
        if i >=
          aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidOutputLane)
        else
          next

theorem source_factor (s : RawStatement) :
    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
    (do let c ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common s
        gate c (continuation s c)) := by rfl

#print axioms source_factor
end NEE_RawValidatorPrefix

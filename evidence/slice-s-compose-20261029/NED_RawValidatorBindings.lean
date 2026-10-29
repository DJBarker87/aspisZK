import NED_RawValidatorControl
set_option autoImplicit false
noncomputable section
namespace NED_RawValidatorBindings
open Aeneas Aeneas.Std Result NBN_StatementResult NED_ErrorCarriers
open AspisR1AdapterReconstruct
attribute [local instance] Classical.propDecidable

def run (s : Statement) : Result (core.result.Result Unit NED_RawValidatorControl.E) := do
  let statement := NED_ReconstructCarriers.toRaw s
  let common := NED_ReconstructCarriers.toRawCommon (NBN_StatementResult.common s)
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
            NED_RawValidatorControl.tail s

theorem result (s : Statement) : run s = ok
    (NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (suffix s)) := by
  unfold run
  rw [NED_RawValidatorControl.tail_factor,NED_RawValidatorTail.result,
    NED_ReconstructCarriers.parts_argument]
  simp only [bind_tc_ok,NBN_ArrayNe.bytes,NED_RawWordArrayEq.ne,
    NED_StatementCarrierFields.master,NED_LateCarrierFields.common_late,
    NED_LateCarrierFields.live,NED_StatementCarrierFields.pool,NED_StatementCarrierFields.deployment,
    NED_StatementCarrierFields.sequence,NED_LateCarrierFields.common_anchor]
  rw [NBN_BindingChecks.factor]
  unfold NBN_BindingChecks.chain
  simp only [bne_iff_ne,decide_eq_true_eq]
  repeat' first | rfl | (split <;> try simp_all only
    [NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1])

#print axioms result
end NED_RawValidatorBindings

import R1Z.PV_RunJoin_OuterCall30
import R1Z.PV_RunJoin_RejectionProof28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterTransferErrors30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

def Path
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (witness :
  pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
  (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
  (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (error : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) : Prop :=
  ∃ r, (
    pool_v1.pair_forest_trace.lane_root witness.input.pair
  ) = ok r ∧
  ∃ cf, (
    core.result.Result.Insts.CoreOpsTry.branch r
  ) = ok cf ∧
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ∃ r1, (
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
      { public1 with anchor_root := val }
    ) = ok r1 ∧
    ∃ r2, (
      core.result.Result.map_err (BuiltinFnOnce
      pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError
      pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) r1
      (pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.StatementCtor)
    ) = ok r2 ∧
    ∃ cf1, (
      core.result.Result.Insts.CoreOpsTry.branch r2
    ) = ok cf1 ∧
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ∃ pvprcv, (
        pool_v1.pair_forest_trace.temporary_context context val
      ) = ok pvprcv ∧
      ∃ r3, (
        pool_v1.pair_trace.validate_common public1.pool
        public1.deployment_domain public1.anchor_sequence val
        public1.nullifier public1.asset_id witness.input.pair pvprcv
      ) = ok r3 ∧
      ∃ cf2, (
        core.result.Result.Insts.CoreOpsTry.branch r3
      ) = ok cf2 ∧
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ∃ b, (
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          snapshot.pool public1.pool
        ) = ok b ∧
        if b
        then
          (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.SnapshotBindingMismatch = .Err error)
        else
          ∃ b1, (
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            snapshot.deployment_domain public1.deployment_domain
          ) = ok b1 ∧
          if b1
          then
            (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.SnapshotBindingMismatch = .Err error)
          else
            if witness.recipient.value = 0#u32
            then
              (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.Conservation = .Err error)
            else
              if witness.change.value = 0#u32
              then
                (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.Conservation = .Err error)
              else
                ∃ i, (
                  spend.VALUE_LIMIT
                ) = ok i ∧
                if witness.recipient.value >= i
                then
                  (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.Conservation = .Err error)
                else
                  if witness.change.value >= i
                  then
                    (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.Conservation = .Err error)
                  else
                    ∃ o, (
                      lift (U32.checked_add witness.recipient.value
                      witness.change.value)
                    ) = ok o ∧
                    ∃ b2, (
                      core.option.Option.Insts.CoreCmpPartialEqOption.ne
                      core.cmp.PartialEqU32 o (some witness.input.pair.value)
                    ) = ok b2 ∧
                    if b2
                    then
                      (core.result.Result.Err pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1.Conservation = .Err error)
                    else
                      wp (
                      pool_v1.pair_forest_trace.compile_forest_from_copies
                        witness.input witness.recipient.value (some
                        witness.recipient) witness.change
                        {
                          anchor := public1.anchor_root,
                          nullifier := public1.nullifier,
                          recipient_commitment :=
                            (some public1.recipient_commitment),
                          change_commitment := public1.change_commitment,
                          asset := public1.asset_id
                        } val snapshot
                      ) (fun r => r = .Err error)
      | core.ops.control_flow.ControlFlow.Break residual =>
        (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) residual = ok (.Err error))
    | core.ops.control_flow.ControlFlow.Break residual =>
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) residual = ok (.Err error))
  | core.ops.control_flow.ControlFlow.Break residual =>
    (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (core.convert.FromSame pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) residual = ok (.Err error))

theorem error_iff
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (witness :
  pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
  (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
  (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (error : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) :
    pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 public1 witness context snapshot = ok (.Err error) ↔ Path public1 witness context snapshot error := by
  rw [eq_wp]
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,
    ok_ne_err,residual_eq_wp,Result.ok.injEq,Prod.exists]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,
        residual_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,Prod.exists])
#print axioms error_iff
end R1Z.PV_RunJoin_OuterTransferErrors30

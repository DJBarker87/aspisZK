import R1Z.PV_RunJoin_CanonicalCoverage31
import R1Z.PV_RunJoin_OuterSnapshotBinding30
import R1Z.PV_RunJoin_PreparationContext32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalBinding32
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native

/-- Binding facts for the original successful canonical preparation, without
 assuming equality of its omitted context bytes. -/
theorem transfer (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    (PV_RunJoin_CodecOuter30.snapshot snapshot).pool=p.pool ∧
    (PV_RunJoin_CodecOuter30.snapshot snapshot).deployment_domain=p.deployment_domain ∧
    context.runtime_binding.pool=p.pool ∧
    context.runtime_binding.deployment_domain=p.deployment_domain ∧
    context.runtime_binding.anchor_sequence=p.anchor_sequence ∧
    context.runtime_binding.asset_id=p.asset_id := by
  have ho := (PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h).2
  have hs := PV_RunJoin_OuterSnapshotBinding30.transfer p w context _ c ho
  exact ⟨hs.1,hs.2,PV_RunJoin_PreparationContext32.transfer_binding p w context _ c ho⟩
#print axioms transfer

/-- Binding facts for the original successful canonical preparation, without
 assuming equality of its omitted context bytes. -/
theorem withdrawal (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    (PV_RunJoin_CodecOuter30.snapshot snapshot).pool=p.pool ∧
    (PV_RunJoin_CodecOuter30.snapshot snapshot).deployment_domain=p.deployment_domain ∧
    context.runtime_binding.pool=p.pool ∧
    context.runtime_binding.deployment_domain=p.deployment_domain ∧
    context.runtime_binding.anchor_sequence=p.anchor_sequence ∧
    context.runtime_binding.asset_id=p.asset_id := by
  have ho := (PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h).2
  have hs := PV_RunJoin_OuterSnapshotBinding30.withdrawal p w context _ c ho
  exact ⟨hs.1,hs.2,PV_RunJoin_PreparationContext32.withdrawal_binding p w context _ c ho⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_CanonicalBinding32

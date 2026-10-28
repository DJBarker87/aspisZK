import R1Z.PV_RunJoin_OuterReady30
import R1Z.PV_RunJoin_CodecOuter30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalReady30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]

theorem transfer
    (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    (∃ output, PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok output)) ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun s =>
      ∃ root, PV_RunJoin_OuterReady30.TransferReady p w context (PV_RunJoin_CodecOuter30.snapshot s) root) :=
  PV_RunJoin_CodecOuter30.success_iff bytes _ _ (fun s =>
    PV_RunJoin_OuterReady30.transfer_iff p w context (PV_RunJoin_CodecOuter30.snapshot s))
#print axioms transfer

theorem withdrawal
    (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    (∃ output, PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok output)) ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun s =>
      ∃ root, PV_RunJoin_OuterReady30.WithdrawalReady p w context (PV_RunJoin_CodecOuter30.snapshot s) root) :=
  PV_RunJoin_CodecOuter30.success_iff bytes _ _ (fun s =>
    PV_RunJoin_OuterReady30.withdrawal_iff p w context (PV_RunJoin_CodecOuter30.snapshot s))
#print axioms withdrawal
end R1Z.PV_RunJoin_CanonicalReady30

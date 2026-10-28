import R1Z.PV_RunJoin_CanonicalHonest31
import R1Z.PV_RunJoin_CanonicalReady30
import R1Z.PV_RunJoin_HonestIdentification26
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalCoverage31
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- The canonical prepared family, including actual success and all HonestInput
obligations. Honesty is proved below from the operational domain, never assumed. -/
def TransferCovered (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) : Prop :=
  ∃ snapshot c root,
    PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c)) ∧
    pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
      (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c)

theorem transfer_iff (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    TransferCovered (K := K) bytes p w context ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun snapshot =>
      ∃ root, PV_RunJoin_OuterReady30.TransferReady p w context (PV_RunJoin_CodecOuter30.snapshot snapshot) root) := by
  constructor
  · rintro ⟨snapshot,c,root,h,_,_⟩
    exact (PV_RunJoin_CanonicalReady30.transfer bytes p w context).mp ⟨(snapshot,c),h⟩
  · intro ready
    obtain ⟨output,h⟩ := (PV_RunJoin_CanonicalReady30.transfer bytes p w context).mpr ready
    rcases output with ⟨snapshot,c⟩
    obtain ⟨root,hr,honest⟩ := PV_RunJoin_CanonicalHonest31.transfer (K := K) bytes p w context snapshot c h
    exact ⟨snapshot,c,root,h,hr,honest⟩
#print axioms transfer_iff

/-- The canonical prepared family, including actual success and all HonestInput
obligations. Honesty is proved below from the operational domain, never assumed. -/
def WithdrawalCovered (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) : Prop :=
  ∃ snapshot c root,
    PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c)) ∧
    pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
      (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c)

theorem withdrawal_iff (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    WithdrawalCovered (K := K) bytes p w context ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun snapshot =>
      ∃ root, PV_RunJoin_OuterReady30.WithdrawalReady p w context (PV_RunJoin_CodecOuter30.snapshot snapshot) root) := by
  constructor
  · rintro ⟨snapshot,c,root,h,_,_⟩
    exact (PV_RunJoin_CanonicalReady30.withdrawal bytes p w context).mp ⟨(snapshot,c),h⟩
  · intro ready
    obtain ⟨output,h⟩ := (PV_RunJoin_CanonicalReady30.withdrawal bytes p w context).mpr ready
    rcases output with ⟨snapshot,c⟩
    obtain ⟨root,hr,honest⟩ := PV_RunJoin_CanonicalHonest31.withdrawal (K := K) bytes p w context snapshot c h
    exact ⟨snapshot,c,root,h,hr,honest⟩
#print axioms withdrawal_iff
end R1Z.PV_RunJoin_CanonicalCoverage31

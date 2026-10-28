import R1Z.PV_RunJoin_CanonicalCoverage31
import PV_L2C_HonestCaller
set_option autoImplicit false
noncomputable section
namespace PV_L2C_CanonicalCaller
open Aeneas Aeneas.Std Result R1Z PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- A successful preparation, retaining both Result layers and its exact payload.
No guard outcome or extra randomness condition is part of this carrier. -/
structure Transfer where
  bytes : Slice U8
  pubInput : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
  witness : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1
  context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1
  snapshot : PV_RunJoin_CodecOuter30.Snapshot
  compiled : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  success : PV_RunJoin_CodecOuter30.run bytes
    (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 pubInput witness context) =
      ok (.Ok (snapshot,compiled))

structure Withdrawal where
  bytes : Slice U8
  pubInput : pool_v1.payment_relation.PoolV1WithdrawalPublicV1
  witness : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1
  context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1
  snapshot : PV_RunJoin_CodecOuter30.Snapshot
  compiled : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  success : PV_RunJoin_CodecOuter30.run bytes
    (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 pubInput witness context) =
      ok (.Ok (snapshot,compiled))

theorem transfer_entry (t : Transfer) :
    ∃ i : PV_L2C_HonestCaller.Family (K:=K), ∃ root,
      pool_v1.pair_forest_trace.lane_root t.witness.input.pair = ok (.Ok root) ∧
      i.val = PV_RunJoin_OuterChecked30.transferInput t.pubInput t.witness root
        (PV_RunJoin_CodecOuter30.snapshot t.snapshot) t.compiled := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.transfer (K:=K)
    t.bytes t.pubInput t.witness t.context t.snapshot t.compiled t.success
  exact ⟨⟨_,hi⟩,root,hr,rfl⟩
#print axioms transfer_entry

theorem withdrawal_entry (t : Withdrawal) :
    ∃ i : PV_L2C_HonestCaller.Family (K:=K), ∃ root,
      pool_v1.pair_forest_trace.lane_root t.witness.input.pair = ok (.Ok root) ∧
      i.val = PV_RunJoin_OuterChecked30.withdrawalInput t.pubInput t.witness root
        (PV_RunJoin_CodecOuter30.snapshot t.snapshot) t.compiled := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.withdrawal (K:=K)
    t.bytes t.pubInput t.witness t.context t.snapshot t.compiled t.success
  exact ⟨⟨_,hi⟩,root,hr,rfl⟩
#print axioms withdrawal_entry

def transfer (t : Transfer) : PV_L2C_HonestCaller.Family (K:=K) :=
  Classical.choose (transfer_entry (K:=K) t)
def withdrawal (t : Withdrawal) : PV_L2C_HonestCaller.Family (K:=K) :=
  Classical.choose (withdrawal_entry (K:=K) t)

theorem transfer_payload (t : Transfer) :
    (transfer (K:=K) t).val.compiled=t.compiled := by
  obtain ⟨root,_,hi⟩ := Classical.choose_spec (transfer_entry (K:=K) t)
  rw [show (transfer (K:=K) t).val = _ from hi]
  rfl
#print axioms transfer_payload

theorem withdrawal_payload (t : Withdrawal) :
    (withdrawal (K:=K) t).val.compiled=t.compiled := by
  obtain ⟨root,_,hi⟩ := Classical.choose_spec (withdrawal_entry (K:=K) t)
  rw [show (withdrawal (K:=K) t).val = _ from hi]
  rfl
#print axioms withdrawal_payload
end PV_L2C_CanonicalCaller

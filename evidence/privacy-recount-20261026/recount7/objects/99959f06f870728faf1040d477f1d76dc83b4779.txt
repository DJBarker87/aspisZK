import R1Z.PV_RunJoin_OuterReturns30
import R1Z.PV_RunJoin_OuterCommonFacts30
import R1Z.PV_RunJoin_OuterBounds30
import R1Z.PV_RunJoin_CompilerSuperRoot30
import R1Z.PV_RunJoin_DomainSupport28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterChecked30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable [LaneRoot]

def transferPublic (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : BuilderPublicProjection.Transfer :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩

def withdrawalPublic (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : BuilderPublicProjection.Withdrawal :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩

def transferInput (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (root : Array U32 8#usize) (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : PV_Src_NativeInput.Input :=
  ⟨.transfer (transferPublic p) (noteToForest w.recipient),inputToForest w.input,
    noteToForest w.change,root,snapshotToForest snapshot,compilationToForest c⟩

def withdrawalInput (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (root : Array U32 8#usize) (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : PV_Src_NativeInput.Input :=
  ⟨.withdrawal (withdrawalPublic p),inputToForest w.input,noteToForest w.change,
    root,snapshotToForest snapshot,compilationToForest c⟩

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_Src_NativeInput.run (transferInput p w root snapshot c) =
        ok (.Ok (transferInput p w root snapshot c).compiled) ∧
      PV_Src_RecordReference.Checked (transferInput p w root snapshot c) := by
  obtain ⟨root,hr,hc⟩ := PV_RunJoin_OuterReturns30.transfer_inner p w context snapshot c h
  have facts := PV_RunJoin_OuterCommonFacts30.transfer p w context snapshot c h
  have bounds := PV_RunJoin_OuterBounds30.transfer p w context snapshot c h
  have super := PV_RunJoin_CompilerSuperRoot30.canonical _ _ _ _ _ _ _ _ hc
  exact ⟨root,hr,hc,⟨⟨facts.value_bound,bounds.1,bounds.2⟩,
    facts.pair_first,facts.pair_second,facts.membership,super⟩⟩
#print axioms transfer

theorem withdrawal
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_Src_NativeInput.run (withdrawalInput p w root snapshot c) =
        ok (.Ok (withdrawalInput p w root snapshot c).compiled) ∧
      PV_Src_RecordReference.Checked (withdrawalInput p w root snapshot c) := by
  obtain ⟨root,hr,hc⟩ := PV_RunJoin_OuterReturns30.withdrawal_inner p w context snapshot c h
  have facts := PV_RunJoin_OuterCommonFacts30.withdrawal p w context snapshot c h
  have out := PV_RunJoin_OuterBounds30.withdrawal_amount p w context snapshot c h
  have change := PV_RunJoin_OuterBounds30.withdrawal_change p w context snapshot c h
  have super := PV_RunJoin_CompilerSuperRoot30.canonical _ _ _ _ _ _ _ _ hc
  exact ⟨root,hr,hc,⟨⟨facts.value_bound,out,change⟩,
    facts.pair_first,facts.pair_second,facts.membership,super⟩⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_OuterChecked30

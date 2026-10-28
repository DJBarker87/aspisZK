import R1Z.PV_RunJoin_OuterChecked30
import R1Z.PV_RunJoin_OuterConservation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticValues30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def witness (i : PV_Src_NativeInput.Input) := BuilderCanonical.liftWitness (K := K)
  (BuilderRecordCanonical.witness (PV_Src_Forest_PrimitiveArguments.wordWitness
    (PV_RunJoin_UniversalBuild22.records i).w))

theorem balance (i : PV_Src_NativeInput.Input) (hc : PV_Src_RecordReference.Checked i)
    (hs : (PV_Src_NativeInput.outputValue i.request).val+i.change.value.val=i.witness.pair.value.val) :
    (witness (K := K) i).inputValue.val =
      (witness (K := K) i).outputValue.val+(witness (K := K) i).changeValue.val := by
  change i.witness.pair.value.val % 2^30 =
    (PV_Src_NativeInput.outputValue i.request).val % 2^30+i.change.value.val % 2^30
  rw [Nat.mod_eq_of_lt hc.values.1,Nat.mod_eq_of_lt hc.values.2.1,Nat.mod_eq_of_lt hc.values.2.2]
  exact hs.symm
#print axioms balance

local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable [LaneRoot]

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ root, let i := PV_RunJoin_OuterChecked30.transferInput p w root snapshot c
      (witness (K := K) i).inputValue.val =
        (witness (K := K) i).outputValue.val+(witness (K := K) i).changeValue.val := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterChecked30.transfer p w context snapshot c h
  have hv := PV_RunJoin_OuterConservation30.transfer p w context snapshot c h
  exact ⟨root,balance _ hc hv.2.2.2.2⟩
#print axioms transfer

theorem withdrawal
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ root, let i := PV_RunJoin_OuterChecked30.withdrawalInput p w root snapshot c
      (witness (K := K) i).inputValue.val =
        (witness (K := K) i).outputValue.val+(witness (K := K) i).changeValue.val := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterChecked30.withdrawal p w context snapshot c h
  have hv := PV_RunJoin_OuterConservation30.withdrawal p w context snapshot c h
  exact ⟨root,balance _ hc hv.2.2⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_SemanticValues30

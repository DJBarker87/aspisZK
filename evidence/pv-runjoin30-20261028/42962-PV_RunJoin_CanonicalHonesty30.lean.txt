import R1Z.PV_RunJoin_OuterChecked30
import R1Z.PV_RunJoin_CodecOuter30
import R1Z.PV_RunJoin_DecodedFrontier29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalHonesty30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable [LaneRoot]

theorem transfer_payload (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_Src_NativeInput.run (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) = ok (.Ok (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c).compiled) ∧
      PV_Src_RecordReference.Checked (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ∧
      ∀ l : Fin 20, Canon8 (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c).snapshot.frontier.val[l.val]! := by
  obtain ⟨decoded,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  obtain ⟨root,hr,hn,hc⟩ := PV_RunJoin_OuterChecked30.transfer p w context _ c compiled
  refine ⟨root,hr,hn,hc,?_⟩
  intro l
  change Canon8 (PV_RunJoin_OuterABI30.snapshotToForest
    (PV_RunJoin_OuterABI30.snapshotFromForest
      (PV_RunJoin_DecodedArguments29.snapshot snapshot))).frontier.val[l.val]!
  rw [PV_RunJoin_OuterABI30.snapshot_roundtrip]
  exact PV_RunJoin_DecodedFrontier29.decoded_frontier bytes snapshot decoded l
#print axioms transfer_payload

theorem withdrawal_payload (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_Src_NativeInput.run (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) = ok (.Ok (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c).compiled) ∧
      PV_Src_RecordReference.Checked (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ∧
      ∀ l : Fin 20, Canon8 (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c).snapshot.frontier.val[l.val]! := by
  obtain ⟨decoded,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  obtain ⟨root,hr,hn,hc⟩ := PV_RunJoin_OuterChecked30.withdrawal p w context _ c compiled
  refine ⟨root,hr,hn,hc,?_⟩
  intro l
  change Canon8 (PV_RunJoin_OuterABI30.snapshotToForest
    (PV_RunJoin_OuterABI30.snapshotFromForest
      (PV_RunJoin_DecodedArguments29.snapshot snapshot))).frontier.val[l.val]!
  rw [PV_RunJoin_OuterABI30.snapshot_roundtrip]
  exact PV_RunJoin_DecodedFrontier29.decoded_frontier bytes snapshot decoded l
#print axioms withdrawal_payload

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- All representation, cached-result and Checked obligations follow from the
canonical route. Semantic Admission remains explicit and is not inferred. -/
theorem transfer_honest_iff (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      (PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ↔
        PV_RunJoin_UniversalBuild22.Admission (K := K) (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c)) := by
  obtain ⟨root,hr,hn,hc,hf⟩ := transfer_payload bytes p w context snapshot c h
  refine ⟨root,hr,?_⟩
  exact ⟨fun hi => hi.1,fun ha => ⟨ha,hn,hc,hf⟩⟩
#print axioms transfer_honest_iff

/-- All representation, cached-result and Checked obligations follow from the
canonical route. Semantic Admission remains explicit and is not inferred. -/
theorem withdrawal_honest_iff (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      (PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ↔
        PV_RunJoin_UniversalBuild22.Admission (K := K) (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c)) := by
  obtain ⟨root,hr,hn,hc,hf⟩ := withdrawal_payload bytes p w context snapshot c h
  refine ⟨root,hr,?_⟩
  exact ⟨fun hi => hi.1,fun ha => ⟨ha,hn,hc,hf⟩⟩
#print axioms withdrawal_honest_iff
end R1Z.PV_RunJoin_CanonicalHonesty30

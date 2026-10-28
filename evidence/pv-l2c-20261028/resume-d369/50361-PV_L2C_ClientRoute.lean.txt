import PV_L2C_DecoderRoute
import PV_L2C_AccountOrigins
import PV_L2C_DirectCompilerRange
set_option autoImplicit false
noncomputable section
namespace PV_L2C_ClientRoute
open Aeneas Aeneas.Std Result R1Z PV_RunJoin_Outer30 R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native

/- A route domain for the selected planner: actual outer success, actual
output-field origins, and the ordered account-decode cut. This contains no
trace-cell canonicality or prover-guard success assumption. Unlike D370's
serialized snapshot route, the planner constructs this snapshot directly. -/
structure Transfer where
  pubInput : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
  witness : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1
  context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1
  snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  compiled : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  success : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
    pubInput witness context snapshot = ok (.Ok compiled)
  tree : PV_L2C_AccountOrigins.Tree snapshot.current_root snapshot.frontier
  asset : pubInput.asset_id = 77#u32
  recipientOwner : PV_L2C_DigestOrigin.Origin witness.recipient.owner_key
  recipientSalt : PV_L2C_DigestOrigin.Origin witness.recipient.salt
  changeOwner : PV_L2C_DigestOrigin.Origin witness.change.owner_key
  changeSalt : PV_L2C_DigestOrigin.Origin witness.change.salt

structure Withdrawal where
  pubInput : pool_v1.payment_relation.PoolV1WithdrawalPublicV1
  witness : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1
  context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1
  snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  compiled : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  success : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
    pubInput witness context snapshot = ok (.Ok compiled)
  tree : PV_L2C_AccountOrigins.Tree snapshot.current_root snapshot.frontier
  asset : pubInput.asset_id = 77#u32
  changeOwner : PV_L2C_DigestOrigin.Origin witness.change.owner_key
  changeSalt : PV_L2C_DigestOrigin.Origin witness.change.salt

theorem transfer_fields (t : Transfer) (root : Array U32 8#usize) :
    PV_L2C_RecordRange.Fields (PV_RunJoin_OuterChecked30.transferInput t.pubInput t.witness root
      t.snapshot t.compiled) := by
  have facts := PV_RunJoin_OuterCommonFacts30.transfer _ _ _ _ _ t.success
  have coords := PV_L2C_AdmissionPairRange.coordinates _ facts.pair_validation
  refine ⟨facts.key,facts.salt,coords.1,coords.2,?_,t.changeOwner,t.changeSalt⟩
  intro note he
  change some (PV_RunJoin_OuterABI30.noteToForest t.witness.recipient) = some note at he
  cases Option.some.inj he
  exact ⟨t.recipientOwner,t.recipientSalt⟩
#print axioms transfer_fields

theorem withdrawal_fields (t : Withdrawal) (root : Array U32 8#usize) :
    PV_L2C_RecordRange.Fields (PV_RunJoin_OuterChecked30.withdrawalInput t.pubInput t.witness root
      t.snapshot t.compiled) := by
  have facts := PV_RunJoin_OuterCommonFacts30.withdrawal _ _ _ _ _ t.success
  have coords := PV_L2C_AdmissionPairRange.coordinates _ facts.pair_validation
  refine ⟨facts.key,facts.salt,coords.1,coords.2,?_,t.changeOwner,t.changeSalt⟩
  intro note he
  change none = some note at he
  cases he
#print axioms withdrawal_fields

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
include K in
theorem transfer_columns (t : Transfer) :
    (∀ c, c < 16 → (t.compiled.semantic_c1.c1.val[c]!).val.length = 1024) ∧
    ∀ c r, (PV_Src_Forest_Columns.read t.compiled.semantic_c1.c1 c r).val < 2147483647 := by
  obtain ⟨root,hr,hs,hchecked⟩ := PV_RunJoin_OuterChecked30.transfer _ _ _ _ _ t.success
  exact PV_L2C_DirectCompilerRange.source (K:=K) _ hs hchecked
    (fun j => PV_L2C_DigestOrigin.canonical _ (PV_L2C_AccountOrigins.frontier _ _ t.tree j))
    (transfer_fields t root) (by change t.pubInput.asset_id.val < 2147483647;rw [t.asset];scalar_tac)
#print axioms transfer_columns

include K in
theorem withdrawal_columns (t : Withdrawal) :
    (∀ c, c < 16 → (t.compiled.semantic_c1.c1.val[c]!).val.length = 1024) ∧
    ∀ c r, (PV_Src_Forest_Columns.read t.compiled.semantic_c1.c1 c r).val < 2147483647 := by
  obtain ⟨root,hr,hs,hchecked⟩ := PV_RunJoin_OuterChecked30.withdrawal _ _ _ _ _ t.success
  exact PV_L2C_DirectCompilerRange.source (K:=K) _ hs hchecked
    (fun j => PV_L2C_DigestOrigin.canonical _ (PV_L2C_AccountOrigins.frontier _ _ t.tree j))
    (withdrawal_fields t root) (by change t.pubInput.asset_id.val < 2147483647;rw [t.asset];scalar_tac)
#print axioms withdrawal_columns
end PV_L2C_ClientRoute

import NNH_CorrectConfiguration
import NNH_Stage2GuardedCut
import NNH_EncodeOk
import NNH_AccountIndexOk
import NNH_GetterOk
import NNH_ValidatedExtent
set_option autoImplicit false
noncomputable section
namespace NNH_CorrectTx2Inputs
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

abbrev residual := NNH_CorrectConfiguration.residual
abbrev sdk := NNH_CorrectConfiguration.sdk

theorem getters (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (a : r1_pool_adapter.owned.OwnedAccount) (data : RSL.Bytes)
 (success : (account a).bytes=.ok data) :
 ∃ b,r1_pool_adapter.owned.OwnedAccount.data (sdk missing env err reserve) a=.ok (.Ok b) ∧ bytes b=data := by
 have mapped := NNH_ModelCarrier.getter (sdk missing env err reserve) a
 change outer (reply bytes) (r1_pool_adapter.owned.OwnedAccount.data (sdk missing env err reserve) a)=.ok (account a).bytes at mapped
 rw [success] at mapped
 exact NNH_MappedOk.value _ _ _ mapped

structure Packet (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError) where
 logical : NNH_Stage2GuardedCut.Packet ⟨key program,accounts xs,bytes data,reply slot clock⟩ env
 validated : r1_pool_adapter.ValidatedAsqa
 validate : r1_pool_adapter.owned.validate_asq8 (sdk missing env err reserve) program xs data clock=.ok (.Ok validated)
 validated_eq : NNH_ValidatedCarrier.value validated=logical.cut.validated
 extent : logical.cut.validated.proof_length=RSL.PROOF_BYTES
 proofAccount : r1_pool_adapter.owned.OwnedAccount
 proof_index : Slice.index_usize xs 0#usize=.ok proofAccount
 proof : Slice U8
 proof_read : r1_pool_adapter.owned.OwnedAccount.data (sdk missing env err reserve) proofAccount=.ok (.Ok proof)
 proof_eq : bytes proof=logical.cut.proof_data
 checkpointAccount : r1_pool_adapter.owned.OwnedAccount
 checkpoint_index : Slice.index_usize xs 6#usize=.ok checkpointAccount
 checkpoint : Slice U8
 checkpoint_read : r1_pool_adapter.owned.OwnedAccount.data (sdk missing env err reserve) checkpointAccount=.ok (.Ok checkpoint)
 checkpoint_eq : bytes checkpoint=logical.cut.checkpoint_data
 encoded : Array U8 1880#usize
 encode : (sdk missing env err reserve).op22 logical.cut.validated.statement=.ok (.Ok encoded)
 public_eq : bytes encoded.to_slice=logical.cut.public_bytes

theorem produce (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (success : NNH_Stage2GuardedEval.value ⟨key program,accounts xs,bytes data,reply slot clock⟩ env=.ok ()) :
 Nonempty (Packet missing env err reserve program xs data clock) := by
 obtain ⟨logical⟩ := NNH_Stage2GuardedCut.produce _ env success
 obtain ⟨validated,validate,validated_eq⟩ := NNH_ValidateSdkPort.value (residual missing env) env err reserve program xs data clock logical.cut.validated logical.cut.validate_ok
 have extent := NNH_ValidatedExtent.value (sdk missing env err reserve) env program xs data (reply slot clock) logical.cut.validated logical.cut.validate_ok
 obtain ⟨proofAccount,proof_index,proofAccount_eq⟩ := NNH_AccountIndexOk.value xs 0#usize logical.cut.proof_account logical.cut.proof_index
 obtain ⟨checkpointAccount,checkpoint_index,checkpointAccount_eq⟩ := NNH_AccountIndexOk.value xs 6#usize logical.cut.checkpoint_account logical.cut.checkpoint_index
 have proof_ok := logical.cut.proof_ok
 rw [←proofAccount_eq] at proof_ok
 obtain ⟨proof,proof_read,proof_eq⟩ := getters missing env err reserve proofAccount logical.cut.proof_data proof_ok
 have checkpoint_ok := logical.cut.checkpoint_ok
 rw [←checkpointAccount_eq] at checkpoint_ok
 obtain ⟨checkpoint,checkpoint_read,checkpoint_eq⟩ := getters missing env err reserve checkpointAccount logical.cut.checkpoint_data checkpoint_ok
 obtain ⟨encoded,encode,public_eq⟩ := NNH_EncodeOk.sdk (residual missing env) env err reserve logical.cut.validated.statement logical.cut.public_bytes logical.cut.encode_ok
 exact ⟨⟨logical,validated,validate,validated_eq,extent,proofAccount,proof_index,proof,proof_read,proof_eq,
  checkpointAccount,checkpoint_index,checkpoint,checkpoint_read,checkpoint_eq,encoded,encode,public_eq⟩⟩
#print axioms getters
#print axioms produce
end NNH_CorrectTx2Inputs

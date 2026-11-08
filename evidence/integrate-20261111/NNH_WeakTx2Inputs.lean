import NNH_Weak241Prefix
import NNH_CorrectTx2Inputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_WeakTx2Inputs
open Aeneas Aeneas.Std Result _root_.AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
structure Packet (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (V : RSL.TX2_241.V2Lib) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (clock : core.result.Result U64 solana_program_error.ProgramError) where
 logical : NNH_Weak241Prefix.Packet V ⟨key program,accounts xs,bytes data,reply slot clock⟩ env
 validated : r1_pool_adapter.ValidatedAsqa
 validate : r1_pool_adapter.owned.validate_asq8 (NNH_CorrectConfiguration.sdk m env err r)
  program xs data clock = .ok (.Ok validated)
 validated_eq : NNH_ValidatedCarrier.value validated = logical.validated
 extent : logical.validated.proof_length = RSL.PROOF_BYTES
 proofAccount : r1_pool_adapter.owned.OwnedAccount
 proof_index : Slice.index_usize xs 0#usize = .ok proofAccount
 proof : Slice U8
 proof_read : r1_pool_adapter.owned.OwnedAccount.data (NNH_CorrectConfiguration.sdk m env err r)
  proofAccount = .ok (.Ok proof)
 proof_eq : bytes proof = logical.reads.proofData
 checkpointAccount : r1_pool_adapter.owned.OwnedAccount
 checkpoint_index : Slice.index_usize xs 6#usize = .ok checkpointAccount
 checkpoint : Slice U8
 checkpoint_read : r1_pool_adapter.owned.OwnedAccount.data (NNH_CorrectConfiguration.sdk m env err r)
  checkpointAccount = .ok (.Ok checkpoint)
 checkpoint_eq : bytes checkpoint = logical.reads.checkpointData
 encoded : Array U8 1880#usize
 encode : (NNH_CorrectConfiguration.sdk m env err r).op22 validated.statement = .ok (.Ok encoded)
 public_eq : bytes encoded.to_slice = logical.reads.publicBytes

theorem produce (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (V : RSL.TX2_241.V2Lib) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (clock : core.result.Result U64 solana_program_error.ProgramError) (events : List RSL.Event)
 (reference : RSL.TX2_241.Ref L D V ⟨key program,accounts xs,bytes data,reply slot clock⟩ env
  ⟨.ret (.ok ()),events⟩) : Nonempty (Packet m env err r V program xs data clock) := by
 obtain ⟨logical⟩ := NNH_Weak241Prefix.produce V _ env events reference
 obtain ⟨validated,validate,validated_eq⟩ := NNH_ValidateSdkPort.value
  (NNH_CorrectConfiguration.residual m env) env err r program xs data clock logical.validated logical.validate_ok
 have extent := NNH_ValidatedExtent.value (NNH_CorrectConfiguration.sdk m env err r)
  env program xs data (reply slot clock) logical.validated logical.validate_ok
 have i0 : NND_Returned.indexValue (accounts xs) 0 = .ok logical.reads.acc0 := by
  unfold NND_Returned.indexValue
  rw [logical.reads.index0]
  rfl
 have i6 : NND_Returned.indexValue (accounts xs) 6 = .ok logical.reads.acc6 := by
  unfold NND_Returned.indexValue
  rw [logical.reads.index6]
  rfl
 obtain ⟨pa,ip,ep⟩ := NNH_AccountIndexOk.value xs 0#usize logical.reads.acc0 i0
 obtain ⟨ca,ic,ec⟩ := NNH_AccountIndexOk.value xs 6#usize logical.reads.acc6 i6
 have rp := logical.reads.read0
 rw [←ep] at rp
 obtain ⟨proof,read,proof_eq⟩ := NNH_CorrectTx2Inputs.getters m env err r pa logical.reads.proofData rp
 have rc := logical.reads.read6
 rw [←ec] at rc
 obtain ⟨ck,readck,ck_eq⟩ := NNH_CorrectTx2Inputs.getters m env err r ca logical.reads.checkpointData rc
 obtain ⟨enc,encoding,pub_eq⟩ := NNH_EncodeOk.sdk (NNH_CorrectConfiguration.residual m env)
  env err r logical.validated.statement logical.reads.publicBytes logical.encode_ok
 have st_eq : validated.statement = logical.validated.statement := congrArg RSL.TX2_242.Validated.statement validated_eq
 rw [←st_eq] at encoding
 exact ⟨⟨logical,validated,validate,validated_eq,extent,pa,ip,proof,read,proof_eq,
  ca,ic,ck,readck,ck_eq,enc,encoding,pub_eq⟩⟩
#print axioms produce
end AspisR1.NNH_WeakTx2Inputs
end

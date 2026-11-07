import NNH_Stage1TopCut
import NNH_CorrectTx2Inputs
import NNH_S1CodecOk
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1NativePublic
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem produce (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (saved : RSL.Bytes) (success : NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ env=.ok saved) :
 ∃ p pub ck, (accounts xs)=[p,pub,ck] ∧
 ∃ packet : NNH_Stage1Cut.Packet ⟨key program,accounts xs,bytes data⟩ p pub ck saved env,
 ∃ publicAccount publicData nativeStatement,
 Slice.index_usize xs 1#usize=.ok publicAccount ∧
 r1_pool_adapter.owned.OwnedAccount.data (NNH_CorrectConfiguration.sdk missing env err reserve) publicAccount=.ok (.Ok publicData) ∧
 bytes publicData=packet.public_data ∧
 (NNH_CorrectConfiguration.sdk missing env err reserve).op47 publicData=.ok (.Ok nativeStatement) ∧
 NNH_S1DecodeOk.carrier nativeStatement=packet.statement := by
 obtain ⟨p,pub,ck,shape,route,⟨packet⟩⟩ := NNH_Stage1TopCut.produce _ saved env success
 change accounts xs=[p,pub,ck] at shape
 have index : NND_Returned.indexValue (accounts xs) 1=.ok pub := by rw [shape]; rfl
 obtain ⟨publicAccount,indexRun,carrierEq⟩ := NNH_AccountIndexOk.value xs 1#usize pub index
 have read : (account publicAccount).bytes=.ok packet.public_data :=
  (congrArg RSL.OwnedAccount.bytes carrierEq).trans packet.public_read
 obtain ⟨publicData,readRun,bytesEq⟩ := NNH_CorrectTx2Inputs.getters missing env err reserve publicAccount packet.public_data read
 have decode : C.decodeStatement (bytes publicData)=some packet.statement :=
  (congrArg C.decodeStatement bytesEq).trans packet.decode
 obtain ⟨nativeStatement,decodeRun,statementEq⟩ := NNH_S1CodecOk.decode missing env err reserve publicData packet.statement decode
 exact ⟨p,pub,ck,shape,packet,publicAccount,publicData,nativeStatement,indexRun,readRun,bytesEq,decodeRun,statementEq⟩
#print axioms produce
end NNH_Stage1NativePublic

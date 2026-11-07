import NNH_Stage2To064
import NNH_AuthResumeSdk
import NNH_AuthReservation
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2ResumeOccurrence
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem produce (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (packet : NNH_CorrectTx2Inputs.Packet missing env err reserve program xs data clock) :
 env.reservation=true ∧ ∃ segment p a,
 RSL.TX2_241.Dom064 V0 (bytes packet.encoded.to_slice,bytes segment,bytes packet.checkpoint) ∧
 (DrvC_Installation.stage (NNH_CorrectConfiguration.configuration missing env err reserve)).op18
  (LIBB_PartitionEnv.digest env) packet.checkpoint segment packet.encoded.to_slice .S2 ()=.ok (.Ok (p,a)) ∧
 NID_ResumeFields.Domain p a ∧ a.next=10#usize := by
 obtain ⟨segment,range,domain,source⟩ := NNH_CorrectCallInputs.produce missing env err reserve program xs data clock packet
 have reserved:=NNH_AuthReservation.source env packet.encoded.to_slice segment packet.checkpoint domain source
 obtain ⟨p,a,resume,fields,next⟩ := NNH_AuthResumeSdk.produce missing env err reserve packet.encoded.to_slice segment packet.checkpoint domain source
 refine ⟨reserved,segment,p,a,domain,?_,fields,next⟩
 rw [NNH_CorrectConfiguration.stage]
 exact resume
#print axioms produce
end NNH_Stage2ResumeOccurrence

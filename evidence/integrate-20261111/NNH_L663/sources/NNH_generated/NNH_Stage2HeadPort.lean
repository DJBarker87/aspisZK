import NNH_Stage2HeadGuard
import NNH_CorrectTx2Inputs
import NNH_Stage2Fission
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2HeadPort
open Aeneas Aeneas.Std AspisR1 AdapterRw NNH_ModelCarrier NND_Carrier

theorem source (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (p : NNH_CorrectTx2Inputs.Packet missing env err reserve program xs data clock) :
 r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data clock=
 NNH_Stage2Fission.reads (NNH_CorrectConfiguration.sdk missing env err reserve) xs p.validated := by
 obtain ⟨length,data_length,magic⟩ := NNH_Stage2Guards.value _ p.logical.cut.guards
 have native_length : Slice.len xs=7#usize := by
  apply UScalar.eq_of_val_eq
  change xs.val.length=7
  simpa only [accounts,List.length_map] using length
 have native_data_length : 4≤data.val.length := by
  simpa only [bytes,List.length_map] using data_length
 have get := NNH_RequestMagic.get data native_data_length magic
 rw [NNH_Stage2Fission.source]
 unfold NNH_Stage2Fission.head
 simp only [native_length,bne_self_eq_false,Bool.false_eq_true,if_false,get,
  NNH_Stage2HeadGuard.full,bind_tc_ok,NNH_Stage2HeadGuard.equal,p.validate,
  core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end NNH_Stage2HeadPort

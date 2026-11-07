import NNH_Stage2Suffix
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Reads
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem source (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (p : NNH_Tx2ConcreteInputs.Packet missing env err reserve program xs data clock) :
 NNH_Stage2Fission.reads (NNH_RuntimeErrorValue.sdk missing env err reserve) xs p.validated=
 NNH_Stage2Fission.afterReads (NNH_RuntimeErrorValue.sdk missing env err reserve) p.validated p.proof p.checkpoint := by
 unfold NNH_Stage2Fission.reads
 simp only [p.proof_index,p.proof_read,p.checkpoint_index,p.checkpoint_read,bind_tc_ok,
  core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end NNH_Stage2Reads

import NNH_ValidateFission
set_option autoImplicit false
noncomputable section
namespace NNH_ValidateScanStep
open Aeneas Aeneas.Std Result AdapterRw

theorem source (base : Ops) (env : RSL.Env)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (q : LIBB_PoolCarriers.Request)
 (auth : r1_pool_adapter.AuthenticatedAsq8Accounts)
 (proof : r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (scanned : r1_pool_adapter.ScannedAsqaProof)
 (statement : LIBB_PoolCarriers.Statement)
 (head : xs.val.head?=some proof)
 (read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) proof=.ok (.Ok data))
 (scan : AspisR1.NFY_JHf_Scan.source data=.ok (.Ok scanned))
 (reconstruct : AspisR1.NFY_JHf_ReconstructionSlot.source q auth scanned.candidate_afterstate=.ok (.Ok statement)) :
 NNH_ValidateFission.scan (NNH_Tx2ModelSlots.install base env) xs q auth=
 .ok (.Ok {statement:=statement,proof_length:=scanned.proof_length}) := by
 have first : (NNH_Tx2ModelSlots.install base env).op9 xs=.ok (some proof) := by
  change Result.ok (xs.val.head?)=_
  rw [head]
 have scanning : (NNH_Tx2ModelSlots.install base env).op51 data=.ok (.Ok scanned) := scan
 have reconstructing : (NNH_Tx2ModelSlots.install base env).op52 q auth scanned.candidate_afterstate=.ok (.Ok statement) := reconstruct
 unfold NNH_ValidateFission.scan
 simp only [first,bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
  read,scanning,reconstructing]
#print axioms source
end NNH_ValidateScanStep

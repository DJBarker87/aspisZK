import NNH_AuthCheckpointPort
import NNH_AuthMasterPort
import NNH_AuthHeadStep
import NNH_AuthSdkGuards
import NNH_AuthSdkTail
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSdkBodyPort
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value {E : Type} (missing : IDa_Deployed.Uninstalled E) (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64) (out : RSL.Authenticated)
 (success : NNH_AuthEval.bodyValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out) :
 ∃ native,r1_pool_adapter.owned.authenticate_asq8_accounts (NNH_Tx2Configuration.sdk missing env err reserve)
  program (NNH_SevenAccounts.value p m c l r e v) pool lane slot=.ok (.Ok native) ∧ auth native=out := by
 have guards := NNH_AuthSdkGuards.produce missing env err reserve program pool p m c l r e v (byte lane) (NND_Carrier.slot slot) out success
 have cut := NNH_AuthOkPrefix.produce L D _ _ _ _ _ _ _ _ env out success
 have tail := cut.tail
 rw [NNH_AuthTailValues.factor] at tail
 obtain ⟨master,step,next⟩ := NNH_AuthMasterPort.value (NNH_Tx2Configuration.sdk missing env err reserve) env program pool p m c l r e v lane slot out tail
 obtain ⟨native,run,output⟩ := NNH_AuthCheckpointPort.value (NNH_Tx2Configuration.sdk missing env err reserve) env program pool p m c l r e v lane slot master out next
 refine ⟨native,?_,output⟩
 rw [NNH_AuthHeadStep.source _ program pool p m c l r e v lane slot guards,NNH_AuthTailParts.source,NNH_AuthSdkTail.master missing env err reserve,step]
 exact run
#print axioms value
end NNH_AuthSdkBodyPort

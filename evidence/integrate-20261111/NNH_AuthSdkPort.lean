import NNH_AuthSdkBodyPort
import NNH_AuthSevenShape
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSdkPort
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value {E : Type} (missing : IDa_Deployed.Uninstalled E) (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation) (program pool : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64) (out : RSL.Authenticated)
 (success : NNH_AuthEval.value L D ⟨key program,accounts xs,key pool,byte lane,NND_Carrier.slot slot⟩ env=.ok out) :
 ∃ native,r1_pool_adapter.owned.authenticate_asq8_accounts (NNH_Tx2Configuration.sdk missing env err reserve)
  program xs pool lane slot=.ok (.Ok native) ∧ auth native=out := by
 obtain ⟨p,m,c,l,r,e,v,shape,body⟩ := NNH_AuthSevenShape.value L D env program pool xs lane slot out success
 have same : xs=NNH_SevenAccounts.value p m c l r e v := by
  apply Subtype.ext
  exact shape
 have body' : NNH_AuthEval.bodyValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out := by
  simpa only [accounts,shape,List.map_cons,List.map_nil] using body
 rw [same]
 exact NNH_AuthSdkBodyPort.value missing env err reserve program pool p m c l r e v lane slot out body'
#print axioms value
end NNH_AuthSdkPort

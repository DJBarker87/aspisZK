import NNH_AuthGuardCongr
import NNH_AuthSdkDistinct
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSdkGuards
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem produce {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation)
 (program pool : solana_pubkey.Pubkey) (p m c l r e v : r1_pool_adapter.owned.OwnedAccount)
 (lane : UInt8) (slot : UInt64) (out : RSL.Authenticated)
 (success : NNH_AuthEval.bodyValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,lane,slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out) :
 NNH_AuthNativeGuards.Packet (NNH_Tx2Configuration.sdk missing env err reserve) program pool p m c l r e v := by
 have localGuards := NNH_AuthNativeGuards.produce L (NNH_Tx2Configuration.sdk missing env err reserve) env program pool p m c l r e v lane slot out success
 refine ⟨localGuards.proofGuard,?_,?_,?_,?_,?_⟩
 · rw [NNH_AuthGuardCongr.checkpoint _ (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err reserve) env)
    (by rfl) (by rfl) (by rfl)]
   exact localGuards.checkpointGuard
 · rw [NNH_AuthGuardCongr.readonly _ (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err reserve) env) (by rfl)]
   exact localGuards.masterGuard
 · rw [NNH_AuthGuardCongr.readonly _ (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err reserve) env) (by rfl)]
   exact localGuards.checkpointOwner
 · rw [NNH_AuthGuardCongr.readonly _ (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err reserve) env) (by rfl)]
   exact localGuards.laneGuard
 · apply NNH_AuthSdkDistinct.value missing env err reserve _ (by decide)
   have cut := NNH_AuthOkPrefix.produce _ _ _ _ _ _ _ _ _ _ _ _ success
   have distinct := cut.distinctGuard
   unfold RSL.requireDistinct at distinct
   split at distinct
   · rename_i h; exact h
   · cases distinct
#print axioms produce
end NNH_AuthSdkGuards

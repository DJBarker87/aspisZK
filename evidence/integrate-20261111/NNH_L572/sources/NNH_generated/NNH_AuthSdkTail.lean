import NNH_AuthMasterCongr
import NNH_Tx2Configuration
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSdkTail
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem registry {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_Tx2Configuration.sdk missing env err r)=
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err r) env) := by
 funext v p m s reg ent t
 apply NNH_RegistryCallCongr.same <;> rfl

theorem lane {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 NNH_AuthTailParts.lane (NNH_Tx2Configuration.sdk missing env err r)=
 NNH_AuthTailParts.lane (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err r) env) := by
 apply NNH_AuthLaneCongr.same <;> rfl

theorem checkpoint {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 NNH_AuthTailParts.checkpoint (NNH_Tx2Configuration.sdk missing env err r)=
 NNH_AuthTailParts.checkpoint (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err r) env) := by
 exact NNH_AuthCheckpointCongr.same _ _ rfl rfl rfl rfl rfl rfl (lane missing env err r)

theorem master {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 NNH_AuthTailParts.master (NNH_Tx2Configuration.sdk missing env err r)=
 NNH_AuthTailParts.master (NNH_Tx2ModelSlots.install (NNH_Tx2Configuration.sdk missing env err r) env) := by
 exact NNH_AuthMasterCongr.same _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  (checkpoint missing env err r) (registry missing env err r)
#print axioms registry
#print axioms lane
#print axioms checkpoint
#print axioms master
end NNH_AuthSdkTail

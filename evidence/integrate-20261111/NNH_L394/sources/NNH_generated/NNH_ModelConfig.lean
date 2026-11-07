import NNH_RegistryModel
import NNH_LaneModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_ModelConfig
open Aeneas Aeneas.Std
/-- Source-linked lane/registry slots and the actual fallible reservation tag.
The remaining base records are explicit unfinished data: this is NOT the
required total Missing.instance and is not installed as the final host. -/
def residual {E : Type} (missing : IDa_Deployed.Uninstalled E) (env : RSL.Env) :
 IDa_Deployed.Uninstalled E :=
 {missing with adapter := NNH_LaneModel.install missing.adapter, reserved := env.reservation}

def configuration {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 NNH_RegistryConfig.configuration (residual missing env) NNH_Libraries.D env err r

def sdk {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 DrvC_Installation.sdk (configuration missing env err r)

theorem reserved {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 (configuration missing env err r).reserved=env.reservation := rfl

theorem lane {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 (sdk missing env err r).op50=NNH_LaneModel.decode := rfl

#print axioms reserved
#print axioms lane
end AspisR1.NNH_ModelConfig

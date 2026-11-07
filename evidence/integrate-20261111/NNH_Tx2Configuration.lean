import NNH_AuthLaneCongr
import NNH_RegistryCallCongr
import RPx_Deployed
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2Configuration
open Aeneas Aeneas.Std AspisR1 AdapterRw NNH_Libraries
/-- Concrete source helpers selected for the TX2 model transport. Residual
records remain explicit data until the total literal Missing is constructed. -/
def select {E : Type} (missing : IDa_Deployed.Uninstalled E) (env : RSL.Env) : IDa_Deployed.Uninstalled E :=
 {missing with adapter:=NNH_Tx2ModelSlots.install missing.adapter env,reserved:=env.reservation}

def configuration {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 FIp_Install.configuration err (IDa_Deployed.deployedConfiguration (select missing env) err r) r

def sdk {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 DrvC_Installation.sdk (configuration missing env err r)

theorem reserved {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 (configuration missing env err r).reserved=env.reservation := rfl

theorem readonly {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 NGL_ReadonlyModel.install (sdk missing env err r)=sdk missing env err r := by rfl

#print axioms reserved
#print axioms readonly
end NNH_Tx2Configuration

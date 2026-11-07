import NNH_MRegistryOps
import IDa_Deployed
set_option autoImplicit false
noncomputable section
namespace NNH_RegistryConfig
open Aeneas Aeneas.Std AspisR1
/-- Registry-value slots installed into the actual headline configuration.
Unconsumed residual components remain explicit; this is not Missing.instance. -/
def select {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) : IDa_Deployed.Uninstalled E :=
 {missing with adapter := NNH_MRegistryOps.install missing.adapter D env}

def configuration {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 FIp_Install.configuration err (IDa_Deployed.deployedConfiguration (select missing D env) err r) r

def sdk {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :=
 DrvC_Installation.sdk (configuration missing D env err r)

/-- The reached PDA and clone slots survive the actual deployment installers. -/
theorem runtime_slots {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 (sdk missing D env err r).op38=NNH_MRegistryOps.pda env ∧
 (sdk missing D env err r).op35=(NNH_MRegistryOps.install missing.adapter D env).op35 := ⟨rfl,rfl⟩

/-- Every registry leaf slot is at the concrete local model's SAME function.
This is a proved projection equality, never a free Ops-compatibility premise. -/
theorem decoder_slots {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) :
 (sdk missing D env err r).op15=(NNH_MRegistryOps.install missing.adapter D env).op15 ∧
 (sdk missing D env err r).op31=(NNH_MRegistryOps.install missing.adapter D env).op31 ∧
 (sdk missing D env err r).op32=(NNH_MRegistryOps.install missing.adapter D env).op32 ∧
 (sdk missing D env err r).op33=(NNH_MRegistryOps.install missing.adapter D env).op33 ∧
 (sdk missing D env err r).op34=(NNH_MRegistryOps.install missing.adapter D env).op34 := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms runtime_slots
#print axioms decoder_slots
end NNH_RegistryConfig

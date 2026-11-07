import NNH_ModelConfig
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MissingErasure
open Aeneas Aeneas.Std

theorem current {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation)
 (other : AspisR1CurrentCaller.Ops) :
 DrvC_Installation.currentInstalled (NNH_ModelConfig.configuration
  {missing with currentBase:=other} env err r)=
 DrvC_Installation.currentInstalled (NNH_ModelConfig.configuration missing env err r) := by
 rfl
#print axioms current
end AspisR1.NNH_MissingErasure

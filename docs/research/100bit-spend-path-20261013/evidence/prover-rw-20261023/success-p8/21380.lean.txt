import R1Z.PV_OrdinaryPolicyBridge
import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OrdinaryReferenceDictionary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Auxiliary dictionaries. Neither is asserted equal to the current live candidate.
-- The full native sampler gate remains OPEN; op250 is not supplied by this file.
@[reducible] def reference (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op250 := PV_OrdinarySource.sampler_owned.ordinary_sample}
@[reducible] def policy (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op250 := ProverRwDictionarySamplers.ordinary}

theorem dictionaries (ops : ExternalFuns) : reference ops=policy ops := by
  exact congrArg (fun sample : Array U8 32#usize → Result aspis_core.field.wide_exact.WideExact =>
    {PV_CurrentScaleInstall.selected ops with op250 := sample})
      (funext PV_OrdinaryPolicyBridge.reference)
#print axioms dictionaries
end R1Z.PV_OrdinaryReferenceDictionary

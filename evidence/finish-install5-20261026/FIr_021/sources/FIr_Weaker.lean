import FIr_GlobalOwners
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_GlobalOwners
open Aeneas Aeneas.Std Result
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence
theorem of_original {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FIp_GlobalOwners.Owners c B) : Owners c B := by
  intro s H e i p q data t prepared calls shape x
  obtain ⟨pair,matching,endpoint⟩ := old s H e i p q data t prepared calls shape x
  refine ⟨pair,matching,?_⟩
  intro view claim polys opening claimRead polyRead
  exact (endpoint view claim polys opening claimRead polyRead).2

#print axioms of_original
end AspisR1.FIr_GlobalOwners
end

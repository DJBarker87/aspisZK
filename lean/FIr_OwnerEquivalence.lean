import FIr_GlobalOwners2
import FIr_Weaker
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_OwnerEquivalence
open Aeneas Aeneas.Std Result
open DrvC_Installation

theorem project {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FIp_GlobalOwners.Owners c B) : FIr_GlobalOwners2.Owners c B := by
  intro s H e i p q data t prepared calls shape x
  obtain ⟨pair,matching,endpoint⟩ := old s H e i p q data t prepared calls shape x
  refine ⟨pair,matching,?_⟩
  intro view claim polys opening claimRead polyRead
  exact (endpoint view claim polys opening claimRead polyRead).2.2

theorem equivalent {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    FIr_GlobalOwners2.Owners c B ↔ FIp_GlobalOwners.Owners c B :=
  ⟨fun h=>FIr_GlobalOwners.complete c B (FIr_GlobalOwners2.complete c B h),project c B⟩

#print axioms project
#print axioms equivalent
end AspisR1.FIr_OwnerEquivalence
end

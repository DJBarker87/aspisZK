import FJu_GlobalOwners
import FJp_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_Nonvacuity

theorem owners {F C : Type} (c : DrvC_Installation.Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : Nonempty (FJp_GlobalOwners.Owners c B)) :
    Nonempty (FJu_GlobalOwners.Owners c B) := by
  rcases old with ⟨h⟩
  exact ⟨FJu_GlobalOwners.weaken c B h⟩

theorem equivalent {F C : Type} (c : DrvC_Installation.Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    FJp_GlobalOwners.Owners c B ↔ FJu_GlobalOwners.Owners c B :=
  ⟨FJu_GlobalOwners.weaken c B,FJu_GlobalOwners.complete c B⟩

#print axioms owners
#print axioms equivalent
#print axioms AspisR1.ARX_Nonvacuity.conditional
#print axioms AspisR1.FJo_Nonvacuity.decoded
#print axioms AspisR1.FJl_Nonvacuity.scalar
end AspisR1.FJu_Nonvacuity
end

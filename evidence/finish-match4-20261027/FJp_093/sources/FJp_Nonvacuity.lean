import FJp_GlobalOwners
import ARX_Nonvacuity
import FJo_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_Nonvacuity
/-- Removing the owner matching family preserves every old satisfying instance.
This does not assert joint native/runtime premise inhabitation. -/
theorem owners {F C : Type} (c : DrvC_Installation.Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : Nonempty (FIp_GlobalOwners.Owners c B)) :
    Nonempty (FJp_GlobalOwners.Owners c B) := by
  rcases old with ⟨h⟩
  exact ⟨FJp_GlobalOwners.weaken c B h⟩
#print axioms owners
#print axioms AspisR1.ARX_Nonvacuity.conditional
#print axioms AspisR1.FJo_Nonvacuity.decoded
#print axioms AspisR1.FJl_Nonvacuity.scalar
end AspisR1.FJp_Nonvacuity
end

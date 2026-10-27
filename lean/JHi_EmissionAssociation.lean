import JHi_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_EmissionAssociation
open Aeneas Aeneas.Std Result DrvC_Installation
/-- Exact installed slot association to the checked emission model. Native
return-data syscall and ELF correspondence are not asserted. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (JHi_Configuration.value c err)).op53=JHb_EmitAdapter.source := by
  cases c
  rfl
#print axioms source
end AspisR1.JHi_EmissionAssociation
end

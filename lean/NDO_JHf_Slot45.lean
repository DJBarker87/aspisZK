import NDO_JHf_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_Slot45
open Aeneas Aeneas.Std Result DrvC_Installation

theorem fixed {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (JHd_ReferenceSlots.install (sdk (JHf_Configuration.value c err))).op45=
      (sdk (JHf_Configuration.value c err)).op45 := by
  cases c
  rfl
#print axioms fixed
end AspisR1.JHf_Slot45
end

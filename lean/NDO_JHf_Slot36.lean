import NDO_JHf_Configuration
import JHf_KeyEq
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_Slot36
open Aeneas Aeneas.Std Result DrvC_Installation

theorem fixed {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (JHd_ReferenceSlots.install (sdk (JHf_Configuration.value c err))).op36=
      (sdk (JHf_Configuration.value c err)).op36 := by
  change JHd_KeyStd.keyEq=Hist_Authority.keyEq
  funext left right
  exact JHf_KeyEq.key left right
#print axioms fixed
end AspisR1.JHf_Slot36
end

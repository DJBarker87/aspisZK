import JHd_Validation
import JHb_EmitInstall
import JGx_CallerSeed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHd_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation

def select {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  JHb_EmitInstall.value {c with adapter:=JHd_ReferenceSlots.install c.adapter}
def value {C : Type} (c : Configuration FIo_Install.W C) (err : C) :=
  JGx_Configuration.value (JGx_CallerSeed.value (select c)) err

theorem fixed {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JHd_ReferenceSlots.install (DrvC_Installation.sdk (value c err))=
      DrvC_Installation.sdk (value c err) := by
  cases c
  rfl
#print axioms fixed

theorem emission {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (value c err)).op53 JGx_RealStatement.value=ok (.Ok ()) := by
  exact JHb_EmitInstall.accepted (JGx_CallerSeed.value
    {c with adapter:=JHd_ReferenceSlots.install c.adapter}) err
#print axioms emission
end AspisR1.JHd_Configuration
end

import JGx_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_AdapterEmit
open Aeneas Aeneas.Std Result DrvC_Installation

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (JGx_Configuration.value c err)).op53=c.adapter.op53 := by
  cases c
  rfl
#print axioms source
end AspisR1.JGx_AdapterEmit
end

import NDO_JHb_EmitAdapter
import NDO_JGx_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_EmitInstall
open Aeneas Aeneas.Std Result DrvC_Installation

def value {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with adapter:={c.adapter with op53:=JHb_EmitAdapter.source}}

theorem slot {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (JGx_Configuration.value (value c) err)).op53=JHb_EmitAdapter.source := by
  cases c
  rfl
#print axioms slot

theorem accepted {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (JGx_Configuration.value (value c) err)).op53 JGx_RealStatement.value=ok (.Ok ()) := by
  rw [slot]
  exact JHb_EmitAdapter.accepted
#print axioms accepted
end AspisR1.JHb_EmitInstall
end

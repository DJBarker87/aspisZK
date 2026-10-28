import NCX_Install
import NCV_InstallationSupport
set_option autoImplicit false
noncomputable section
namespace NCX_Install
open Aeneas Aeneas.Std Result AspisR1
def configure {F E : Type} (missing : DrvC_Installation.Configuration F E) :=
  {NCV_InstallationSupport.configure missing with adapter:=install (NCV_Install.install missing.adapter)}
theorem sdk_selected {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op33=op33 ∧
    (DrvC_Installation.sdk (configure missing)).op34=op34 := ⟨rfl,rfl⟩
theorem ncv_retained {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (configure missing).adapter.op48=NCV_Install.op48 ∧
    (configure missing).adapter.op49=NCV_Install.op49 ∧
    (configure missing).adapter.op50=NCV_Install.op50 := ⟨rfl,rfl,rfl⟩
#print axioms sdk_selected
#print axioms ncv_retained
end NCX_Install
end

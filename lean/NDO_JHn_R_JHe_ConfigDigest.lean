import NDO_JHe_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ConfigDigest
open Aeneas Aeneas.Std Result DrvC_Installation

theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentDigest (JHe_Configuration.value adapter stage)=JGr_Geometry.digest := by
  rfl
#print axioms source
end AspisR1.JHe_ConfigDigest
end

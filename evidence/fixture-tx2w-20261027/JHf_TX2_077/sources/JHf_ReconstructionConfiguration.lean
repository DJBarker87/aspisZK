import JHf_Configuration
import JHf_ReconstructionSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_ReconstructionConfiguration
open Aeneas Aeneas.Std Result DrvC_Installation

def seed {C : Type} (c : Configuration FIo_Install.W C) :=
  {c with adapter:={c.adapter with op52:=JHf_ReconstructionSlot.source}}
def value {C : Type} (c : Configuration FIo_Install.W C) (err : C) :=
  JHf_Configuration.value (seed c) err

theorem slot {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op52=JHf_ReconstructionSlot.source := by cases c;rfl
#print axioms slot

theorem decoder {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op23 JHb_DataRequest.value=ok (.Ok JHd_RequestCarrier.actual) :=
  JHd_RequestNative.source
#print axioms decoder
end AspisR1.JHf_ReconstructionConfiguration
end

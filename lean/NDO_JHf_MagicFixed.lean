import NDO_JHf_Slot02
import NDO_JHf_Slot04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_MagicFixed
open Aeneas Aeneas.Std Result DrvC_Installation

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JGx_MagicStd.install (sdk (JHf_Configuration.value c err))=sdk (JHf_Configuration.value c err) := by
  have h2:=JHf_Slot02.fixed c err
  have h4:=JHf_Slot04.fixed c err
  generalize h : sdk (JHf_Configuration.value c err)=ops at *
  cases ops
  cases h2
  cases h4
  rfl
#print axioms source

theorem real {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JGx_MagicGate.value (sdk (JHf_Configuration.value c err)) JHb_DataRequest.value=ok false := by
  have h:=JHb_RequestCarrier.magic (sdk (JHf_Configuration.value c err))
  rw [source] at h
  exact h
#print axioms real
end AspisR1.JHf_MagicFixed
end

import JHf_Slot02
import JHf_Slot04
import JHf_Slot09
import JHf_Slot12
import JHf_Slot36
import JHf_Slot37
import JHf_Slot39
import JHf_Slot40
import JHf_Slot45
import JHf_Slot46
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_KeyFixed
open Aeneas Aeneas.Std Result DrvC_Installation
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JHd_KeyStd.install (sdk (JHf_Configuration.value c err))=sdk (JHf_Configuration.value c err) := by
  have h2:=JHf_Slot02.fixed c err
  have h4:=JHf_Slot04.fixed c err
  have h9:=JHf_Slot09.fixed c err
  have h12:=JHf_Slot12.fixed c err
  have h36:=JHf_Slot36.fixed c err
  have h37:=JHf_Slot37.fixed c err
  have h39:=JHf_Slot39.fixed c err
  have h40:=JHf_Slot40.fixed c err
  have h45:=JHf_Slot45.fixed c err
  have h46:=JHf_Slot46.fixed c err
  generalize h : sdk (JHf_Configuration.value c err)=ops at *
  cases ops
  cases h2
  cases h4
  cases h9
  cases h12
  cases h36
  cases h37
  cases h39
  cases h40
  cases h45
  cases h46
  rfl
#print axioms source
end AspisR1.JHf_KeyFixed
end

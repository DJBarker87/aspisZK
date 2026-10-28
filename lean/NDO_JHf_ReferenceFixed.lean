import NDO_JHf_Slot02
import NDO_JHf_Slot04
import NDO_JHf_Slot09
import NDO_JHf_Slot12
import NDO_JHf_Slot13
import NDO_JHf_Slot14
import NDO_JHf_Slot16
import NDO_JHf_Slot17
import NDO_JHf_Slot18
import NDO_JHf_Slot19
import NDO_JHf_Slot20
import NDO_JHf_Slot23
import NDO_JHf_Slot36
import NDO_JHf_Slot37
import NDO_JHf_Slot39
import NDO_JHf_Slot40
import NDO_JHf_Slot45
import NDO_JHf_Slot46
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_ReferenceFixed
open Aeneas Aeneas.Std Result DrvC_Installation
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JHd_ReferenceSlots.install (sdk (JHf_Configuration.value c err))=sdk (JHf_Configuration.value c err) := by
  have h2:=JHf_Slot02.fixed c err
  have h4:=JHf_Slot04.fixed c err
  have h9:=JHf_Slot09.fixed c err
  have h12:=JHf_Slot12.fixed c err
  have h13:=JHf_Slot13.fixed c err
  have h14:=JHf_Slot14.fixed c err
  have h16:=JHf_Slot16.fixed c err
  have h17:=JHf_Slot17.fixed c err
  have h18:=JHf_Slot18.fixed c err
  have h19:=JHf_Slot19.fixed c err
  have h20:=JHf_Slot20.fixed c err
  have h23:=JHf_Slot23.fixed c err
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
  cases h13
  cases h14
  cases h16
  cases h17
  cases h18
  cases h19
  cases h20
  cases h23
  cases h36
  cases h37
  cases h39
  cases h40
  cases h45
  cases h46
  rfl
#print axioms source
end AspisR1.JHf_ReferenceFixed
end

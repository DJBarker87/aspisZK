import NDO_JHf_Scan
import NDO_JHd_ReferenceSlots
import NDO_JHb_EmitInstall
import NDO_JGx_CallerSeed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation

def select {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  JHb_EmitInstall.value {c with adapter:={JHd_ReferenceSlots.install c.adapter with op51:=JHf_Scan.source}}
def value {C : Type} (c : Configuration FIo_Install.W C) (err : C) :=
  JGx_Configuration.value (JGx_CallerSeed.value (select c)) err

theorem scan {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op51 JHb_Header.account=ok (.Ok JHd_ScanValue.value) :=
  JHf_Scan.real
#print axioms scan

theorem emission {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op53 JGx_RealStatement.value=ok (.Ok ()) :=
  JHb_EmitInstall.accepted {c with adapter:={JHd_ReferenceSlots.install c.adapter with op51:=JHf_Scan.source}} err
#print axioms emission
end AspisR1.JHf_Configuration
end

import NDO_JHf_Configuration
import NDO_JHf_MagicFixed
import NDO_JHf_ReconstructionSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation
/-- Install the complete extracted reconstruction body with its explicit
carrier conversion. Account decoders/PDA/registry leaves remain uninstalled. -/
def base {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with adapter:={c.adapter with op52:=JHf_ReconstructionSlot.source}}
def value {C : Type} (c : Configuration FIo_Install.W C) (err : C) :=
  JHf_Configuration.value (base c) err

theorem reconstruction_slot {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op52=JHf_ReconstructionSlot.source := by
  cases c
  rfl
#print axioms reconstruction_slot

theorem magic {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    JGx_MagicGate.value (sdk (value c err)) JHb_DataRequest.value=ok false :=
  JHf_MagicFixed.real (base c) err
#print axioms magic

theorem emission_model {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (value c err)).op53 JGx_RealStatement.value=ok (.Ok ()) :=
  JHf_Configuration.emission (base c) err
#print axioms emission_model
end AspisR1.JHi_Configuration
end

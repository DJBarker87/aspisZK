import JGx_MagicStd
import JGx_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_CallerStd
open Aeneas Aeneas.Std Result DrvC_Installation

def value {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with adapter:=JGx_MagicStd.install c.adapter}

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) (payload : Array U8 316#usize) :
    JGx_MagicGate.value (DrvC_Installation.sdk (JGx_Configuration.value (value c) err))
      (JGx_RequestBytes.value payload)=ok false := by
  exact JGx_MagicStd.source (DrvC_Installation.sdk (JGx_Configuration.value (value c) err)) payload
#print axioms source
end AspisR1.JGx_CallerStd
end

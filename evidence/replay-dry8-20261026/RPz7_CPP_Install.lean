import RPz7_DrvC_FirstConstants
import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Install
open Aeneas Aeneas.Std Result

/-- Concrete source interpretation of two pure SDK/std leaves. It changes no
shipped code and supplies no native/source acceptance or history conclusion.
The owned native extraction boundary remains indexed by this installation. -/
def configuration {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.Configuration F C :=
  {c with adapter := {c.adapter with op36 := Hist_Authority.keyEq, op35 := fun e => ok e}}

theorem key {F C : Type} (c : DrvC_Installation.Configuration F C) :
    (DrvC_Installation.sdk (DrvC_FirstConstants.configuration (configuration c))).op36 = Hist_Authority.keyEq := rfl

theorem clone {F C : Type} (c : DrvC_Installation.Configuration F C) :
    (DrvC_Installation.sdk (DrvC_FirstConstants.configuration (configuration c))).op35 = (fun e => ok e) := rfl

#print axioms key
#print axioms clone
end AspisR1.CPP_Install
end

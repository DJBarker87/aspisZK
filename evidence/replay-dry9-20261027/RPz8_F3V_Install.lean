import RPz8_F3V_AllWorldInput
import RPz7_F3M_CircleSource
set_option autoImplicit false
namespace AspisR1.F3V_Install

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.Configuration F C :=
  {c with boundaries:=F3M_CircleSource.install c.boundaries}

theorem boundaries {F C : Type} (c : DrvC_Installation.Configuration F C) :
    (configuration c).boundaries=F3M_CircleSource.install c.boundaries := rfl

#print axioms boundaries
end AspisR1.F3V_Install

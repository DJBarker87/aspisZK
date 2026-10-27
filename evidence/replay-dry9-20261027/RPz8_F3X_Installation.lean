import RPz8_F3V_Install
import RPz7_Rc2_Install
set_option autoImplicit false
namespace AspisR1.F3X_Installation

def configuration {F C : Type} (base : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  F3V_Install.configuration (Rc2_Install.configuration base reservation)

theorem native_configuration {F C : Type} (base : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    Rc2_Install.configuration (F3V_Install.configuration base) reservation=
      configuration base reservation := rfl

theorem standard {F C : Type} (base : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration base reservation).std=NP6_StdModel.calls reservation := rfl

theorem circle {F C : Type} (base : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration base reservation).boundaries.circle=F3M_CircleSource.source := rfl

#print axioms native_configuration
#print axioms standard
#print axioms circle
end AspisR1.F3X_Installation

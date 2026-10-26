import Rc2_Install
import CPP_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Install
/-- Select both existing source instances; all other configuration fields survive. -/
def select {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  CPP_Install.configuration (Rc2_Install.select c reservation)
def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  DrvC_FirstConstants.configuration (select c reservation)
theorem rc2 {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    configuration c reservation = Rc2_Install.configuration (CPP_Install.configuration c) reservation := rfl
theorem key {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (configuration c reservation)).op36 = Hist_Authority.keyEq := rfl
theorem standard {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration c reservation).std = NP6_StdModel.calls reservation := rfl
#print axioms rc2
#print axioms key
#print axioms standard
end AspisR1.CPH_Install
end

import Rc4_Install
import CPH_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc5_Install
open DrvC_Installation
def seed {F C : Type} (err : C) (c : Configuration F C) :=
  SAQ_CompleteInstall.select err (CPP_Install.configuration c)
def configuration {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) := Rc3_Install.configuration (seed err c) r
theorem rc4 {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = Rc4_Install.configuration err (CPP_Install.configuration c) r := rfl
theorem saf {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = Rc3_Install.configuration (seed err c) r := rfl
theorem cph {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = CPH_Install.configuration
      {SAQ_CompleteInstall.select err c with boundaries := F3M_CircleSource.install c.boundaries} r := rfl
theorem key {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (sdk (configuration err c r)).op36 = Hist_Authority.keyEq := rfl
#print axioms rc4
#print axioms saf
#print axioms cph
#print axioms key
end AspisR1.Rc5_Install
end

import FIq_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_FinalInstall
open DrvC_Installation

/-- FIr removes logical premises without changing the adopted FIq dictionary. -/
abbrev configuration := @FIq_Install.configuration

theorem unchanged {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    configuration err c r=FIq_Install.configuration err c r := rfl

theorem terminal_fixed {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (configuration err c r).boundaries.terminal=FIq_Terminal.terminal := rfl

#print axioms unchanged
#print axioms terminal_fixed
end AspisR1.FIr_FinalInstall
end

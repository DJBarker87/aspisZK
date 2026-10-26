import RPz7_F3V_AllWorldPair
import RPz7_Cons_NativeBuild
set_option autoImplicit false
namespace AspisR1.F3V_SecondSlots

theorem same {F C : Type} (c : DrvC_Installation.Configuration F C) :
    GExp_SecondCode.installed (DrvC_Installation.stage c) c.reserved=
      Tx2I_Install.stage
        (Tx2N_Execution.control (Op5T_Concrete.stage (AuS1_Install.base c.stageBase))
          c.reserved c.query c.geometry) c.finish := by
  cases c
  rfl

#print axioms same
end AspisR1.F3V_SecondSlots

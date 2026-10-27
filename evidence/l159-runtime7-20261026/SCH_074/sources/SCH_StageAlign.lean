import Rc5_Install
set_option autoImplicit false
namespace AspisR1.SCH_StageAlign

theorem library {F C : Type} (c : DrvC_Installation.Configuration F C) :
    AuS1_Install.base (DrvC_FirstConstants.configuration c).stageBase =
      (DrvC_FirstConstants.configuration c).stageBase := rfl

#print axioms library
end AspisR1.SCH_StageAlign

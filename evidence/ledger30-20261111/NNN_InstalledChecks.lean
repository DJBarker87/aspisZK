import FIN_COMBINED_IMPORT
import NVR_TAS
import NVR_TasRoots
import LIB_FullInstances
set_option autoImplicit false
noncomputable section
namespace NNN_InstalledChecks
open RSL
abbrev L := LIBB_PoolLib.library
abbrev V := LIBB_V2Star.library
abbrev VL := LIB_Instances.VL
/-- Install the literal CLOSED children before applying the wrapper/dispatcher folds. -/
def children (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices) : TAS.Impl L V VL :=
 { I with f345 := AspisR1.NNG_TotalProducer345.producer,
          f241 := NMX_R9_StageTwo.stage2 ch }
def installed (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices)
 (a2 : NMV_ConcreteWindows.Allocation) : TAS.Impl L V VL :=
 NVR_TAS.install (NVR_TasRoots.implementation (children I ch)
  AspisR1.NNG_Candidate344.allocation a2)
theorem f344_same (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices)
 (a2 : NMV_ConcreteWindows.Allocation) :
 (installed I ch a2).f344 = AspisR1.NNG_Candidate344.producer := rfl
theorem f240_same (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices)
 (a2 : NMV_ConcreteWindows.Allocation) :
 (installed I ch a2).f240 = FIN_240.producer ch a2 := rfl
theorem process_same (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices)
 (a2 : NMV_ConcreteWindows.Allocation) :
 (installed I ch a2).process = FIN_333.producer ch a2 := rfl
theorem entry_same (I : TAS.Impl L V VL) (ch : NMX_R4_Authentication.Choices)
 (a2 : NMV_ConcreteWindows.Allocation) :
 (installed I ch a2).entry = FIN_330.producer ch a2 := rfl
#print axioms f344_same
#print axioms f240_same
#print axioms process_same
#print axioms entry_same
end NNN_InstalledChecks
end

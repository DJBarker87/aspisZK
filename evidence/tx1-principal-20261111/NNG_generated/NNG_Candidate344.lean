import NNG_Candidate345
import NMV_ConcreteWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate344

/-- Fixed silent local-allocation interpretation, with the complete SDK/std
source-fission windows and original concrete345 child. -/
def allocation : NMV_ConcreteWindows.Allocation := fun _ _ _ _=>true
def producer := NMV_ConcreteWindows.stage1 allocation NNG_Producer345.producer

/-- Complete canonical344 instantiation under the retained ruling(bn)
source-fission certificate, with no library/child/accuracy hypothesis. -/
theorem candidate : RSL.TX1_344.RowSpec_344 LIB_Instances.VL LIB_Instances.P LIB_Instances.C producer :=
 NMV_ConcreteWindows.root344 LIB_Instances.VL LIB_Instances.P LIB_Instances.C allocation
  NNG_Producer345.producer NNG_Candidate345.candidate
#print axioms candidate
end AspisR1.NNG_Candidate344

import FIN_240
import NNG_Candidate344
import NVR_Folds
/-
FIN_ TX2:221 process (r1_pool_adapter.rs::process), one-step instantiation.
Fold:   NVR_Folds.process_tx2 (rev4 re-pin of NNF_Folds.process_tx2; awaited).
Children: AspisR1.NNG_Candidate344.candidate (TX1:344, d3fcd82238b) on the stage1
        route and FIN_240.candidate on the ASQ8 route.
Library: LIB_FullInstances L / D / V0 / VL / P / C.
Statement: RowSpec_221 exactly, with S1 = TX1_344.asStage1 VL P C.
-/
set_option autoImplicit false
noncomputable section
namespace FIN_221
open RSL

abbrev L := LIB_FullInstances.L
abbrev D := LIB_FullInstances.D
abbrev V := LIB_FullInstances.V0
abbrev VL := LIB_FullInstances.VL
abbrev P := LIB_FullInstances.P
abbrev C := LIB_FullInstances.C

def producer (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) : NVR_Dispatch.Child :=
  NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
    (FIN_240.producer choices allocation)

theorem candidate (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) :
    TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) (producer choices allocation) :=
  NVR_Folds.process_tx2 L D V VL P C _ _
    AspisR1.NNG_Candidate344.candidate (FIN_240.candidate choices allocation)

#print axioms candidate
end FIN_221
end

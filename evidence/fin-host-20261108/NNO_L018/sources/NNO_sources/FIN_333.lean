import FIN_240
import NNG_Candidate344
import NVR_Folds
/-
FIN_ TX1:333 process (r1_pool_adapter.rs::process, TX1 occurrence), one-step
instantiation over BOTH admitted routes.
Fold:   NVR_Folds.process_tx1 (rev4 re-pin of NNF_Folds.process_tx1; awaited).
Children: AspisR1.NNG_Candidate344.candidate (stage1) and FIN_240.candidate (stage2),
        i.e. the row needs 344 AND 240 (TGA_ G2).
Statement: RowSpec_333 exactly. The producer is the same function as
FIN_221.producer (checked by rfl in FIN_COMBINED_IMPORT).
-/
set_option autoImplicit false
noncomputable section
namespace FIN_333
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
    TX1_333.RowSpec_333 L D V VL P C (producer choices allocation) :=
  NVR_Folds.process_tx1 L D V VL P C _ _
    AspisR1.NNG_Candidate344.candidate (FIN_240.candidate choices allocation)

#print axioms candidate
end FIN_333
end

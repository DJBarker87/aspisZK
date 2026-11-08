import FIN_221
/-
FIN_ TX2:213 entry (lib.rs::process_r1_cost_probe_instruction), one-step
instantiation.
Fold:   NVR_Folds.entry_tx2 (rev4 re-pin of NNF_Folds.entry_tx2; awaited).
Child:  FIN_221.candidate.
Statement: RowSpec_213 exactly. Its Domain keeps (E1) = (D2') Root0 on the ASQ8
route at V0; that clause is not discharged here (see FIN_CALLER_CLAUSES.json).
-/
set_option autoImplicit false
noncomputable section
namespace FIN_213
open RSL

abbrev L := LIB_FullInstances.L
abbrev D := LIB_FullInstances.D
abbrev V := LIB_FullInstances.V0
abbrev VL := LIB_FullInstances.VL
abbrev P := LIB_FullInstances.P
abbrev C := LIB_FullInstances.C

def producer (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) : NVR_Dispatch.Child :=
  NVR_Dispatch.entry (FIN_221.producer choices allocation)

theorem candidate (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) :
    TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) (producer choices allocation) :=
  NVR_Folds.entry_tx2 L D V VL P C _ (FIN_221.candidate choices allocation)

#print axioms candidate
end FIN_213
end

import FIN_333
/-
FIN_ TX1:330 entry (lib.rs::process_r1_cost_probe_instruction, TX1 occurrence),
one-step instantiation.
Fold:   NVR_Folds.entry_tx1 (rev4 re-pin of NNF_Folds.entry_tx1; awaited).
Child:  FIN_333.candidate.
Statement: RowSpec_330 exactly. Same (E1) Root0 caller clause as TX2:213.
-/
set_option autoImplicit false
noncomputable section
namespace FIN_330
open RSL

abbrev L := LIB_FullInstances.L
abbrev D := LIB_FullInstances.D
abbrev V := LIB_FullInstances.V0
abbrev VL := LIB_FullInstances.VL
abbrev P := LIB_FullInstances.P
abbrev C := LIB_FullInstances.C

def producer (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) : NVR_Dispatch.Child :=
  NVR_Dispatch.entry (FIN_333.producer choices allocation)

theorem candidate (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) :
    TX1_330.RowSpec_330 L D V VL P C (producer choices allocation) :=
  NVR_Folds.entry_tx1 L D V VL P C _ (FIN_333.candidate choices allocation)

#print axioms candidate
end FIN_330
end

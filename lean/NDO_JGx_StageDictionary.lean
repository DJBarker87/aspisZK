import NDO_JGc_TX2_InstalledQuery
import RPz7_Op5T_Concrete
import Port1_Library
import RPz7_AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_StageDictionary
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

def library (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
  AuS1_Install.base (Port1_Library.install (Port1_Library.std base))

def source {C : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geo : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops) : VTop_Stages.Ops :=
  Tx2I_Install.stage (Op5T_Concrete.stage (Tx2N_Execution.control (library base) true
    (JGc_TX2_InstalledQuery.raw query) (SAQ_Constructor.install err geo))) (FIo_Install.finishOps (.Ok ()) seed)

theorem slots {C : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geo : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops) :
    (source base seed err geo query).op16=ok 10#usize ∧
    (source base seed err geo query).op23=ok 7495#usize ∧
    (source base seed err geo query).op22=ok 7527#usize ∧
    (source base seed err geo query).op15=ok 7751#usize ∧
    (source base seed err geo query).op14=ok 7783#usize ∧
    (source base seed err geo query).op21=ok 8007#usize ∧
    (source base seed err geo query).op20=ok 10055#usize := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms slots
end AspisR1.JGx_StageDictionary
end

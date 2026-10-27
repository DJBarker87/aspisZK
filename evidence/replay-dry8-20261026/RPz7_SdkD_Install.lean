import RPz7_SdkD_ReaderQueries
import RPz7_Tx2N_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Install
open Aeneas Aeneas.Std Result

/-- Literal folded-root source offsets and unwrap; the remaining installed
inner slots are Tx2N's. This only specializes previously free source slots. -/
def stage {CoreError : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) : VTop_Stages.Ops :=
  {Tx2N_Execution.control base reserved query geo with
    op14 := ok 7783#usize,op15 := ok 7751#usize,unwrap32 := Port4B_FoldedCut.unwrap32}

theorem commute {CoreError : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) :
    Op5T_Concrete.stage (stage base reserved query geo) =
      stage (Op5T_Concrete.stage base) reserved query geo := by cases base; rfl

theorem inner {CoreError : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) :
    stage base reserved query geo =
      Tx2N_Execution.control
        {base with op14 := ok 7783#usize,op15 := ok 7751#usize,unwrap32 := Port4B_FoldedCut.unwrap32}
        reserved query geo := by cases base; rfl

#print axioms commute
#print axioms inner
end AspisR1.SdkD_Install
end

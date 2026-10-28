import NDO_JGn_CurrentPreparation
import NDO_JGi_TX1Ready
set_option autoImplicit false
namespace AspisR1.JGp_PrepareLayout
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

def installed {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) : Ops :=
  WAdm_Execution.actual base true query geo JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))

theorem logical {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) :
    compact.LOGICAL_SEMANTIC (installed base query geo)=ok 13831#usize := by
  unfold compact.LOGICAL_SEMANTIC
  rfl
#print axioms logical

theorem y1 : compact.LOGICAL_Y1=ok 928#usize := by
  unfold compact.LOGICAL_Y1
  apply UsizeArithmetic.mul_eq_ok <;> scalar_tac
#print axioms y1

theorem semantic {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) :
    compact.OFF_SEMANTIC (installed base query geo)=ok 16#usize := by
  unfold compact.OFF_SEMANTIC
  rfl
#print axioms semantic

theorem offsetY1 {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) :
    compact.OFF_Y1 (installed base query geo)=ok 7031#usize := by
  unfold compact.OFF_Y1
  rw [semantic,bind_tc_ok]
  change (16#usize + 7015#usize)=ok 7031#usize
  apply UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms offsetY1

theorem inactive {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) :
    compact.OFF_INACTIVE (installed base query geo)=ok 7495#usize := by
  unfold compact.OFF_INACTIVE
  rw [offsetY1,bind_tc_ok]
  change (7031#usize + 464#usize)=ok 7495#usize
  apply UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms inactive
end AspisR1.JGp_PrepareLayout

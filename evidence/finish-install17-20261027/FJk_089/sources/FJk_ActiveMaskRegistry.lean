import FJh_Base
import FIq_Native13
import R0P.Copy
set_option autoImplicit false
namespace AspisR1.FJk_ActiveMaskRegistry
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
/-- Fixed64 small mask words,without evaluating any field operation. -/
theorem value (i : Fin 64) :
    (FJh_Base.cell constants.ACTIVE_ROW_MASKS i).val=R0P.copyActiveRowMasks i := by
  unfold constants.ACTIVE_ROW_MASKS
  fin_cases i <;> rfl
#print axioms value
end AspisR1.FJk_ActiveMaskRegistry

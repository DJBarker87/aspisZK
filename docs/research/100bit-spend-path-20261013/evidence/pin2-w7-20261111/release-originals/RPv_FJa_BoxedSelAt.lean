import RPv_FJa_BoxedLiteral
import RPv_FJa_TensorAtPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_BoxedSelAt
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
/-- Literal selector meaning of the ORIGINAL boxed body at the SAME point;
this association is DERIVED, not an interface assumption. -/
theorem value (point : Array NQ 10#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : FIw_ArrayValue.canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    FIw_PublicModel.selector s=R0P.SemSource.selAt (FIw_ArrayValue.decoded point) := by
  rw [FJa_BoxedLiteral.value point s hp run,FJa_TensorAtPoint.list]
  funext row
  exact FJa_TensorAtPoint.ofFn _ row
#print axioms value
end AspisR1.FJa_BoxedSelAt
end

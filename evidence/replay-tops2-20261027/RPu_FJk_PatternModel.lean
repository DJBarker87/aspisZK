import RPu_FJk_PatternValuesRaw
import RPu_FJk_PatternRegistry
import RPu_FJk_CopyRowTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded)
/-- SAME source pattern, powers and opening cells, identified with the R0P fold. -/
theorem value (a powers : Array field.QM31 16#usize) (lambda : field.QM31)
    (h : decoded powers=fun i=>decode lambda^(i.val+1)) (j : Fin 14) :
    FJk_PatternOuterValue.model a powers j=R0P.copyPatternValuesLiteral (decoded a) (decode lambda) j := by
  unfold FJk_PatternOuterValue.model FJk_PatternInnerValue.model FJk_PatternInnerValue.indices
  rw [List.drop_zero,FJk_PatternRegistry.value]
  unfold R0P.copyPatternValuesLiteral
  apply congrArg (fun step : K → Fin 16 → K=>(List.ofFn id).foldl step 0)
  funext acc i
  unfold FJk_PatternCellValue.step
  rw [FJk_CopyRowTransport.cell powers i,h,R0P.copy_powers_eq,
    FJk_CopyRowTransport.cell a ((R0P.copyPatterns j).columns i)]
#print axioms value
end AspisR1.FJk_PatternModel
end

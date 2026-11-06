import NJX_PatternModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternMeaning05
open FIv_NativeValue (K)
open NJX_PatternModel (model atoms window)
theorem value (o : Fin 16 → K) (lambda : K) :
 model o lambda 5=R0P.copyPatternValuesLiteral o lambda 5 := by
 simp [model,NJX_PatternTail.expr,NJX_TailExpr.value,atoms,window,NJX_PatternPacket.starts,
  List.ofFn_succ,R0P.copyPatternValuesLiteral,R0P.copyPatterns,
  R0P.copyPattern5,R0P.copy_powers_eq] <;> ring
#print value
#print axioms value
end AspisR1.NJX_PatternMeaning05
end

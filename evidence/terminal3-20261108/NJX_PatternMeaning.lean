import NJX_PatternMeaning00
import NJX_PatternMeaning01
import NJX_PatternMeaning02
import NJX_PatternMeaning03
import NJX_PatternMeaning04
import NJX_PatternMeaning05
import NJX_PatternMeaning06
import NJX_PatternMeaning07
import NJX_PatternMeaning08
import NJX_PatternMeaning09
import NJX_PatternMeaning10
import NJX_PatternMeaning11
import NJX_PatternMeaning12
import NJX_PatternMeaning13
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternMeaning
open FIv_NativeValue (K)
theorem value (o : Fin 16 → K) (lambda : K) (j : Fin 14) :
 NJX_PatternModel.model o lambda j=R0P.copyPatternValuesLiteral o lambda j := by
 fin_cases j
 · exact NJX_PatternMeaning00.value o lambda
 · exact NJX_PatternMeaning01.value o lambda
 · exact NJX_PatternMeaning02.value o lambda
 · exact NJX_PatternMeaning03.value o lambda
 · exact NJX_PatternMeaning04.value o lambda
 · exact NJX_PatternMeaning05.value o lambda
 · exact NJX_PatternMeaning06.value o lambda
 · exact NJX_PatternMeaning07.value o lambda
 · exact NJX_PatternMeaning08.value o lambda
 · exact NJX_PatternMeaning09.value o lambda
 · exact NJX_PatternMeaning10.value o lambda
 · exact NJX_PatternMeaning11.value o lambda
 · exact NJX_PatternMeaning12.value o lambda
 · exact NJX_PatternMeaning13.value o lambda
#print value
#print axioms value
end AspisR1.NJX_PatternMeaning
end

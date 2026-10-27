import FJi_Coordinate0
import FJi_Coordinate1
import FJi_Coordinate2
import FJi_Coordinate3
import FJi_Coordinate4
import FJi_Coordinate5
import FJi_Coordinate6
import FJi_Coordinate7
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_EightValue
open Aeneas Aeneas.Std Result
open FJi_Accumulations FJi_LaneValue
open FJf_U64Array (cell)
theorem value (c : Coefficients) (a : U32) (s out : Sums)
    (run : accumulate c a s=ok out) (j : Nat) (hj : j<8) :
    (cell out j).val=(cell s j).val+(word c j).val*a.val := by
  interval_cases j
  · exact FJi_Coordinate0.value c a s out run
  · exact FJi_Coordinate1.value c a s out run
  · exact FJi_Coordinate2.value c a s out run
  · exact FJi_Coordinate3.value c a s out run
  · exact FJi_Coordinate4.value c a s out run
  · exact FJi_Coordinate5.value c a s out run
  · exact FJi_Coordinate6.value c a s out run
  · exact FJi_Coordinate7.value c a s out run
#print axioms value
end AspisR1.FJi_EightValue
end

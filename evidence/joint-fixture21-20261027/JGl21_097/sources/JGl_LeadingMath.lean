import JGl_LeadingAbsorb
import JGl_LeadingExternal
import JGl_LeadingPow0
import JGl_LeadingMid
import JGl_LeadingPow1
import JGl_LeadingFinal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_LeadingMath
open FIw_ArrayValue (decoded)
/-- The closed leading mathematical vector, composed from six individually
certified phases instead of expanding the two-round reduction graph. -/
theorem value : R0P.poseidonLeadingPair (decoded JGl_NumericData.a) (decoded JGl_NumericData.c)=
    decoded JGl_VectorData.leading := by
  unfold R0P.poseidonLeadingPair
  dsimp only
  erw [JGl_LeadingAbsorb.value,JGl_LeadingExternal.value]
  unfold R0P.poseidonFullRound
  dsimp only
  erw [JGl_LeadingPow0.value,JGl_LeadingMid.value,JGl_LeadingPow1.value,JGl_LeadingFinal.value]
#print axioms value
end AspisR1.JGl_LeadingMath
end

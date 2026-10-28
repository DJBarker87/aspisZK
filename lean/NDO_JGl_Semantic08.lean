import NDO_JFu_PublicSemantic
import NDO_JGl_WordProof
import NDO_JGl_NumericData
import RPv_FIy_NativeCoefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_Semantic08
open Aeneas Aeneas.Std FIq_Native
open FIw_ArrayValue (decoded)
/-- One bounded packed semantic coefficient on the diagnostic candidate
operands; the separate source-operand identification is still required. -/
theorem value : FIy_NativeCoefficients.model JFu_PublicSemantic.value
    JGl_NumericData.openings JGl_NumericData.selectors ⟨8,by decide⟩=
    decoded JGl_NumericData.semantic ⟨8,by decide⟩ := by
  jgl_words
#print axioms value
end AspisR1.JGl_Semantic08
end

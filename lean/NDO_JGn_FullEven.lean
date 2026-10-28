import NDO_JGn_FullPhaseData
import NDO_JGl_WordProof
import RPv_FJe_FullConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullEven
open FIw_ArrayValue (decoded)
theorem lane0 : FJe_FullConstants.even JGl_NumericData.low ⟨0,by decide⟩=decoded JGn_FullPhaseData.even ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : FJe_FullConstants.even JGl_NumericData.low ⟨1,by decide⟩=decoded JGn_FullPhaseData.even ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : FJe_FullConstants.even JGl_NumericData.low ⟨2,by decide⟩=decoded JGn_FullPhaseData.even ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : FJe_FullConstants.even JGl_NumericData.low ⟨3,by decide⟩=decoded JGn_FullPhaseData.even ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : FJe_FullConstants.even JGl_NumericData.low ⟨4,by decide⟩=decoded JGn_FullPhaseData.even ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : FJe_FullConstants.even JGl_NumericData.low ⟨5,by decide⟩=decoded JGn_FullPhaseData.even ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : FJe_FullConstants.even JGl_NumericData.low ⟨6,by decide⟩=decoded JGn_FullPhaseData.even ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : FJe_FullConstants.even JGl_NumericData.low ⟨7,by decide⟩=decoded JGn_FullPhaseData.even ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : FJe_FullConstants.even JGl_NumericData.low ⟨8,by decide⟩=decoded JGn_FullPhaseData.even ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : FJe_FullConstants.even JGl_NumericData.low ⟨9,by decide⟩=decoded JGn_FullPhaseData.even ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : FJe_FullConstants.even JGl_NumericData.low ⟨10,by decide⟩=decoded JGn_FullPhaseData.even ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : FJe_FullConstants.even JGl_NumericData.low ⟨11,by decide⟩=decoded JGn_FullPhaseData.even ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : FJe_FullConstants.even JGl_NumericData.low ⟨12,by decide⟩=decoded JGn_FullPhaseData.even ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : FJe_FullConstants.even JGl_NumericData.low ⟨13,by decide⟩=decoded JGn_FullPhaseData.even ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : FJe_FullConstants.even JGl_NumericData.low ⟨14,by decide⟩=decoded JGn_FullPhaseData.even ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : FJe_FullConstants.even JGl_NumericData.low ⟨15,by decide⟩=decoded JGn_FullPhaseData.even ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : FJe_FullConstants.even JGl_NumericData.low=decoded JGn_FullPhaseData.even := by
  funext i
  fin_cases i
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
  · exact lane8
  · exact lane9
  · exact lane10
  · exact lane11
  · exact lane12
  · exact lane13
  · exact lane14
  · exact lane15
#print axioms value
end AspisR1.JGn_FullEven
end

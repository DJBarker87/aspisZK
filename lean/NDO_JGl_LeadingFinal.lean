import NDO_JGl_LeadingPhaseData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_LeadingFinal
open FIw_ArrayValue (decoded)
theorem lane0 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨0,by decide⟩=decoded JGl_VectorData.leading ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨1,by decide⟩=decoded JGl_VectorData.leading ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨2,by decide⟩=decoded JGl_VectorData.leading ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨3,by decide⟩=decoded JGl_VectorData.leading ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨4,by decide⟩=decoded JGl_VectorData.leading ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨5,by decide⟩=decoded JGl_VectorData.leading ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨6,by decide⟩=decoded JGl_VectorData.leading ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨7,by decide⟩=decoded JGl_VectorData.leading ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨8,by decide⟩=decoded JGl_VectorData.leading ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨9,by decide⟩=decoded JGl_VectorData.leading ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨10,by decide⟩=decoded JGl_VectorData.leading ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨11,by decide⟩=decoded JGl_VectorData.leading ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨12,by decide⟩=decoded JGl_VectorData.leading ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨13,by decide⟩=decoded JGl_VectorData.leading ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨14,by decide⟩=decoded JGl_VectorData.leading ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1) ⟨15,by decide⟩=decoded JGl_VectorData.leading ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.powered1)=decoded JGl_VectorData.leading := by
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
end AspisR1.JGl_LeadingFinal
end

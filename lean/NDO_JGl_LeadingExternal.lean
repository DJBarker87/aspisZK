import NDO_JGl_LeadingPhaseData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_LeadingExternal
open FIw_ArrayValue (decoded)
theorem lane0 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨0,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨1,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨2,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨3,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨4,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨5,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨6,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨7,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨8,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨9,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨10,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨11,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨12,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨13,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨14,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed) ⟨15,by decide⟩=decoded JGl_LeadingPhaseData.external ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : R0P.poseidonExternalLinear (decoded JGl_LeadingPhaseData.absorbed)=decoded JGl_LeadingPhaseData.external := by
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
end AspisR1.JGl_LeadingExternal
end

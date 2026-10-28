import NDO_JGn_FullPhaseData
import NDO_JGl_WordProof
import RPv_FJe_FullConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullMid
open FIw_ArrayValue (decoded)
theorem lane0 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨0,by decide⟩=decoded JGn_FullPhaseData.mid ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨1,by decide⟩=decoded JGn_FullPhaseData.mid ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨2,by decide⟩=decoded JGn_FullPhaseData.mid ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨3,by decide⟩=decoded JGn_FullPhaseData.mid ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨4,by decide⟩=decoded JGn_FullPhaseData.mid ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨5,by decide⟩=decoded JGn_FullPhaseData.mid ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨6,by decide⟩=decoded JGn_FullPhaseData.mid ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨7,by decide⟩=decoded JGn_FullPhaseData.mid ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨8,by decide⟩=decoded JGn_FullPhaseData.mid ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨9,by decide⟩=decoded JGn_FullPhaseData.mid ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨10,by decide⟩=decoded JGn_FullPhaseData.mid ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨11,by decide⟩=decoded JGn_FullPhaseData.mid ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨12,by decide⟩=decoded JGn_FullPhaseData.mid ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨13,by decide⟩=decoded JGn_FullPhaseData.mid ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨14,by decide⟩=decoded JGn_FullPhaseData.mid ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0) ⟨15,by decide⟩=decoded JGn_FullPhaseData.mid ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0)=decoded JGn_FullPhaseData.mid := by
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
end AspisR1.JGn_FullMid
end

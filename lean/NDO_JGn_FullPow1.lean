import NDO_JGn_FullPhaseData
import NDO_JGl_WordProof
import RPv_FJe_FullConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullPow1
open FIw_ArrayValue (decoded)
theorem lane0 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨0,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨1,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨2,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨3,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨4,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨5,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨6,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨7,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨8,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨9,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨10,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨11,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨12,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨13,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨14,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j)) ⟨15,by decide⟩=decoded JGn_FullPhaseData.powered1 ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j))=decoded JGn_FullPhaseData.powered1 := by
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
end AspisR1.JGn_FullPow1
end

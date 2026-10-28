import NDO_JGn_FullPhaseData
import NDO_JGl_WordProof
import RPv_FJe_FullConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullPow0
open FIw_ArrayValue (decoded)
theorem lane0 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨0,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨1,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨2,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨3,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨4,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨5,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨6,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨7,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem lane8 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨8,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨8,by decide⟩ := by
  jgl_words
#print axioms lane8
theorem lane9 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨9,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨9,by decide⟩ := by
  jgl_words
#print axioms lane9
theorem lane10 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨10,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨10,by decide⟩ := by
  jgl_words
#print axioms lane10
theorem lane11 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨11,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨11,by decide⟩ := by
  jgl_words
#print axioms lane11
theorem lane12 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨12,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨12,by decide⟩ := by
  jgl_words
#print axioms lane12
theorem lane13 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨13,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨13,by decide⟩ := by
  jgl_words
#print axioms lane13
theorem lane14 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨14,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨14,by decide⟩ := by
  jgl_words
#print axioms lane14
theorem lane15 : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j)) ⟨15,by decide⟩=decoded JGn_FullPhaseData.powered0 ⟨15,by decide⟩ := by
  jgl_words
#print axioms lane15
theorem value : (fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j))=decoded JGn_FullPhaseData.powered0 := by
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
end AspisR1.JGn_FullPow0
end

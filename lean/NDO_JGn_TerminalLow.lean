import NDO_JGn_TerminalData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_TerminalLow
open FIv_NativeValue (decode)
open FIw_ArrayValue (cells)
attribute [local irreducible] HMul.hMul HAdd.hAdd HPow.hPow
theorem sem16 : FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta)
    (JGl_NumericData.semantic.val.drop 16)=decode JGn_TerminalData.sem16 := by
  jgl_words
#print axioms sem16
theorem sem08 : FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta)
    (JGl_NumericData.semantic.val.drop 8)=decode JGn_TerminalData.sem08 := by
  change (decode (cells JGl_NumericData.semantic ⟨8,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨9,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨10,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨11,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨12,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨13,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨14,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨15,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*(FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta) (JGl_NumericData.semantic.val.drop 16)))))))))))))))))=_
  rw [sem16]
  jgl_words
#print axioms sem08
theorem sem00 : FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta)
    (JGl_NumericData.semantic.val.drop 0)=decode JGn_TerminalData.sem00 := by
  change (decode (cells JGl_NumericData.semantic ⟨0,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨1,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨2,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨3,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨4,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨5,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨6,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*((decode (cells JGl_NumericData.semantic ⟨7,by decide⟩)+decode JFu_TerminalPrefix.challenges.theta*(FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta) (JGl_NumericData.semantic.val.drop 8)))))))))))))))))=_
  rw [sem08]
  jgl_words
#print axioms sem00
theorem poseidon : FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta)
    JGl_NumericData.poseidon.val=decode JGn_TerminalData.pos := by
  jgl_words
#print axioms poseidon
end AspisR1.JGn_TerminalLow
end

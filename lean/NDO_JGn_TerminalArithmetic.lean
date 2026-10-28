import NDO_JGn_TerminalPowers
import NDO_JGn_TerminalLow
import NDO_JGn_TerminalEquality
import NDO_JGd_NumericData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_TerminalArithmetic
open FIv_NativeValue (decode)
attribute [local irreducible] HMul.hMul HAdd.hAdd HPow.hPow

theorem composition : FIv_CompositionValue.polynomial (decode JFu_TerminalPrefix.challenges.theta)
    JGl_NumericData.semantic JGl_NumericData.poseidon JGn_CopyNumeric.residual=
    decode JGn_TerminalData.comp := by
  have sem : FIv_HornerAlgebra.low (decode JFu_TerminalPrefix.challenges.theta)
      JGl_NumericData.semantic.val=decode JGn_TerminalData.sem00 := by
    simpa only [List.drop_zero] using JGn_TerminalLow.sem00
  unfold FIv_CompositionValue.polynomial
  rw [JGn_TerminalPowers.twentyEight,JGn_TerminalPowers.four,sem,JGn_TerminalLow.poseidon]
  have closed : decode JGn_TerminalData.theta28 * decode JGn_CopyNumeric.residual +
      decode JGn_TerminalData.theta4 * decode JGn_TerminalData.sem00 +
        decode JGn_TerminalData.pos = decode JGn_TerminalData.comp := by
    jgl_words
  exact closed
#print axioms composition

theorem terminal : FIv_TerminalValue.formula
    (FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha)
    (decode JGn_TerminalData.comp) (decode JFu_TerminalPrefix.challenges.mu)
    (decode JGn_CopyNumeric.helper) (decode JGn_ActiveData.a64)=
    decode (FIq_Carriers.toQ JGd_NumericData.neededTerminal) := by
  rw [JGn_TerminalEquality.weight]
  jgl_words
#print axioms terminal
end AspisR1.JGn_TerminalArithmetic
end

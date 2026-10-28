import NDO_JGn_TerminalData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_TerminalEquality
open FIv_NativeValue (decode)
open FIv_NativeArray (value)
attribute [local irreducible] HMul.hMul HAdd.hAdd HPow.hPow

theorem tail5 : FIv_EqualityLoop.tail JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha 5 5=
    decode JGn_TerminalData.eq05 := by
  jgl_words
#print axioms tail5

theorem weight : FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha=
    decode JGn_TerminalData.eq00 := by
  change ((value JFu_TerminalPrefix.challenges.zc 0*value JFu_TerminalPrefix.alpha 0+(1-value JFu_TerminalPrefix.challenges.zc 0)*(1-value JFu_TerminalPrefix.alpha 0))*(((value JFu_TerminalPrefix.challenges.zc 1*value JFu_TerminalPrefix.alpha 1+(1-value JFu_TerminalPrefix.challenges.zc 1)*(1-value JFu_TerminalPrefix.alpha 1))*(((value JFu_TerminalPrefix.challenges.zc 2*value JFu_TerminalPrefix.alpha 2+(1-value JFu_TerminalPrefix.challenges.zc 2)*(1-value JFu_TerminalPrefix.alpha 2))*(((value JFu_TerminalPrefix.challenges.zc 3*value JFu_TerminalPrefix.alpha 3+(1-value JFu_TerminalPrefix.challenges.zc 3)*(1-value JFu_TerminalPrefix.alpha 3))*(((value JFu_TerminalPrefix.challenges.zc 4*value JFu_TerminalPrefix.alpha 4+(1-value JFu_TerminalPrefix.challenges.zc 4)*(1-value JFu_TerminalPrefix.alpha 4))*(FIv_EqualityLoop.tail JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha 5 5))))))))))=_
  rw [tail5]
  jgl_words
#print axioms weight
end AspisR1.JGn_TerminalEquality
end

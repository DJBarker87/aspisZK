import NDO_JGn_TerminalData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_TerminalPowers
open FIv_NativeValue (decode)
attribute [local irreducible] HMul.hMul HAdd.hAdd HPow.hPow

theorem four : decode JFu_TerminalPrefix.challenges.theta^4=decode JGn_TerminalData.theta4 := by
  jgl_words
#print axioms four

theorem twentyEight : decode JFu_TerminalPrefix.challenges.theta^28=decode JGn_TerminalData.theta28 := by
  rw [show 28=4*7 by norm_num [HMul.hMul],pow_mul,four]
  jgl_words
#print axioms twentyEight
end AspisR1.JGn_TerminalPowers
end

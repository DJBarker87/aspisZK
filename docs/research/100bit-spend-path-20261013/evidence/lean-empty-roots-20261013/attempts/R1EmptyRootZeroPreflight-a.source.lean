import R1EmptyRootZeroData

/-! Small-first check of the leading linear layer and one full round on
literal states. This file does not evaluate a multi-round recurrence. -/
set_option autoImplicit false
namespace AspisR1.EmptyRootZeroPreflight
open R0P AspisR1.EmptyRootZeroData

theorem leading : s1 = poseidonExternalLinear s0 := by decide

theorem first_round : s2 = poseidonFullRound s1 (poseidonExternalInitial 0) := by decide

#print axioms leading
#print axioms first_round
end AspisR1.EmptyRootZeroPreflight

import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_0_1 : poseidonExternalLinear s_0_0 = s_0_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_1
theorem round_0_2 : poseidonFullRound s_0_1 (poseidonExternalInitial 0) = s_0_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_2
theorem round_0_3 : poseidonFullRound s_0_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_0_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_3
theorem round_0_4 : poseidonFullRound s_0_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_0_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_4
theorem round_0_5 : poseidonFullRound s_0_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_0_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_5
theorem round_0_6 : poseidonInternalRound s_0_5 (poseidonInternalConstants 0) = s_0_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_6
end R1Z.PV_RunJoin_FixtureHashModel

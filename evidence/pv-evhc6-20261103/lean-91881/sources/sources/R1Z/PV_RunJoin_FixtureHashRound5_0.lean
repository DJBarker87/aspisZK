import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_5_1 : poseidonExternalLinear s_5_0 = s_5_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_1
theorem round_5_2 : poseidonFullRound s_5_1 (poseidonExternalInitial 0) = s_5_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_2
theorem round_5_3 : poseidonFullRound s_5_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_5_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_3
theorem round_5_4 : poseidonFullRound s_5_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_5_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_4
theorem round_5_5 : poseidonFullRound s_5_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_5_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_5
theorem round_5_6 : poseidonInternalRound s_5_5 (poseidonInternalConstants 0) = s_5_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_6
end R1Z.PV_RunJoin_FixtureHashModel

import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_4_1 : poseidonExternalLinear s_4_0 = s_4_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_1
theorem round_4_2 : poseidonFullRound s_4_1 (poseidonExternalInitial 0) = s_4_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_2
theorem round_4_3 : poseidonFullRound s_4_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_4_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_3
theorem round_4_4 : poseidonFullRound s_4_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_4_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_4
theorem round_4_5 : poseidonFullRound s_4_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_4_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_5
theorem round_4_6 : poseidonInternalRound s_4_5 (poseidonInternalConstants 0) = s_4_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_6
end R1Z.PV_RunJoin_FixtureHashModel

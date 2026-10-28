import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_1_7 : poseidonInternalRound s_1_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_1_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_7
theorem round_1_8 : poseidonInternalRound s_1_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_1_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_8
theorem round_1_9 : poseidonInternalRound s_1_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_1_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_9
theorem round_1_10 : poseidonInternalRound s_1_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_1_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_10
theorem round_1_11 : poseidonInternalRound s_1_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_1_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_11
theorem round_1_12 : poseidonInternalRound s_1_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_1_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_12
end R1Z.PV_RunJoin_FixtureHashModel

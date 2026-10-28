import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_1_13 : poseidonInternalRound s_1_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_1_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_13
theorem round_1_14 : poseidonInternalRound s_1_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_1_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_14
theorem round_1_15 : poseidonInternalRound s_1_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_1_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_15
theorem round_1_16 : poseidonInternalRound s_1_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_1_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_16
theorem round_1_17 : poseidonInternalRound s_1_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_1_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_17
theorem round_1_18 : poseidonInternalRound s_1_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_1_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_18
end R1Z.PV_RunJoin_FixtureHashModel

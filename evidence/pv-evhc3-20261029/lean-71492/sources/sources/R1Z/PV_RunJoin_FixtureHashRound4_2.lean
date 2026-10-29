import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_4_13 : poseidonInternalRound s_4_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_4_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_13
theorem round_4_14 : poseidonInternalRound s_4_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_4_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_14
theorem round_4_15 : poseidonInternalRound s_4_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_4_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_15
theorem round_4_16 : poseidonInternalRound s_4_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_4_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_16
theorem round_4_17 : poseidonInternalRound s_4_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_4_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_17
theorem round_4_18 : poseidonInternalRound s_4_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_4_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_18
end R1Z.PV_RunJoin_FixtureHashModel

import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_0_13 : poseidonInternalRound s_0_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_0_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_13
theorem round_0_14 : poseidonInternalRound s_0_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_0_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_14
theorem round_0_15 : poseidonInternalRound s_0_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_0_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_15
theorem round_0_16 : poseidonInternalRound s_0_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_0_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_16
theorem round_0_17 : poseidonInternalRound s_0_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_0_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_17
theorem round_0_18 : poseidonInternalRound s_0_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_0_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_18
end R1Z.PV_RunJoin_FixtureHashModel

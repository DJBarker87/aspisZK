import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_5_7 : poseidonInternalRound s_5_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_5_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_7
theorem round_5_8 : poseidonInternalRound s_5_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_5_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_8
theorem round_5_9 : poseidonInternalRound s_5_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_5_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_9
theorem round_5_10 : poseidonInternalRound s_5_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_5_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_10
theorem round_5_11 : poseidonInternalRound s_5_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_5_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_11
theorem round_5_12 : poseidonInternalRound s_5_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_5_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_12
end R1Z.PV_RunJoin_FixtureHashModel

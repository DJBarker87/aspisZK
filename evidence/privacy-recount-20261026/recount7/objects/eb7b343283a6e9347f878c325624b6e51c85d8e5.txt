import R1Z.PV_RunJoin_FixtureHashData

/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem round_4_19 : poseidonInternalRound s_4_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_4_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_19
theorem round_4_20 : poseidonFullRound s_4_19 (poseidonExternalFinal 0) = s_4_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_20
theorem round_4_21 : poseidonFullRound s_4_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_4_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_21
theorem round_4_22 : poseidonFullRound s_4_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_4_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_22
theorem round_4_23 : poseidonFullRound s_4_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_4_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_23
end R1Z.PV_RunJoin_FixtureHashModel

import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_36_1 : poseidonExternalLinear s_36_0 = s_36_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_1
theorem round_36_2 : poseidonFullRound s_36_1 (poseidonExternalInitial 0) = s_36_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_2
theorem round_36_3 : poseidonFullRound s_36_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_36_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_3
theorem round_36_4 : poseidonFullRound s_36_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_36_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_4
theorem round_36_5 : poseidonFullRound s_36_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_36_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_5
theorem round_36_6 : poseidonInternalRound s_36_5 (poseidonInternalConstants 0) = s_36_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_6
theorem round_36_7 : poseidonInternalRound s_36_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_36_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_7
theorem round_36_8 : poseidonInternalRound s_36_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_36_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_8
theorem round_36_9 : poseidonInternalRound s_36_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_36_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_9
theorem round_36_10 : poseidonInternalRound s_36_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_36_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_10
theorem round_36_11 : poseidonInternalRound s_36_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_36_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_11
theorem round_36_12 : poseidonInternalRound s_36_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_36_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_12
theorem round_36_13 : poseidonInternalRound s_36_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_36_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_13
theorem round_36_14 : poseidonInternalRound s_36_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_36_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_14
theorem round_36_15 : poseidonInternalRound s_36_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_36_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_15
theorem round_36_16 : poseidonInternalRound s_36_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_36_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_16
theorem round_36_17 : poseidonInternalRound s_36_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_36_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_17
theorem round_36_18 : poseidonInternalRound s_36_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_36_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_18
theorem round_36_19 : poseidonInternalRound s_36_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_36_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_19
theorem round_36_20 : poseidonFullRound s_36_19 (poseidonExternalFinal 0) = s_36_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_20
theorem round_36_21 : poseidonFullRound s_36_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_36_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_21
theorem round_36_22 : poseidonFullRound s_36_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_36_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_22
theorem round_36_23 : poseidonFullRound s_36_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_36_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_36_23
theorem permutation_36 : poseidonPermutation s_36_0 = s_36_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_36_1,round_36_2,round_36_3,round_36_4,round_36_5,round_36_6,round_36_7,round_36_8,round_36_9,round_36_10,round_36_11,round_36_12,round_36_13,round_36_14,round_36_15,round_36_16,round_36_17,round_36_18,round_36_19,round_36_20,round_36_21,round_36_22,round_36_23]
#print axioms permutation_36
theorem round_37_1 : poseidonExternalLinear s_37_0 = s_37_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_1
theorem round_37_2 : poseidonFullRound s_37_1 (poseidonExternalInitial 0) = s_37_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_2
theorem round_37_3 : poseidonFullRound s_37_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_37_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_3
theorem round_37_4 : poseidonFullRound s_37_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_37_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_4
theorem round_37_5 : poseidonFullRound s_37_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_37_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_5
theorem round_37_6 : poseidonInternalRound s_37_5 (poseidonInternalConstants 0) = s_37_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_6
theorem round_37_7 : poseidonInternalRound s_37_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_37_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_7
theorem round_37_8 : poseidonInternalRound s_37_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_37_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_8
theorem round_37_9 : poseidonInternalRound s_37_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_37_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_9
theorem round_37_10 : poseidonInternalRound s_37_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_37_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_10
theorem round_37_11 : poseidonInternalRound s_37_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_37_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_11
theorem round_37_12 : poseidonInternalRound s_37_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_37_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_12
theorem round_37_13 : poseidonInternalRound s_37_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_37_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_13
theorem round_37_14 : poseidonInternalRound s_37_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_37_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_14
theorem round_37_15 : poseidonInternalRound s_37_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_37_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_15
theorem round_37_16 : poseidonInternalRound s_37_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_37_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_16
theorem round_37_17 : poseidonInternalRound s_37_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_37_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_17
theorem round_37_18 : poseidonInternalRound s_37_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_37_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_18
theorem round_37_19 : poseidonInternalRound s_37_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_37_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_19
theorem round_37_20 : poseidonFullRound s_37_19 (poseidonExternalFinal 0) = s_37_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_20
theorem round_37_21 : poseidonFullRound s_37_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_37_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_21
theorem round_37_22 : poseidonFullRound s_37_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_37_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_22
theorem round_37_23 : poseidonFullRound s_37_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_37_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_37_23
theorem permutation_37 : poseidonPermutation s_37_0 = s_37_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_37_1,round_37_2,round_37_3,round_37_4,round_37_5,round_37_6,round_37_7,round_37_8,round_37_9,round_37_10,round_37_11,round_37_12,round_37_13,round_37_14,round_37_15,round_37_16,round_37_17,round_37_18,round_37_19,round_37_20,round_37_21,round_37_22,round_37_23]
#print axioms permutation_37
theorem round_38_1 : poseidonExternalLinear s_38_0 = s_38_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_1
theorem round_38_2 : poseidonFullRound s_38_1 (poseidonExternalInitial 0) = s_38_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_2
theorem round_38_3 : poseidonFullRound s_38_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_38_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_3
theorem round_38_4 : poseidonFullRound s_38_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_38_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_4
theorem round_38_5 : poseidonFullRound s_38_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_38_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_5
theorem round_38_6 : poseidonInternalRound s_38_5 (poseidonInternalConstants 0) = s_38_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_6
theorem round_38_7 : poseidonInternalRound s_38_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_38_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_7
theorem round_38_8 : poseidonInternalRound s_38_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_38_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_8
theorem round_38_9 : poseidonInternalRound s_38_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_38_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_9
theorem round_38_10 : poseidonInternalRound s_38_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_38_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_10
theorem round_38_11 : poseidonInternalRound s_38_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_38_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_11
theorem round_38_12 : poseidonInternalRound s_38_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_38_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_12
theorem round_38_13 : poseidonInternalRound s_38_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_38_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_13
theorem round_38_14 : poseidonInternalRound s_38_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_38_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_14
theorem round_38_15 : poseidonInternalRound s_38_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_38_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_15
theorem round_38_16 : poseidonInternalRound s_38_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_38_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_16
theorem round_38_17 : poseidonInternalRound s_38_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_38_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_17
theorem round_38_18 : poseidonInternalRound s_38_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_38_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_18
theorem round_38_19 : poseidonInternalRound s_38_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_38_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_19
theorem round_38_20 : poseidonFullRound s_38_19 (poseidonExternalFinal 0) = s_38_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_20
theorem round_38_21 : poseidonFullRound s_38_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_38_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_21
theorem round_38_22 : poseidonFullRound s_38_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_38_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_22
theorem round_38_23 : poseidonFullRound s_38_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_38_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_38_23
theorem permutation_38 : poseidonPermutation s_38_0 = s_38_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_38_1,round_38_2,round_38_3,round_38_4,round_38_5,round_38_6,round_38_7,round_38_8,round_38_9,round_38_10,round_38_11,round_38_12,round_38_13,round_38_14,round_38_15,round_38_16,round_38_17,round_38_18,round_38_19,round_38_20,round_38_21,round_38_22,round_38_23]
#print axioms permutation_38
end R1Z.PV_RunJoin_OutputModel16

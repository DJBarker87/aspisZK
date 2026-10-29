import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_30_1 : poseidonExternalLinear s_30_0 = s_30_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_1
theorem round_30_2 : poseidonFullRound s_30_1 (poseidonExternalInitial 0) = s_30_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_2
theorem round_30_3 : poseidonFullRound s_30_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_30_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_3
theorem round_30_4 : poseidonFullRound s_30_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_30_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_4
theorem round_30_5 : poseidonFullRound s_30_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_30_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_5
theorem round_30_6 : poseidonInternalRound s_30_5 (poseidonInternalConstants 0) = s_30_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_6
theorem round_30_7 : poseidonInternalRound s_30_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_30_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_7
theorem round_30_8 : poseidonInternalRound s_30_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_30_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_8
theorem round_30_9 : poseidonInternalRound s_30_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_30_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_9
theorem round_30_10 : poseidonInternalRound s_30_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_30_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_10
theorem round_30_11 : poseidonInternalRound s_30_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_30_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_11
theorem round_30_12 : poseidonInternalRound s_30_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_30_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_12
theorem round_30_13 : poseidonInternalRound s_30_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_30_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_13
theorem round_30_14 : poseidonInternalRound s_30_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_30_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_14
theorem round_30_15 : poseidonInternalRound s_30_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_30_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_15
theorem round_30_16 : poseidonInternalRound s_30_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_30_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_16
theorem round_30_17 : poseidonInternalRound s_30_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_30_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_17
theorem round_30_18 : poseidonInternalRound s_30_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_30_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_18
theorem round_30_19 : poseidonInternalRound s_30_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_30_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_19
theorem round_30_20 : poseidonFullRound s_30_19 (poseidonExternalFinal 0) = s_30_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_20
theorem round_30_21 : poseidonFullRound s_30_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_30_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_21
theorem round_30_22 : poseidonFullRound s_30_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_30_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_22
theorem round_30_23 : poseidonFullRound s_30_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_30_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_30_23
theorem permutation_30 : poseidonPermutation s_30_0 = s_30_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_30_1,round_30_2,round_30_3,round_30_4,round_30_5,round_30_6,round_30_7,round_30_8,round_30_9,round_30_10,round_30_11,round_30_12,round_30_13,round_30_14,round_30_15,round_30_16,round_30_17,round_30_18,round_30_19,round_30_20,round_30_21,round_30_22,round_30_23]
#print axioms permutation_30
theorem round_31_1 : poseidonExternalLinear s_31_0 = s_31_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_1
theorem round_31_2 : poseidonFullRound s_31_1 (poseidonExternalInitial 0) = s_31_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_2
theorem round_31_3 : poseidonFullRound s_31_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_31_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_3
theorem round_31_4 : poseidonFullRound s_31_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_31_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_4
theorem round_31_5 : poseidonFullRound s_31_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_31_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_5
theorem round_31_6 : poseidonInternalRound s_31_5 (poseidonInternalConstants 0) = s_31_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_6
theorem round_31_7 : poseidonInternalRound s_31_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_31_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_7
theorem round_31_8 : poseidonInternalRound s_31_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_31_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_8
theorem round_31_9 : poseidonInternalRound s_31_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_31_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_9
theorem round_31_10 : poseidonInternalRound s_31_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_31_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_10
theorem round_31_11 : poseidonInternalRound s_31_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_31_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_11
theorem round_31_12 : poseidonInternalRound s_31_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_31_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_12
theorem round_31_13 : poseidonInternalRound s_31_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_31_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_13
theorem round_31_14 : poseidonInternalRound s_31_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_31_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_14
theorem round_31_15 : poseidonInternalRound s_31_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_31_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_15
theorem round_31_16 : poseidonInternalRound s_31_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_31_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_16
theorem round_31_17 : poseidonInternalRound s_31_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_31_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_17
theorem round_31_18 : poseidonInternalRound s_31_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_31_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_18
theorem round_31_19 : poseidonInternalRound s_31_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_31_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_19
theorem round_31_20 : poseidonFullRound s_31_19 (poseidonExternalFinal 0) = s_31_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_20
theorem round_31_21 : poseidonFullRound s_31_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_31_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_21
theorem round_31_22 : poseidonFullRound s_31_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_31_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_22
theorem round_31_23 : poseidonFullRound s_31_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_31_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_31_23
theorem permutation_31 : poseidonPermutation s_31_0 = s_31_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_31_1,round_31_2,round_31_3,round_31_4,round_31_5,round_31_6,round_31_7,round_31_8,round_31_9,round_31_10,round_31_11,round_31_12,round_31_13,round_31_14,round_31_15,round_31_16,round_31_17,round_31_18,round_31_19,round_31_20,round_31_21,round_31_22,round_31_23]
#print axioms permutation_31
theorem round_32_1 : poseidonExternalLinear s_32_0 = s_32_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_1
theorem round_32_2 : poseidonFullRound s_32_1 (poseidonExternalInitial 0) = s_32_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_2
theorem round_32_3 : poseidonFullRound s_32_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_32_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_3
theorem round_32_4 : poseidonFullRound s_32_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_32_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_4
theorem round_32_5 : poseidonFullRound s_32_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_32_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_5
theorem round_32_6 : poseidonInternalRound s_32_5 (poseidonInternalConstants 0) = s_32_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_6
theorem round_32_7 : poseidonInternalRound s_32_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_32_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_7
theorem round_32_8 : poseidonInternalRound s_32_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_32_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_8
theorem round_32_9 : poseidonInternalRound s_32_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_32_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_9
theorem round_32_10 : poseidonInternalRound s_32_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_32_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_10
theorem round_32_11 : poseidonInternalRound s_32_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_32_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_11
theorem round_32_12 : poseidonInternalRound s_32_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_32_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_12
theorem round_32_13 : poseidonInternalRound s_32_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_32_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_13
theorem round_32_14 : poseidonInternalRound s_32_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_32_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_14
theorem round_32_15 : poseidonInternalRound s_32_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_32_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_15
theorem round_32_16 : poseidonInternalRound s_32_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_32_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_16
theorem round_32_17 : poseidonInternalRound s_32_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_32_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_17
theorem round_32_18 : poseidonInternalRound s_32_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_32_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_18
theorem round_32_19 : poseidonInternalRound s_32_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_32_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_19
theorem round_32_20 : poseidonFullRound s_32_19 (poseidonExternalFinal 0) = s_32_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_20
theorem round_32_21 : poseidonFullRound s_32_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_32_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_21
theorem round_32_22 : poseidonFullRound s_32_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_32_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_22
theorem round_32_23 : poseidonFullRound s_32_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_32_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_32_23
theorem permutation_32 : poseidonPermutation s_32_0 = s_32_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_32_1,round_32_2,round_32_3,round_32_4,round_32_5,round_32_6,round_32_7,round_32_8,round_32_9,round_32_10,round_32_11,round_32_12,round_32_13,round_32_14,round_32_15,round_32_16,round_32_17,round_32_18,round_32_19,round_32_20,round_32_21,round_32_22,round_32_23]
#print axioms permutation_32
end R1Z.PV_RunJoin_OutputModel16

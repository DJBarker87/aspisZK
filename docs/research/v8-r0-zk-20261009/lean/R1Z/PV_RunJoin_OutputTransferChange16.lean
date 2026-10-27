import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_33_1 : poseidonExternalLinear s_33_0 = s_33_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_1
theorem round_33_2 : poseidonFullRound s_33_1 (poseidonExternalInitial 0) = s_33_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_2
theorem round_33_3 : poseidonFullRound s_33_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_33_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_3
theorem round_33_4 : poseidonFullRound s_33_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_33_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_4
theorem round_33_5 : poseidonFullRound s_33_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_33_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_5
theorem round_33_6 : poseidonInternalRound s_33_5 (poseidonInternalConstants 0) = s_33_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_6
theorem round_33_7 : poseidonInternalRound s_33_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_33_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_7
theorem round_33_8 : poseidonInternalRound s_33_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_33_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_8
theorem round_33_9 : poseidonInternalRound s_33_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_33_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_9
theorem round_33_10 : poseidonInternalRound s_33_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_33_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_10
theorem round_33_11 : poseidonInternalRound s_33_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_33_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_11
theorem round_33_12 : poseidonInternalRound s_33_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_33_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_12
theorem round_33_13 : poseidonInternalRound s_33_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_33_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_13
theorem round_33_14 : poseidonInternalRound s_33_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_33_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_14
theorem round_33_15 : poseidonInternalRound s_33_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_33_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_15
theorem round_33_16 : poseidonInternalRound s_33_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_33_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_16
theorem round_33_17 : poseidonInternalRound s_33_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_33_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_17
theorem round_33_18 : poseidonInternalRound s_33_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_33_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_18
theorem round_33_19 : poseidonInternalRound s_33_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_33_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_19
theorem round_33_20 : poseidonFullRound s_33_19 (poseidonExternalFinal 0) = s_33_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_20
theorem round_33_21 : poseidonFullRound s_33_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_33_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_21
theorem round_33_22 : poseidonFullRound s_33_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_33_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_22
theorem round_33_23 : poseidonFullRound s_33_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_33_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_33_23
theorem permutation_33 : poseidonPermutation s_33_0 = s_33_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_33_1,round_33_2,round_33_3,round_33_4,round_33_5,round_33_6,round_33_7,round_33_8,round_33_9,round_33_10,round_33_11,round_33_12,round_33_13,round_33_14,round_33_15,round_33_16,round_33_17,round_33_18,round_33_19,round_33_20,round_33_21,round_33_22,round_33_23]
#print axioms permutation_33
theorem round_34_1 : poseidonExternalLinear s_34_0 = s_34_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_1
theorem round_34_2 : poseidonFullRound s_34_1 (poseidonExternalInitial 0) = s_34_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_2
theorem round_34_3 : poseidonFullRound s_34_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_34_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_3
theorem round_34_4 : poseidonFullRound s_34_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_34_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_4
theorem round_34_5 : poseidonFullRound s_34_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_34_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_5
theorem round_34_6 : poseidonInternalRound s_34_5 (poseidonInternalConstants 0) = s_34_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_6
theorem round_34_7 : poseidonInternalRound s_34_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_34_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_7
theorem round_34_8 : poseidonInternalRound s_34_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_34_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_8
theorem round_34_9 : poseidonInternalRound s_34_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_34_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_9
theorem round_34_10 : poseidonInternalRound s_34_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_34_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_10
theorem round_34_11 : poseidonInternalRound s_34_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_34_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_11
theorem round_34_12 : poseidonInternalRound s_34_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_34_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_12
theorem round_34_13 : poseidonInternalRound s_34_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_34_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_13
theorem round_34_14 : poseidonInternalRound s_34_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_34_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_14
theorem round_34_15 : poseidonInternalRound s_34_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_34_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_15
theorem round_34_16 : poseidonInternalRound s_34_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_34_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_16
theorem round_34_17 : poseidonInternalRound s_34_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_34_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_17
theorem round_34_18 : poseidonInternalRound s_34_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_34_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_18
theorem round_34_19 : poseidonInternalRound s_34_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_34_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_19
theorem round_34_20 : poseidonFullRound s_34_19 (poseidonExternalFinal 0) = s_34_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_20
theorem round_34_21 : poseidonFullRound s_34_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_34_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_21
theorem round_34_22 : poseidonFullRound s_34_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_34_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_22
theorem round_34_23 : poseidonFullRound s_34_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_34_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_34_23
theorem permutation_34 : poseidonPermutation s_34_0 = s_34_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_34_1,round_34_2,round_34_3,round_34_4,round_34_5,round_34_6,round_34_7,round_34_8,round_34_9,round_34_10,round_34_11,round_34_12,round_34_13,round_34_14,round_34_15,round_34_16,round_34_17,round_34_18,round_34_19,round_34_20,round_34_21,round_34_22,round_34_23]
#print axioms permutation_34
theorem round_35_1 : poseidonExternalLinear s_35_0 = s_35_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_1
theorem round_35_2 : poseidonFullRound s_35_1 (poseidonExternalInitial 0) = s_35_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_2
theorem round_35_3 : poseidonFullRound s_35_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_35_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_3
theorem round_35_4 : poseidonFullRound s_35_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_35_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_4
theorem round_35_5 : poseidonFullRound s_35_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_35_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_5
theorem round_35_6 : poseidonInternalRound s_35_5 (poseidonInternalConstants 0) = s_35_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_6
theorem round_35_7 : poseidonInternalRound s_35_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_35_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_7
theorem round_35_8 : poseidonInternalRound s_35_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_35_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_8
theorem round_35_9 : poseidonInternalRound s_35_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_35_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_9
theorem round_35_10 : poseidonInternalRound s_35_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_35_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_10
theorem round_35_11 : poseidonInternalRound s_35_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_35_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_11
theorem round_35_12 : poseidonInternalRound s_35_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_35_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_12
theorem round_35_13 : poseidonInternalRound s_35_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_35_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_13
theorem round_35_14 : poseidonInternalRound s_35_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_35_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_14
theorem round_35_15 : poseidonInternalRound s_35_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_35_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_15
theorem round_35_16 : poseidonInternalRound s_35_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_35_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_16
theorem round_35_17 : poseidonInternalRound s_35_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_35_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_17
theorem round_35_18 : poseidonInternalRound s_35_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_35_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_18
theorem round_35_19 : poseidonInternalRound s_35_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_35_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_19
theorem round_35_20 : poseidonFullRound s_35_19 (poseidonExternalFinal 0) = s_35_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_20
theorem round_35_21 : poseidonFullRound s_35_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_35_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_21
theorem round_35_22 : poseidonFullRound s_35_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_35_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_22
theorem round_35_23 : poseidonFullRound s_35_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_35_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_35_23
theorem permutation_35 : poseidonPermutation s_35_0 = s_35_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_35_1,round_35_2,round_35_3,round_35_4,round_35_5,round_35_6,round_35_7,round_35_8,round_35_9,round_35_10,round_35_11,round_35_12,round_35_13,round_35_14,round_35_15,round_35_16,round_35_17,round_35_18,round_35_19,round_35_20,round_35_21,round_35_22,round_35_23]
#print axioms permutation_35
end R1Z.PV_RunJoin_OutputModel16

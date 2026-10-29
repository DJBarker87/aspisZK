import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_27_1 : poseidonExternalLinear s_27_0 = s_27_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_1
theorem round_27_2 : poseidonFullRound s_27_1 (poseidonExternalInitial 0) = s_27_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_2
theorem round_27_3 : poseidonFullRound s_27_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_27_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_3
theorem round_27_4 : poseidonFullRound s_27_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_27_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_4
theorem round_27_5 : poseidonFullRound s_27_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_27_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_5
theorem round_27_6 : poseidonInternalRound s_27_5 (poseidonInternalConstants 0) = s_27_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_6
theorem round_27_7 : poseidonInternalRound s_27_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_27_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_7
theorem round_27_8 : poseidonInternalRound s_27_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_27_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_8
theorem round_27_9 : poseidonInternalRound s_27_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_27_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_9
theorem round_27_10 : poseidonInternalRound s_27_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_27_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_10
theorem round_27_11 : poseidonInternalRound s_27_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_27_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_11
theorem round_27_12 : poseidonInternalRound s_27_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_27_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_12
theorem round_27_13 : poseidonInternalRound s_27_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_27_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_13
theorem round_27_14 : poseidonInternalRound s_27_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_27_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_14
theorem round_27_15 : poseidonInternalRound s_27_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_27_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_15
theorem round_27_16 : poseidonInternalRound s_27_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_27_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_16
theorem round_27_17 : poseidonInternalRound s_27_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_27_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_17
theorem round_27_18 : poseidonInternalRound s_27_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_27_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_18
theorem round_27_19 : poseidonInternalRound s_27_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_27_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_19
theorem round_27_20 : poseidonFullRound s_27_19 (poseidonExternalFinal 0) = s_27_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_20
theorem round_27_21 : poseidonFullRound s_27_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_27_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_21
theorem round_27_22 : poseidonFullRound s_27_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_27_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_22
theorem round_27_23 : poseidonFullRound s_27_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_27_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_27_23
theorem permutation_27 : poseidonPermutation s_27_0 = s_27_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_27_1,round_27_2,round_27_3,round_27_4,round_27_5,round_27_6,round_27_7,round_27_8,round_27_9,round_27_10,round_27_11,round_27_12,round_27_13,round_27_14,round_27_15,round_27_16,round_27_17,round_27_18,round_27_19,round_27_20,round_27_21,round_27_22,round_27_23]
theorem node_27 : nodeCompress (![3001,3018,3035,3052,3069,3086,3103,3120] : Fin 8 → Scalar) ![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753] = ![1542818520,1882037664,1251951877,1554108809,81746851,159927545,2111428769,132405182] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![3001,3018,3035,3052,3069,3086,3103,3120] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_27_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_27]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_27
#print axioms node_27
end R1Z.PV_RunJoin_PathModel16

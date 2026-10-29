import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_26_1 : poseidonExternalLinear s_26_0 = s_26_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_1
theorem round_26_2 : poseidonFullRound s_26_1 (poseidonExternalInitial 0) = s_26_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_2
theorem round_26_3 : poseidonFullRound s_26_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_26_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_3
theorem round_26_4 : poseidonFullRound s_26_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_26_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_4
theorem round_26_5 : poseidonFullRound s_26_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_26_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_5
theorem round_26_6 : poseidonInternalRound s_26_5 (poseidonInternalConstants 0) = s_26_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_6
theorem round_26_7 : poseidonInternalRound s_26_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_26_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_7
theorem round_26_8 : poseidonInternalRound s_26_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_26_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_8
theorem round_26_9 : poseidonInternalRound s_26_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_26_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_9
theorem round_26_10 : poseidonInternalRound s_26_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_26_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_10
theorem round_26_11 : poseidonInternalRound s_26_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_26_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_11
theorem round_26_12 : poseidonInternalRound s_26_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_26_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_12
theorem round_26_13 : poseidonInternalRound s_26_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_26_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_13
theorem round_26_14 : poseidonInternalRound s_26_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_26_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_14
theorem round_26_15 : poseidonInternalRound s_26_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_26_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_15
theorem round_26_16 : poseidonInternalRound s_26_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_26_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_16
theorem round_26_17 : poseidonInternalRound s_26_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_26_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_17
theorem round_26_18 : poseidonInternalRound s_26_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_26_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_18
theorem round_26_19 : poseidonInternalRound s_26_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_26_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_19
theorem round_26_20 : poseidonFullRound s_26_19 (poseidonExternalFinal 0) = s_26_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_20
theorem round_26_21 : poseidonFullRound s_26_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_26_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_21
theorem round_26_22 : poseidonFullRound s_26_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_26_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_22
theorem round_26_23 : poseidonFullRound s_26_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_26_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_26_23
theorem permutation_26 : poseidonPermutation s_26_0 = s_26_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_26_1,round_26_2,round_26_3,round_26_4,round_26_5,round_26_6,round_26_7,round_26_8,round_26_9,round_26_10,round_26_11,round_26_12,round_26_13,round_26_14,round_26_15,round_26_16,round_26_17,round_26_18,round_26_19,round_26_20,round_26_21,round_26_22,round_26_23]
theorem node_26 : nodeCompress (![1272212618,615811090,570892109,1073257360,1217412274,1723220283,85709078,537745032] : Fin 8 → Scalar) ![2381,2398,2415,2432,2449,2466,2483,2500] = ![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1272212618,615811090,570892109,1073257360,1217412274,1723220283,85709078,537745032] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2381,2398,2415,2432,2449,2466,2483,2500] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2381,2398,2415,2432,2449,2466,2483,2500] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_26_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_26]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_26
#print axioms node_26
end R1Z.PV_RunJoin_PathModel16

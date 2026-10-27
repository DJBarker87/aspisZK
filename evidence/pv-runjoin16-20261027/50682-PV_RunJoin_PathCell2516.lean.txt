import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_25_1 : poseidonExternalLinear s_25_0 = s_25_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_1
theorem round_25_2 : poseidonFullRound s_25_1 (poseidonExternalInitial 0) = s_25_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_2
theorem round_25_3 : poseidonFullRound s_25_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_25_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_3
theorem round_25_4 : poseidonFullRound s_25_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_25_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_4
theorem round_25_5 : poseidonFullRound s_25_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_25_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_5
theorem round_25_6 : poseidonInternalRound s_25_5 (poseidonInternalConstants 0) = s_25_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_6
theorem round_25_7 : poseidonInternalRound s_25_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_25_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_7
theorem round_25_8 : poseidonInternalRound s_25_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_25_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_8
theorem round_25_9 : poseidonInternalRound s_25_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_25_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_9
theorem round_25_10 : poseidonInternalRound s_25_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_25_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_10
theorem round_25_11 : poseidonInternalRound s_25_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_25_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_11
theorem round_25_12 : poseidonInternalRound s_25_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_25_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_12
theorem round_25_13 : poseidonInternalRound s_25_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_25_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_13
theorem round_25_14 : poseidonInternalRound s_25_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_25_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_14
theorem round_25_15 : poseidonInternalRound s_25_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_25_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_15
theorem round_25_16 : poseidonInternalRound s_25_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_25_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_16
theorem round_25_17 : poseidonInternalRound s_25_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_25_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_17
theorem round_25_18 : poseidonInternalRound s_25_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_25_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_18
theorem round_25_19 : poseidonInternalRound s_25_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_25_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_19
theorem round_25_20 : poseidonFullRound s_25_19 (poseidonExternalFinal 0) = s_25_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_20
theorem round_25_21 : poseidonFullRound s_25_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_25_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_21
theorem round_25_22 : poseidonFullRound s_25_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_25_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_22
theorem round_25_23 : poseidonFullRound s_25_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_25_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_25_23
theorem permutation_25 : poseidonPermutation s_25_0 = s_25_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_25_1,round_25_2,round_25_3,round_25_4,round_25_5,round_25_6,round_25_7,round_25_8,round_25_9,round_25_10,round_25_11,round_25_12,round_25_13,round_25_14,round_25_15,round_25_16,round_25_17,round_25_18,round_25_19,round_25_20,round_25_21,round_25_22,round_25_23]
theorem node_25 : nodeCompress (![2361,2378,2395,2412,2429,2446,2463,2480] : Fin 8 → Scalar) ![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882] = ![1272212618,615811090,570892109,1073257360,1217412274,1723220283,85709078,537745032] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2361,2378,2395,2412,2429,2446,2463,2480] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_25_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_25]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_25
#print axioms node_25
end R1Z.PV_RunJoin_PathModel16

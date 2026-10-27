import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_8_1 : poseidonExternalLinear s_8_0 = s_8_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_1
theorem round_8_2 : poseidonFullRound s_8_1 (poseidonExternalInitial 0) = s_8_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_2
theorem round_8_3 : poseidonFullRound s_8_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_8_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_3
theorem round_8_4 : poseidonFullRound s_8_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_8_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_4
theorem round_8_5 : poseidonFullRound s_8_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_8_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_5
theorem round_8_6 : poseidonInternalRound s_8_5 (poseidonInternalConstants 0) = s_8_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_6
theorem round_8_7 : poseidonInternalRound s_8_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_8_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_7
theorem round_8_8 : poseidonInternalRound s_8_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_8_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_8
theorem round_8_9 : poseidonInternalRound s_8_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_8_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_9
theorem round_8_10 : poseidonInternalRound s_8_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_8_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_10
theorem round_8_11 : poseidonInternalRound s_8_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_8_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_11
theorem round_8_12 : poseidonInternalRound s_8_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_8_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_12
theorem round_8_13 : poseidonInternalRound s_8_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_8_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_13
theorem round_8_14 : poseidonInternalRound s_8_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_8_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_14
theorem round_8_15 : poseidonInternalRound s_8_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_8_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_15
theorem round_8_16 : poseidonInternalRound s_8_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_8_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_16
theorem round_8_17 : poseidonInternalRound s_8_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_8_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_17
theorem round_8_18 : poseidonInternalRound s_8_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_8_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_18
theorem round_8_19 : poseidonInternalRound s_8_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_8_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_19
theorem round_8_20 : poseidonFullRound s_8_19 (poseidonExternalFinal 0) = s_8_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_20
theorem round_8_21 : poseidonFullRound s_8_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_8_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_21
theorem round_8_22 : poseidonFullRound s_8_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_8_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_22
theorem round_8_23 : poseidonFullRound s_8_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_8_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_23
theorem permutation_8 : poseidonPermutation s_8_0 = s_8_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_8_1,round_8_2,round_8_3,round_8_4,round_8_5,round_8_6,round_8_7,round_8_8,round_8_9,round_8_10,round_8_11,round_8_12,round_8_13,round_8_14,round_8_15,round_8_16,round_8_17,round_8_18,round_8_19,round_8_20,round_8_21,round_8_22,round_8_23]
theorem node_8 : nodeCompress (![1292573235,1255372443,1043307233,1891352131,920017154,1033317521,170537605,505604950] : Fin 8 → Scalar) ![2021,2038,2055,2072,2089,2106,2123,2140] = ![1088882418,1343804471,734616548,13922508,2033036789,781570573,1154493927,1197511955] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1292573235,1255372443,1043307233,1891352131,920017154,1033317521,170537605,505604950] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2021,2038,2055,2072,2089,2106,2123,2140] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2021,2038,2055,2072,2089,2106,2123,2140] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_8_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_8]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_8
#print axioms node_8
end R1Z.PV_RunJoin_PathModel16

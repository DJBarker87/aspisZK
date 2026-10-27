import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_9_1 : poseidonExternalLinear s_9_0 = s_9_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_1
theorem round_9_2 : poseidonFullRound s_9_1 (poseidonExternalInitial 0) = s_9_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_2
theorem round_9_3 : poseidonFullRound s_9_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_9_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_3
theorem round_9_4 : poseidonFullRound s_9_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_9_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_4
theorem round_9_5 : poseidonFullRound s_9_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_9_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_5
theorem round_9_6 : poseidonInternalRound s_9_5 (poseidonInternalConstants 0) = s_9_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_6
theorem round_9_7 : poseidonInternalRound s_9_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_9_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_7
theorem round_9_8 : poseidonInternalRound s_9_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_9_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_8
theorem round_9_9 : poseidonInternalRound s_9_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_9_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_9
theorem round_9_10 : poseidonInternalRound s_9_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_9_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_10
theorem round_9_11 : poseidonInternalRound s_9_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_9_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_11
theorem round_9_12 : poseidonInternalRound s_9_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_9_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_12
theorem round_9_13 : poseidonInternalRound s_9_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_9_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_13
theorem round_9_14 : poseidonInternalRound s_9_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_9_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_14
theorem round_9_15 : poseidonInternalRound s_9_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_9_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_15
theorem round_9_16 : poseidonInternalRound s_9_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_9_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_16
theorem round_9_17 : poseidonInternalRound s_9_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_9_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_17
theorem round_9_18 : poseidonInternalRound s_9_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_9_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_18
theorem round_9_19 : poseidonInternalRound s_9_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_9_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_19
theorem round_9_20 : poseidonFullRound s_9_19 (poseidonExternalFinal 0) = s_9_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_20
theorem round_9_21 : poseidonFullRound s_9_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_9_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_21
theorem round_9_22 : poseidonFullRound s_9_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_9_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_22
theorem round_9_23 : poseidonFullRound s_9_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_9_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_23
theorem permutation_9 : poseidonPermutation s_9_0 = s_9_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_9_1,round_9_2,round_9_3,round_9_4,round_9_5,round_9_6,round_9_7,round_9_8,round_9_9,round_9_10,round_9_11,round_9_12,round_9_13,round_9_14,round_9_15,round_9_16,round_9_17,round_9_18,round_9_19,round_9_20,round_9_21,round_9_22,round_9_23]
theorem node_9 : nodeCompress (![1088882418,1343804471,734616548,13922508,2033036789,781570573,1154493927,1197511955] : Fin 8 → Scalar) ![2041,2058,2075,2092,2109,2126,2143,2160] = ![600625215,237354909,439972622,263907834,1075778621,569932161,1744169643,1373371366] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1088882418,1343804471,734616548,13922508,2033036789,781570573,1154493927,1197511955] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2041,2058,2075,2092,2109,2126,2143,2160] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2041,2058,2075,2092,2109,2126,2143,2160] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_9_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_9]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_9
#print axioms node_9
end R1Z.PV_RunJoin_PathModel16

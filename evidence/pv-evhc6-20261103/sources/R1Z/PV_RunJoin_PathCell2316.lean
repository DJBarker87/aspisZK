import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_23_1 : poseidonExternalLinear s_23_0 = s_23_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_1
theorem round_23_2 : poseidonFullRound s_23_1 (poseidonExternalInitial 0) = s_23_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_2
theorem round_23_3 : poseidonFullRound s_23_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_23_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_3
theorem round_23_4 : poseidonFullRound s_23_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_23_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_4
theorem round_23_5 : poseidonFullRound s_23_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_23_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_5
theorem round_23_6 : poseidonInternalRound s_23_5 (poseidonInternalConstants 0) = s_23_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_6
theorem round_23_7 : poseidonInternalRound s_23_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_23_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_7
theorem round_23_8 : poseidonInternalRound s_23_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_23_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_8
theorem round_23_9 : poseidonInternalRound s_23_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_23_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_9
theorem round_23_10 : poseidonInternalRound s_23_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_23_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_10
theorem round_23_11 : poseidonInternalRound s_23_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_23_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_11
theorem round_23_12 : poseidonInternalRound s_23_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_23_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_12
theorem round_23_13 : poseidonInternalRound s_23_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_23_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_13
theorem round_23_14 : poseidonInternalRound s_23_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_23_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_14
theorem round_23_15 : poseidonInternalRound s_23_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_23_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_15
theorem round_23_16 : poseidonInternalRound s_23_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_23_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_16
theorem round_23_17 : poseidonInternalRound s_23_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_23_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_17
theorem round_23_18 : poseidonInternalRound s_23_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_23_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_18
theorem round_23_19 : poseidonInternalRound s_23_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_23_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_19
theorem round_23_20 : poseidonFullRound s_23_19 (poseidonExternalFinal 0) = s_23_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_20
theorem round_23_21 : poseidonFullRound s_23_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_23_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_21
theorem round_23_22 : poseidonFullRound s_23_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_23_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_22
theorem round_23_23 : poseidonFullRound s_23_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_23_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_23_23
theorem permutation_23 : poseidonPermutation s_23_0 = s_23_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_23_1,round_23_2,round_23_3,round_23_4,round_23_5,round_23_6,round_23_7,round_23_8,round_23_9,round_23_10,round_23_11,round_23_12,round_23_13,round_23_14,round_23_15,round_23_16,round_23_17,round_23_18,round_23_19,round_23_20,round_23_21,round_23_22,round_23_23]
theorem node_23 : nodeCompress (![2321,2338,2355,2372,2389,2406,2423,2440] : Fin 8 → Scalar) ![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184] = ![2136837586,679543585,225002526,1101048270,2134488188,1020968422,1342497638,1907691591] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2321,2338,2355,2372,2389,2406,2423,2440] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_23_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_23]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_23
#print axioms node_23
end R1Z.PV_RunJoin_PathModel16

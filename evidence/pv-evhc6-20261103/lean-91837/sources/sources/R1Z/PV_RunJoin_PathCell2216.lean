import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_22_1 : poseidonExternalLinear s_22_0 = s_22_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_1
theorem round_22_2 : poseidonFullRound s_22_1 (poseidonExternalInitial 0) = s_22_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_2
theorem round_22_3 : poseidonFullRound s_22_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_22_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_3
theorem round_22_4 : poseidonFullRound s_22_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_22_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_4
theorem round_22_5 : poseidonFullRound s_22_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_22_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_5
theorem round_22_6 : poseidonInternalRound s_22_5 (poseidonInternalConstants 0) = s_22_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_6
theorem round_22_7 : poseidonInternalRound s_22_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_22_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_7
theorem round_22_8 : poseidonInternalRound s_22_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_22_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_8
theorem round_22_9 : poseidonInternalRound s_22_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_22_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_9
theorem round_22_10 : poseidonInternalRound s_22_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_22_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_10
theorem round_22_11 : poseidonInternalRound s_22_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_22_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_11
theorem round_22_12 : poseidonInternalRound s_22_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_22_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_12
theorem round_22_13 : poseidonInternalRound s_22_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_22_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_13
theorem round_22_14 : poseidonInternalRound s_22_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_22_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_14
theorem round_22_15 : poseidonInternalRound s_22_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_22_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_15
theorem round_22_16 : poseidonInternalRound s_22_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_22_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_16
theorem round_22_17 : poseidonInternalRound s_22_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_22_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_17
theorem round_22_18 : poseidonInternalRound s_22_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_22_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_18
theorem round_22_19 : poseidonInternalRound s_22_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_22_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_19
theorem round_22_20 : poseidonFullRound s_22_19 (poseidonExternalFinal 0) = s_22_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_20
theorem round_22_21 : poseidonFullRound s_22_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_22_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_21
theorem round_22_22 : poseidonFullRound s_22_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_22_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_22
theorem round_22_23 : poseidonFullRound s_22_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_22_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_22_23
theorem permutation_22 : poseidonPermutation s_22_0 = s_22_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_22_1,round_22_2,round_22_3,round_22_4,round_22_5,round_22_6,round_22_7,round_22_8,round_22_9,round_22_10,round_22_11,round_22_12,round_22_13,round_22_14,round_22_15,round_22_16,round_22_17,round_22_18,round_22_19,round_22_20,round_22_21,round_22_22,round_22_23]
theorem node_22 : nodeCompress (![516145591,463254876,1878652377,174797573,1017414220,839141147,732445005,1267400728] : Fin 8 → Scalar) ![2301,2318,2335,2352,2369,2386,2403,2420] = ![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![516145591,463254876,1878652377,174797573,1017414220,839141147,732445005,1267400728] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2301,2318,2335,2352,2369,2386,2403,2420] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2301,2318,2335,2352,2369,2386,2403,2420] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_22_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_22]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_22
#print axioms node_22
end R1Z.PV_RunJoin_PathModel16

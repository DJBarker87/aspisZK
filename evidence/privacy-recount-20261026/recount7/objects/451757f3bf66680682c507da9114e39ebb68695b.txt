import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_65_1 : poseidonExternalLinear s_65_0 = s_65_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_1
theorem round_65_2 : poseidonFullRound s_65_1 (poseidonExternalInitial 0) = s_65_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_2
theorem round_65_3 : poseidonFullRound s_65_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_65_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_3
theorem round_65_4 : poseidonFullRound s_65_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_65_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_4
theorem round_65_5 : poseidonFullRound s_65_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_65_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_5
theorem round_65_6 : poseidonInternalRound s_65_5 (poseidonInternalConstants 0) = s_65_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_6
theorem round_65_7 : poseidonInternalRound s_65_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_65_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_7
theorem round_65_8 : poseidonInternalRound s_65_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_65_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_8
theorem round_65_9 : poseidonInternalRound s_65_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_65_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_9
theorem round_65_10 : poseidonInternalRound s_65_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_65_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_10
theorem round_65_11 : poseidonInternalRound s_65_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_65_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_11
theorem round_65_12 : poseidonInternalRound s_65_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_65_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_12
theorem round_65_13 : poseidonInternalRound s_65_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_65_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_13
theorem round_65_14 : poseidonInternalRound s_65_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_65_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_14
theorem round_65_15 : poseidonInternalRound s_65_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_65_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_15
theorem round_65_16 : poseidonInternalRound s_65_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_65_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_16
theorem round_65_17 : poseidonInternalRound s_65_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_65_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_17
theorem round_65_18 : poseidonInternalRound s_65_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_65_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_18
theorem round_65_19 : poseidonInternalRound s_65_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_65_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_19
theorem round_65_20 : poseidonFullRound s_65_19 (poseidonExternalFinal 0) = s_65_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_20
theorem round_65_21 : poseidonFullRound s_65_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_65_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_21
theorem round_65_22 : poseidonFullRound s_65_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_65_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_22
theorem round_65_23 : poseidonFullRound s_65_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_65_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_65_23
theorem permutation_65 : poseidonPermutation s_65_0 = s_65_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_65_1,round_65_2,round_65_3,round_65_4,round_65_5,round_65_6,round_65_7,round_65_8,round_65_9,round_65_10,round_65_11,round_65_12,round_65_13,round_65_14,round_65_15,round_65_16,round_65_17,round_65_18,round_65_19,round_65_20,round_65_21,round_65_22,round_65_23]
#print axioms permutation_65
theorem node_65 : nodeCompress (![1134116828,504509963,1796983347,1413555044,1091344596,1299793962,1007871819,653735563] : Fin 8 → Scalar) ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] = ![779295644,1030234634,105546947,1848021183,1259417564,1402874809,1412830686,1654786357] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1134116828,504509963,1796983347,1413555044,1091344596,1299793962,1007871819,653735563] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_65_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_65]
  funext i
  fin_cases i <;> rfl
#print axioms node_65
end R1Z.PV_RunJoin_OutputModel16

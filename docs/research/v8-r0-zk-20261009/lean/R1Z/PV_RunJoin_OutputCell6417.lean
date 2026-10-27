import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_64_1 : poseidonExternalLinear s_64_0 = s_64_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_1
theorem round_64_2 : poseidonFullRound s_64_1 (poseidonExternalInitial 0) = s_64_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_2
theorem round_64_3 : poseidonFullRound s_64_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_64_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_3
theorem round_64_4 : poseidonFullRound s_64_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_64_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_4
theorem round_64_5 : poseidonFullRound s_64_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_64_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_5
theorem round_64_6 : poseidonInternalRound s_64_5 (poseidonInternalConstants 0) = s_64_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_6
theorem round_64_7 : poseidonInternalRound s_64_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_64_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_7
theorem round_64_8 : poseidonInternalRound s_64_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_64_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_8
theorem round_64_9 : poseidonInternalRound s_64_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_64_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_9
theorem round_64_10 : poseidonInternalRound s_64_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_64_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_10
theorem round_64_11 : poseidonInternalRound s_64_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_64_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_11
theorem round_64_12 : poseidonInternalRound s_64_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_64_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_12
theorem round_64_13 : poseidonInternalRound s_64_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_64_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_13
theorem round_64_14 : poseidonInternalRound s_64_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_64_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_14
theorem round_64_15 : poseidonInternalRound s_64_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_64_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_15
theorem round_64_16 : poseidonInternalRound s_64_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_64_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_16
theorem round_64_17 : poseidonInternalRound s_64_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_64_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_17
theorem round_64_18 : poseidonInternalRound s_64_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_64_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_18
theorem round_64_19 : poseidonInternalRound s_64_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_64_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_19
theorem round_64_20 : poseidonFullRound s_64_19 (poseidonExternalFinal 0) = s_64_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_20
theorem round_64_21 : poseidonFullRound s_64_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_64_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_21
theorem round_64_22 : poseidonFullRound s_64_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_64_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_22
theorem round_64_23 : poseidonFullRound s_64_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_64_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_64_23
theorem permutation_64 : poseidonPermutation s_64_0 = s_64_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_64_1,round_64_2,round_64_3,round_64_4,round_64_5,round_64_6,round_64_7,round_64_8,round_64_9,round_64_10,round_64_11,round_64_12,round_64_13,round_64_14,round_64_15,round_64_16,round_64_17,round_64_18,round_64_19,round_64_20,round_64_21,round_64_22,round_64_23]
#print axioms permutation_64
theorem node_64 : nodeCompress (![432585881,1344347431,436199667,1321219941,1344313237,719981873,669780265,1723074008] : Fin 8 → Scalar) ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] = ![1134116828,504509963,1796983347,1413555044,1091344596,1299793962,1007871819,653735563] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![432585881,1344347431,436199667,1321219941,1344313237,719981873,669780265,1723074008] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_64_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_64]
  funext i
  fin_cases i <;> rfl
#print axioms node_64
end R1Z.PV_RunJoin_OutputModel16
